#!/usr/bin/env bash
# Lowering replay: Lean's lowering of each fixture against Rust's own lowering of the same op stream.
# Usage: run.sh OUT [FIXTURE...]   (default: every LoweringFixtures/*/Fixture.lean); OUT/summary.json.
# PLANNER=v1 lowers and replays with Rust's V1 floor planner (default simple).
# A default Simple run also replays LoweringFixtures.Compiled's programs in place of their fixtures'
# sources (OUT/compiled/NAME), which is the Rust half of the comparisons that module proves.
# Environment: REPLAY_ZK midnight-zk with the Filecoin assets (default: next to this repository). It and
# the checkout native/Cargo.toml builds against must be clean at 1e39c120, and the asset checkout's setup files must
# have their pinned SHA-256 (setup-digests.py), or the run refuses; REPLAY_ALLOW_ZK=1 runs anyway and summary.json
# records the override.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd); repo=$(cd "$here/../.." && pwd)
zk=${REPLAY_ZK:-$(cd "$repo/.." && pwd)/midnight-zk}
zk_pin=1e39c120d05200373285fba0e69766e40292b470
out=$(realpath -m "$1"); shift; mkdir -p "$out"; rm -f "$out/summary.json"  # a failed run leaves none
fixtures=("$@"); [ ${#fixtures[@]} -gt 0 ] || fixtures=($(cd "$here/LoweringFixtures" && ls -d */ | tr -d / | sort))
planner=${PLANNER:-simple}
case $planner in simple|v1) ;; *) echo "PLANNER must be simple or v1, not $planner" >&2; exit 2 ;; esac
compiled=0; [ $# -eq 0 ] && [ "$planner" = simple ] && compiled=1
cd "$repo"
# Both the asset checkout and the path dependencies (native/Cargo.toml) decide the result.
setup=$(python3 -I "$repo/scripts/setup-digests.py" "$zk/zk_stdlib/examples/assets")
# OUT/midnight-zk.json is shareable; checkout paths and changed files go to OUT/local/midnight-zk.json.
mkdir -p "$out/local"
python3 - "$out/midnight-zk.json" "$zk_pin" "$zk" "$here/native/../../../../midnight-zk" "$setup" \
    "$out/local/midnight-zk.json" <<'PY' \
  || [ "${REPLAY_ALLOW_ZK:-0}" = 1 ] || { echo "refusing; REPLAY_ALLOW_ZK=1 overrides" >&2; exit 2; }
import hashlib, json, os, subprocess, sys
path, pin = sys.argv[1], sys.argv[2]
def git(d, *args):
    r = subprocess.run(["git", "-C", d, *args], capture_output=True, text=True)
    return r.stdout if r.returncode == 0 else None
state, local = {}, {}
for role, d in [("assets", sys.argv[3]), ("dependencies", os.path.normpath(sys.argv[4]))]:
    rev, status, diff = git(d, "rev-parse", "HEAD"), git(d, "status", "--porcelain"), git(d, "diff", "HEAD", "--binary")
    changes = status.splitlines() if status is not None else None
    local[role] = {"path": os.path.abspath(d), "changes": changes}
    state[role] = {"revision": rev.strip() if rev else None, "dirty": None if changes is None else changes != [],
                   "diff_sha256": hashlib.sha256(diff.encode()).hexdigest() if diff else None}
setup = json.loads(sys.argv[5])
setup_pinned = all(s["pinned"] for s in setup.values())
clean = all(s["revision"] == pin and s["dirty"] is False for s in state.values()) and setup_pinned
with open(path, "w") as f:
    json.dump({"pinned": pin, "clean": clean, **state, "setup": setup, "setup_pinned": setup_pinned}, f, indent=2)
with open(sys.argv[6], "w") as f: json.dump(local, f, indent=2)
if not setup_pinned: print(f"midnight-zk setup files differ from their pins: {setup}", file=sys.stderr)
for role, s in state.items():
    if not (s["revision"] == pin and s["dirty"] is False):
        changes = "not a git checkout" if s["dirty"] is None else f"{len(local[role]['changes'])} changed paths"
        print(f"midnight-zk {role} {local[role]['path']}: {s['revision']}, {changes}; expected a clean {pin}", file=sys.stderr)
sys.exit(0 if clean else 1)
PY
modules=(MidnightExport.Replay LoweringFixtures.Compiled $(printf 'LoweringFixtures.%s.Fixture ' "${fixtures[@]}"))
lake build "${modules[@]}" > "$out/build.log" 2>&1 \
  || { grep -E 'error' -A6 "$out/build.log" | head -60; exit 1; }
cargo build --release -q --manifest-path "$here/native/Cargo.toml"
bin=${CARGO_TARGET_DIR:-$here/../target}/release/midnight-lowering-replay
failures=0
planner_arg=; [ "$planner" = v1 ] && planner_arg=v1
: > "$out/replays.tsv"
replay() { # KEY EXPECT_DIR LEAN_HEADER FIXTURE_EXPR: replay into OUT/KEY, judged by EXPECT_DIR/expect.json
  local dir=$out/$1; rm -rf "$dir"; mkdir -p "$dir"; printf '%s\t%s\n' "$1" "$2" >> "$out/replays.tsv"
  printf '%s\ndef main (args : List String) : IO UInt32 :=\n  Midnight.Export.Replay.main (%s) args\n' "$3" "$4" > "$dir/Driver.lean"
  if lake env lean --run "$dir/Driver.lean" "$dir" "$zk/zk_stdlib/examples/assets" ${planner_arg} > "$dir/lean.log" 2>&1 \
      && python3 "$here/schedule.py" "$dir/replay.json" "$dir/schedule.json" > "$dir/schedule.log" \
      && "$bin" "$dir/replay.json" "$dir/schedule.json" "$zk" "$dir" > "$dir/rust.log" 2>&1; then
    python3 "$here/compare.py" "$2" "$dir" || failures=$((failures + 1))
  else
    echo "FAIL $1: harness error (see $dir/*.log)"; tail -5 "$dir"/*.log; failures=$((failures + 1))
  fi
}
for name in "${fixtures[@]}"; do
  replay "$name" "$here/LoweringFixtures/$name" "import LoweringFixtures.$name.Fixture" "LoweringFixtures.$name.fixture"
done
if [ $compiled = 1 ]; then
  header=$'import LoweringFixtures.Compiled\nimport LoweringFixtures.ShaBaseline.Fixture\nopen LoweringFixtures Midnight'
  echo "compiled sources:"
  replay compiled/VanillaPlonk "$here/LoweringFixtures/VanillaPlonk" "$header" \
    "{ VanillaPlonk.fixture with source := Frontend.compile Compiled.vanillaPlonk }"
  replay compiled/SelectorlessGate "$here/LoweringFixtures/SelectorlessGate" "$header" \
    "{ SelectorlessGate.fixture with source := Frontend.compile Compiled.selectorless }"
  replay compiled/ForeignMultiSelect "$here/LoweringFixtures/ForeignMultiSelect" "$header" \
    "{ ForeignMultiSelect.fixture with source := Frontend.compile Backend.Rows.ForeignMultiSelect.configure }"
  replay compiled/ScannerSubstring "$here/LoweringFixtures/ScannerSubstring" "$header" \
    "{ ScannerSubstring.fixture with source := Frontend.compile Compiled.scanner }"
  replay compiled/RowsCanary "$here/compiled/RowsCanary" "$header" \
    "{ ShaBaseline.fixture with source := Frontend.compile Compiled.rowsCanary }"
fi
python3 - "$out" "$planner" "$here" <<'PY'
import collections, json, sys
from pathlib import Path
out, planner = Path(sys.argv[1]), sys.argv[2]
sys.dont_write_bytecode = True; sys.path.insert(0, sys.argv[3]); from compare import normalize_expect
keep = ["status", "outcome", "expect", "first_difference", "problems", "lean_raw_sha256", "rust_static_vks", "formats"]
fixtures, compiled = {}, {}
for line in (out / "replays.tsv").read_text().splitlines():
    key, expect_dir = line.split("\t")
    expect = json.loads((Path(expect_dir) / "expect.json").read_text())
    expect = normalize_expect(expect, planner)
    r = out / key / "report.json"
    entry = ({k: v for k, v in json.loads(r.read_text()).items() if k in keep} if r.exists()
             else {"status": "ERROR", "expect": expect})
    entry["origin"] = expect.get("origin", "synthetic")
    (compiled if key.startswith("compiled/") else fixtures)[key.removeprefix("compiled/")] = entry
def tally(entries, field):
    t = collections.defaultdict(collections.Counter)
    for e in entries: t[field(e)][e["status"]] += 1
    return {k: dict(v) for k, v in sorted(t.items())}
fx = list(fixtures.values())
zk = json.loads((out / "midnight-zk.json").read_text())
summary = {"planner": planner, "midnight_zk": {**zk, "override": not zk["clean"]},
           "by_expected_outcome": tally(fx, lambda e: e["expect"]["expect"]),
           "by_origin": tally(fx, lambda e: e["origin"]),
           "fixtures": fixtures, "compiled": compiled}
(out / "summary.json.tmp").write_text(json.dumps(summary, indent=2) + "\n")
(out / "summary.json.tmp").replace(out / "summary.json")
line = lambda t: ", ".join(f"{k} {sum(v.values())} ({v.get('PASS', 0)} pass)" for k, v in t.items())
# lean-rejects-unrepresentable: Lean rejects a stream no Rust API spells, so Rust's half is the harness's.
print(f"expected outcomes: {line(summary['by_expected_outcome'])}")
print(f"origins: {line(summary['by_origin'])}")
if compiled: print(f"compiled sources: {len(compiled)} ({sum(e['status'] == 'PASS' for e in compiled.values())} pass)")
if not zk["clean"]: print(f"midnight-zk override: not a clean {zk['pinned']} (see summary.json)")
PY
echo "replay ($planner): ${#fixtures[@]} fixtures$([ $compiled = 1 ] && echo ' + 5 compiled'), $failures failing"
exit $(( failures > 0 ))
