#!/usr/bin/env bash
# Lean-derived vs Rust-generated VK of a zk.golf SHA-256 submission's circuit.
# Usage: run.sh [--planner simple|v1] [--witgen] [--prove HEX]... SUBMISSION OUT   one submission: a directory of flat
#          .lean files with Main.lean, or a .tar.gz of one
#        run.sh [--planner simple|v1] [--witgen] [--prove HEX]... --batch DIR OUT    every directory below DIR holding a
#          Main.lean, each into OUT/submissions/ID (ID its path below DIR, `%` and `/` percent-encoded), OUT/summary.json
# The candidate's k must be at most 19: the largest setup read is bls_filecoin_2p19.
# The key is for the candidate's own floor planner, whose region starts must be the contract's (`Rust.starts`). A
# `Configured.Candidate` is read as the Rust candidate it compiles to (`Configured.Candidate.compiled`); a fixture may
# name a `Rust.Candidate` directly.
# --planner naming another planner derives that planner's key instead: an alternate-key experiment, reported as
# status ALTERNATE (exit 3), never PASS. Lean also runs certified key derivation's checks (`Usize.check`,
# `KeyChecks.keyed`) on the candidate's stream, reported in report.json's certified_checks; any failure is FAIL.
# --witgen also writes the contract's witness program, OUT/witgen.json: with export.json and the setup it is all
# native/examples/prove.rs needs to prove any message without Lean. --prove HEX (repeatable; 24 bytes as 48 lowercase
# hex digits) implies it and proves HEX with it (OUT/prove/HEX), compares its witness with Lean's evaluation, and
# checks that a tampered advice cell or another digest fails (the copy tamper is skipped without an advice-instance
# copy). Only a verifier rejection passes a check; a prover failure or a skip leaves it unexercised and the message
# PARTIAL. The key comparison stays the top-level status; the proofs are in report.json's prove.
# Environment: VK_CONTRACT the challenge repository's Challenge/ directory (required); VK_ZK midnight-zk at
# 1e39c120 with the Filecoin assets (default: next to this repository); VK_PROJECT the scratch Lean project, reused
# so the contract builds once (default OUT/project), and only for the contract sources, backend revision, toolchain
# and mode it was created with (its vk-project.json, report.json's project); VK_LEAN_ARGS / VK_RUST_ARGS extra exporter / keygen arguments
# (negative tests).
# Rust builds against the midnight-zk next to this repository (native/Cargo.toml's path dependencies). Its HEAD, and
# whether and how (a diff digest) the workspace Cargo.toml and proofs/, curves/, circuits/ and zk_stdlib/ changed, go
# into report.json's midnight_zk (checkout paths and changed files into OUT/local/midnight-zk.json), with the SHA-256 of the setup files in the assets checkout (setup-digests.py; report.json's setup is
# the one read); anything but a clean 1e39c120 with the pinned setups is refused, unless VK_ALLOW_DIRTY_ZK=1, which
# turns a passing status into PASS-UNPINNED-ZK.
# Submission proofs are elaborated without kernel checking (only `candidate` matters here), and replaced by `sorry`
# (stub.py) if they do not elaborate at all. VK_KERNEL=1 builds the module with kernel checking enabled and fails on
# any build error instead. That build also
# fails on a reported `sorry` or a source mentioning skipKernelTC, but it is no proof verdict: it requires no
# `checked`, nor checks its axioms or `implemented_by` code. The challenge's trusted comparator checks the contract
# proof. report.json's lean_build is kernel-checking-enabled, kernel-checking-skipped, proofs-stubbed or failed;
# key_status is the key comparison alone.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd); repo=$(cd "$here/../.." && pwd)
usage() { echo "usage: run.sh [--planner simple|v1] [--batch] [--witgen] [--prove HEX]... INPUT OUT" >&2; exit 2; }
planner=candidate; batch=0; witgen=0; messages=()
while [[ ${1:-} == --* ]]; do
  case "$1" in
    --planner)
      case "${2:-}" in simple|v1) planner=$2 ;; *) usage ;; esac
      shift 2 ;;
    --batch) batch=1; shift ;;
    --witgen) witgen=1; shift ;;
    --prove) [[ ${2:-} =~ ^[0-9a-f]{48}$ ]] || usage; messages+=("$2"); witgen=1; shift 2 ;;
    --) shift; break ;;
    *) usage ;;
  esac
done
[ "$#" -eq 2 ] || usage
zkdep=$(realpath -m "$repo/../midnight-zk")  # what native/Cargo.toml builds against
zk=${VK_ZK:-$zkdep}; contract=${VK_CONTRACT:?set VK_CONTRACT to the Challenge/ dir of the challenge repository}
input=$(realpath "$1"); out=$(realpath -m "$2"); mkdir -p "$out"
project=$(realpath -m "${VK_PROJECT:-$out/project}")
mode=kernel-checking-skipped; [ "${VK_KERNEL:-0}" = 1 ] && mode=kernel-checking-enabled
now() { date +%s%3N; }
# Everything a run writes into an output directory, removed before the run so a failure cannot leave the previous
# run's results behind. OUT itself and VK_PROJECT may be the user's and are kept.
outputs=({report,timings,witgen,checks,export,lean,rust,midnight-zk,project,summary}.json {lean,rust}.{raw,processed}.bin
  elaborate.log elaborate-stubbed.log prove submissions local)
clear_outputs() { local f; for f in "${outputs[@]}"; do rm -rf "${1:?}/$f"; done; }

check_zk() {  # OUT/midnight-zk.json: the dependency checkout's revision, changes and setup digests; paths and
  # changed files go to OUT/local/midnight-zk.json, which stays on this machine
  local setup; setup=$(python3 -I "$repo/scripts/setup-digests.py" "$zk/zk_stdlib/examples/assets")
  mkdir -p "$out/local"
  python3 - "$zkdep" "$zk" "${VK_ALLOW_DIRTY_ZK:-0}" "$out/midnight-zk.json" "$setup" "$out/local/midnight-zk.json" <<'PY'
import hashlib, json, subprocess, sys
dep, assets, allow, path, setup, local_path = sys.argv[1:]
PIN = "1e39c120d05200373285fba0e69766e40292b470"
PATHS = ["Cargo.toml", "proofs", "curves", "circuits", "zk_stdlib"]
git = lambda d, *a: subprocess.run(["git", "-C", d, *a], capture_output=True, text=True)
local = {}
def state(role, d):
    head, status = git(d, "rev-parse", "HEAD"), git(d, "status", "--porcelain", "--", *PATHS)
    diff = git(d, "diff", "HEAD", "--binary", "--", *PATHS)
    changes = status.stdout.splitlines() if status.returncode == 0 else None
    local[role] = {"path": d, "changes": changes}
    return {"head": head.stdout.strip() if head.returncode == 0 else None,
            "dirty": None if changes is None else changes != [],
            "diff_sha256": hashlib.sha256(diff.stdout.encode()).hexdigest() if diff.returncode == 0 and diff.stdout else None}
info = {**state("dependencies", dep), "pin": PIN}
info["dependencies_pinned"] = info["head"] == PIN and info["dirty"] is False
info["setup"] = json.loads(setup)
info["setup_pinned"] = all(s["pinned"] for s in info["setup"].values())
info["pinned"] = info["dependencies_pinned"] and info["setup_pinned"]
info["override"] = not info["pinned"] and allow == "1"
info["assets"] = "same checkout" if assets == dep else state("assets", assets)
json.dump(info, open(path, "w"), indent=2)
json.dump(local, open(local_path, "w"), indent=2)
if not info["pinned"]:
    what = (f"HEAD {info['head']}" if info["head"] != PIN else f"{len(local['dependencies']['changes'] or [])} changed paths"
            if not info["dependencies_pinned"] else "setup files differ from their pins")
    print(f"midnight-zk at {dep} is not a clean {PIN[:8]} with the pinned setups ({what}); "
          + ("VK_ALLOW_DIRTY_ZK=1, comparing anyway" if allow == "1" else "set VK_ALLOW_DIRTY_ZK=1 to compare anyway"),
          file=sys.stderr)
    sys.exit(0 if allow == "1" else 1)
PY
}

write_driver() {
  mkdir -p "$project"
  cat > "$project/VKExport.lean" <<'LEAN'
import Solution.MidnightSHA256Pareto.Main
import MidnightExport.Export
import MidnightExport.Witness
open Challenge.MidnightSHA256Pareto

def main (args : List String) : IO UInt32 := do
  -- A `Configured.Candidate` coerces to its compilation: `Backend.compile` of its program, synthesized at its config.
  let c : Rust.Candidate := Solution.MidnightSHA256Pareto.candidate
  let ops := Rust.operations c
  let requested :: args := args | throw (IO.userError "expected a floor planner")
  let exportArgs := args.takeWhile (· != "--witness")
  let witnessArgs := (args.dropWhile (· != "--witness")).drop 1
  let out :: _ := exportArgs | throw (IO.userError "expected an output directory")
  let own : String := match c.planner with
    | .simple => "simple"
    | .v1 => "v1"
  let used := if requested == "candidate" then own else requested
  let planner ← match used with
    | "simple" => pure Midnight.Chips.Layout.Planner.simple
    | "v1" => pure (Midnight.Export.v1 c.source)
    | _ => throw (IO.userError s!"unknown floor planner {used}")
  let alternate := used != own
  unless c.k ≤ 19 do throw (IO.userError s!"k = {c.k}: the exporter's largest setup is bls_filecoin_2p19")
  -- The candidate's key must use the placement the contract checks, deferred constants included.
  let exported := (Midnight.Export.layout c.source ops c.k planner).regionStarts
  let placement : String := if alternate then "not compared"
    else if Rust.starts c == exported then "same" else "differs"
  let checks := Midnight.Export.certifiedChecks c.source ops c.k planner
  let failed : List String :=
    (if placement == "differs" then ["contract placement differs from the exported starts"] else []) ++
      checks.filterMap (·.2)
  let outDir : System.FilePath := out
  IO.FS.writeFile (outDir / "checks.json") (Lean.Json.pretty (Lean.Json.mkObj [
    ("schema", Lean.Json.str "midnight-vk-export-checks-v1"), ("candidate_planner", Lean.Json.str own),
    ("planner", Lean.Json.str used),
    ("experiment", if alternate then Lean.Json.str "alternate-key" else Lean.Json.null),
    ("contract_placement", Lean.Json.str placement),
    ("certified_checks", Lean.Json.mkObj (checks.map fun (name, e) => (name, Lean.Json.str (e.getD "ok")))),
    ("failed", Lean.toJson failed)]))
  unless failed.isEmpty do
    for m in failed do IO.eprintln s!"lean: {m}"
    return 1
  let code ← Midnight.Export.main c.source c.k ops exportArgs (planner := planner)
  if code != 0 || witnessArgs.isEmpty then return code
  -- Under another planner than the contract's, the witness is for that planner's key only.
  let contract := if alternate then none else some (Rust.starts c)
  Midnight.Export.Witness.main c.source c.k ops planner contract witnessArgs
LEAN
}

identity() {  # identity CONTRACT_DIR: what a VK_PROJECT is built from, as canonical JSON
  python3 - "$1" "$repo" "$mode" <<'PY'
import hashlib, json, subprocess, sys
from pathlib import Path
contract, repo, mode = Path(sys.argv[1]), sys.argv[2], sys.argv[3]
h = hashlib.sha256()
for f in sorted(p for p in contract.rglob("*") if p.is_file()):
    rel = f.relative_to(contract).as_posix().encode(); data = f.read_bytes()
    h.update(len(rel).to_bytes(8, "big") + rel + len(data).to_bytes(8, "big") + data)
git = lambda *a: subprocess.run(["git", "-C", repo, *a], capture_output=True, text=True).stdout
diff = git("diff", "HEAD", "--binary")
print(json.dumps({"mode": mode, "contract_sha256": h.hexdigest(), "backend": git("rev-parse", "HEAD").strip(),
                  "backend_diff_sha256": hashlib.sha256(diff.encode()).hexdigest() if diff else None,
                  "toolchain": Path(repo, "lean-toolchain").read_text().strip()}, sort_keys=True))
PY
}

setup() {
  write_driver
  local id; id=$(identity "$contract")
  if [ -f "$project/lakefile.toml" ]; then
    # The contract copy is checked as well as the requested contract: a submission can change it.
    if [ "$(cat "$project/vk-project.json" 2>/dev/null)" != "$id" ] || [ "$(identity "$project/Challenge")" != "$id" ]; then
      echo "VK_PROJECT $project was built from another contract, backend, toolchain or mode than $id" \
        "(see its vk-project.json); use a fresh VK_PROJECT" >&2
      exit 1
    fi
    cp "$project/vk-project.json" "$out/project.json"; return
  fi
  mkdir -p "$project/.lake"
  printf '%s\n' "$id" > "$project/vk-project.json"; cp "$project/vk-project.json" "$out/project.json"
  cp "$repo/lean-toolchain" "$project/"
  cp -r "$contract" "$project/Challenge"
  ln -sfn "$repo/.lake/packages" "$project/.lake/packages"
  cat > "$project/lakefile.toml" <<TOML
name = "VKExportRun"
[[require]]
name = "Clean"
path = "$repo"
[[lean_lib]]
name = "Challenge"
[[lean_lib]]
name = "Solution"
moreLeanArgs = [$( [ "$mode" = kernel-checking-enabled ] || echo '"-Ddebug.skipKernelTC=true"' )]
[[lean_lib]]
name = "VKExport"
TOML
  python3 - "$repo" "$project" <<'PY'
import json, sys
repo, project = sys.argv[1:]
m = json.load(open(f"{repo}/lake-manifest.json"))
clean = dict(type="path", name="Clean", scope="", dir=repo, inherited=False,
             configFile="lakefile.lean", manifestFile="lake-manifest.json")
packages = [clean] + [{**p, "inherited": True} for p in m["packages"]]
json.dump({"version": m["version"], "packagesDir": ".lake/packages", "packages": packages,
           "name": "VKExportRun", "lakeDir": ".lake"}, open(f"{project}/lake-manifest.json", "w"), indent=1)
PY
  (cd "$project" && t=$(now) && lake build Challenge.MidnightSHA256Pareto.Baseline MidnightExport.Export MidnightExport.Witness >&2 \
    && echo "contract and exporter built in $(( $(now) - t )) ms" >&2)
}

one() {  # one SUBMISSION_DIR OUT
  local sub=$1 dir=$2; mkdir -p "$dir"
  [ "$dir" = "$out" ] || { clear_outputs "$dir"; cp "$out/midnight-zk.json" "$out/project.json" "$dir/"; }
  rm -rf "$project/Solution"; mkdir -p "$project/Solution/MidnightSHA256Pareto"
  cp "$sub"/*.lean "$project/Solution/MidnightSHA256Pareto/"
  local t0 t1 t2 t3 status=0 build=$mode
  failed() {  # failed STAGE: a FAIL report naming the stage (compare.py --failed)
    printf '{"lean_build": "%s"}\n' "$build" > "$dir/timings.json"
    python3 "$here/compare.py" --failed "$1" "$dir" || true
  }
  t0=$(now)
  if ! (cd "$project" && lake build VKExport > "$dir/elaborate.log" 2>&1); then
    # A kernel-checking build fails on a build error instead of falling back to stubs.
    if [ $mode = kernel-checking-enabled ]; then build=failed; failed elaborate; return 1; fi
    # Proofs written against another formalization version may not elaborate; `candidate` may still.
    python3 -I "$here/stub.py" "$project"/Solution/MidnightSHA256Pareto/*.lean; build=proofs-stubbed
    if ! (cd "$project" && lake build VKExport > "$dir/elaborate-stubbed.log" 2>&1); then
      build=failed; failed elaborate; return 1
    fi
  elif [ $mode = kernel-checking-enabled ] && { grep -q "declaration uses .sorry." "$dir/elaborate.log" \
      || grep -rqs skipKernelTC "$project/Solution"; }; then
    # Building succeeds with either, but then the kernel has not checked every proof.
    build=failed; failed elaborate; return 1
  fi
  t1=$(now)
  local witness=(); [ $witgen = 0 ] || witness=(--witness "$dir" "${messages[@]}")
  if ! (cd "$project" && lake env lean --run VKExport.lean "$planner" "$dir" "$zk/zk_stdlib/examples/assets" ${VK_LEAN_ARGS:-} "${witness[@]}"); then
    failed lean-export; return 1
  fi
  t2=$(now)
  if ! cargo run --release -q --manifest-path "$here/native/Cargo.toml" -- "$dir/export.json" "$zk" "$dir" ${VK_RUST_ARGS:-}; then
    failed rust-keygen; return 1
  fi
  t3=$(now)
  printf '{"lean_build": "%s", "elaborate": %d, "lean_total": %d, "rust_total": %d}\n' $build $((t1 - t0)) $((t2 - t1)) $((t3 - t2)) > "$dir/timings.json"
  python3 "$here/compare.py" "$dir" || status=$?  # 3: keys agree, but for an alternate planner
  [ ${#messages[@]} = 0 ] || prove "$dir" || status=1
  return $status
}

prove() {  # prove OUT: each message's proof, then its checks, each in its own process; results into OUT/report.json
  local dir=$1 hex check
  local rust=(cargo run --release -q --manifest-path "$here/native/Cargo.toml" --example prove -- "$dir")
  for hex in "${messages[@]}"; do
    local log="$dir/prove/$hex/prove.log"
    mkdir -p "$dir/prove/$hex"
    "${rust[@]}" "$hex" --zk "$zk" --lean "$dir/prove/$hex/witness.json" > "$log" 2>&1 || echo "rust exit $? on prove" >> "$log"
    grep -qs '"verified": true' "$dir/prove/$hex/prove.json" || "${rust[@]}" "$hex" --zk "$zk" --mock >> "$log" 2>&1 || true
    for check in "--wrong-digest" "--tamper first" "--tamper copy"; do
      # shellcheck disable=SC2086
      "${rust[@]}" "$hex" --zk "$zk" $check >> "$log" 2>&1 || echo "rust exit $? on $check" >> "$log"
    done
  done
  python3 - "$dir" "${messages[@]}" <<'PY'
import json, sys
from pathlib import Path
out = Path(sys.argv[1]); report = json.loads((out / "report.json").read_text())
def result(n):
    # Only a verifier rejection exercises the verifier; a prover error or panic produced no proof to reject.
    if n is None: return "missing"
    o = n["outcome"]
    return n.get("result") or ("verifier-rejected" if o == "rejected" else "accepted" if o == "accepted"
        else "skipped" if o.startswith("skipped") else "prover-failed" if o.startswith("prover") else "verifier-panicked")
ok, prove = True, {}
for hex in sys.argv[2:]:
    d = out / "prove" / hex
    load = lambda name: json.loads((d / name).read_text()) if (d / name).exists() else None
    p, w = load("prove.json") or {}, load("witness.json") or {}
    raw = {c: load(f"negative-{c}.json") for c in ["wrong-digest", "tamper-first", "tamper-copy"]}
    neg = {c: n["outcome"] if n else "no result (see prove.log)" for c, n in raw.items()}
    results = {c: result(n) for c, n in raw.items()}
    entry = {k: p.get(k) for k in ["verified", "outcome", "digest", "proof_bytes", "advice_cells", "contract_placement",
                                   "public_inputs", "ms"]}
    entry |= {"vk": p.get("vk"), "vk_equals_lean": p.get("vk") == (report.get("vk") or {}).get("lean")
                  and p.get("vk_raw_sha256") == report.get("lean_raw_sha256"),
              "lean_mismatches": (p.get("lean_mismatches") or {}).get("count"),
              "lean_witness_ms": (w.get("ms") or {}).get("witness"), "negatives": neg, "negative_results": results}
    if (mock := load("mock.json")) is not None: entry["mock"] = mock
    honest = (p.get("status") == "PASS" and entry["vk_equals_lean"] and entry["lean_mismatches"] == 0)
    if not honest or any(r in ("accepted", "missing") for r in results.values()): entry["status"] = "FAIL"
    elif all(r == "verifier-rejected" for r in results.values()): entry["status"] = "PASS"
    else: entry["status"] = "PARTIAL"  # no proof accepted, but some check never reached the verifier
    ok &= entry["status"] != "FAIL"; prove[hex] = entry
    print(f"prove {hex}: {entry['status']} (verified {p.get('verified')}, Lean mismatches {entry['lean_mismatches']}, {results})")
report["prove"] = prove
(out / "report.json").write_text(json.dumps(report, indent=2) + "\n")
sys.exit(0 if ok else 1)
PY
}

unpack() {  # unpack INPUT -> a directory holding Main.lean
  if [ -d "$1" ]; then echo "$1"; return; fi
  local d="$out/submission"; rm -rf "$d"; mkdir -p "$d"; tar -xzf "$1" -C "$d"
  dirname "$(find "$d" -name Main.lean | head -1)"
}

clear_outputs "$out"
subs=(); submissions=()
if [ $batch = 1 ]; then
  while IFS= read -r main; do
    sub=$(dirname "$main"); name=$(realpath --relative-to="$input" "$sub")
    [ "$name" != . ] || { echo "batch: $input/Main.lean is at the root; put each submission in its own directory" >&2; exit 2; }
    name=${name//"%"/%25}; subs+=("$sub"); submissions+=("${name//\//%2F}")
  done < <(find "$input" -name Main.lean | sort)
  [ ${#subs[@]} -gt 0 ] || { echo "batch: no Main.lean below $input" >&2; exit 2; }
fi
check_zk
setup
if [ $batch = 0 ]; then one "$(unpack "$input")" "$out"; exit; fi
failures=0; alternates=0
for i in "${!subs[@]}"; do
  name=${submissions[$i]}
  echo "== $name"; rc=0; one "${subs[$i]}" "$out/submissions/$name" || rc=$?
  case $rc in 0) ;; 3) alternates=$((alternates + 1)) ;; *) failures=$((failures + 1)) ;; esac
done
python3 - "$out" "${submissions[@]}" <<'PY'
import json, sys
from pathlib import Path
out = Path(sys.argv[1])
keys = ["status", "key_status", "lean_build", "contract_proof", "planner", "candidate_planner", "experiment",
        "contract_placement", "certified_checks", "failed_stage", "midnight_zk", "setup", "project", "format", "k", "vk", "lean_raw_sha256", "rust_raw_sha256", "transcript_repr", "rust_static_vks", "ms", "prove"]
summary = {}
for name in sys.argv[2:]:
    r = out / "submissions" / name / "report.json"
    summary[name] = ({k: v for k, v in json.loads(r.read_text()).items() if k in keys + ["differences"]}
                       if r.exists() else {"status": "ERROR"})
(out / "summary.json.tmp").write_text(json.dumps(summary, indent=2) + "\n")
(out / "summary.json.tmp").replace(out / "summary.json")
PY
echo "batch: $failures failing, $alternates alternate-key"
if [ $failures -gt 0 ]; then exit 1; elif [ $alternates -gt 0 ]; then exit 3; fi
