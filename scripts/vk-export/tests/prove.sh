#!/usr/bin/env bash
# Run with VK_CONTRACT set, passing a SHA-256 baseline submission and an output directory.
# The contract's witness proves and verifies against the Simple key (Midnight's published one) for four
# messages, Rust's interpretation of the witness program equals Lean's, the verifier rejects every wrong digest,
# no tampered witness yields an accepted proof, and each tamper reaches the verifier and is rejected for at least
# one message (a tamper that breaks a lookup makes the prover panic instead). Then, with only export.json and
# witgen.json and no Lean on PATH, Rust proves a fifth.
set -euo pipefail
here=$(cd "$(dirname "$0")/.." && pwd)
baseline=${1:?expected a baseline submission}; out=${2:?expected an output directory}
export VK_PROJECT=${VK_PROJECT:-"$out/project"}
random() { od -An -tx1 -N24 /dev/urandom | tr -d ' \n'; }
args=()
for m in 000000000000000000000000000000000000000000000000 6162636465666768696a6b6c6d6e6f707172737475767778 \
    ffffffffffffffffffffffffffffffffffffffffffffffff "$(random)"; do
  args+=(--prove "$m")
done
"$here/run.sh" "${args[@]}" "$baseline" "$out/simple"
python3 - "$out/simple" <<'PYTEST'
import hashlib, json, sys
from pathlib import Path
report = json.loads((Path(sys.argv[1]) / "report.json").read_text())
if (report["status"] not in ("PASS", "PASS-UNPINNED-ZK")
        or report["lean_raw_sha256"] != "071bd29aef0bffdb7b699b467df54fcc8e76ac5644b31245368bb9e5fcf89183"):
    sys.exit("baseline differs from its reference key")
rejected = {"tamper-first": 0, "tamper-copy": 0}
for hex, p in report["prove"].items():
    r = p["negative_results"]
    if (p["status"] not in ("PASS", "PARTIAL") or p["contract_placement"] != "same"
            or p["public_inputs"]["consistent"] is not True or r["wrong-digest"] != "verifier-rejected"
            or p["digest"] != hashlib.sha256(bytes.fromhex(hex)).hexdigest()):
        sys.exit(f"{hex}: {p}")
    for c in rejected: rejected[c] += r[c] == "verifier-rejected"
    print(f"{hex}: {p['status']}, proved and verified, {p['proof_bytes']} bytes, witness equals Lean's; checks {r}")
if not all(rejected.values()):
    sys.exit(f"a tamper never reached the verifier: {rejected}")
PYTEST
alone="$out/rust-only"; rm -rf "$alone"; mkdir -p "$alone"; cp "$out/simple/export.json" "$out/simple/witgen.json" "$alone/"
message=$(random); cargo=$(dirname "$(command -v cargo)")
PATH="$cargo:/usr/bin:/bin" bash -c '
  ! command -v lean && ! command -v lake && ! command -v elan || { echo "Lean is on PATH"; exit 1; }
  cargo run --release -q --manifest-path "$0/native/Cargo.toml" --example prove -- "$1" "$2"' "$here" "$alone" "$message"
python3 - "$alone/prove/$message/prove.json" <<'PYTEST'
import json, sys
p = json.loads(open(sys.argv[1]).read())
if (not p["verified"] or p["vk_raw_sha256"] != "071bd29aef0bffdb7b699b467df54fcc8e76ac5644b31245368bb9e5fcf89183"
        or p["vk"] != "0x2be57df21018a4e8e78615aff27c6f08f2c8037878ec29d71df6fb060c0f1477"):
    sys.exit(f"Rust alone: {p}")
print(f"Rust alone, {p['message']}: proved and verified in {p['ms']}")
PYTEST
