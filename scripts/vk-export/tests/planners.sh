#!/usr/bin/env bash
# Run with VK_CONTRACT set, passing a SHA-256 baseline submission and an output directory.
set -euo pipefail
here=$(cd "$(dirname "$0")/.." && pwd)
baseline=${1:?expected a baseline submission}; out=${2:?expected an output directory}
export VK_PROJECT=${VK_PROJECT:-"$out/project"}
"$here/run.sh" "$baseline" "$out/simple"
# The baseline is a Simple candidate, so its V1 key is an alternate-key experiment: exit 3, never PASS.
rc=0; "$here/run.sh" --planner v1 "$baseline" "$out/v1" || rc=$?
[ $rc = 3 ] || { echo "V1 override exited $rc, not 3"; exit 1; }
python3 - "$out" <<'PYTEST'
import json
import sys
from pathlib import Path

# Midnight's published SHA key and the raw halo2 key from independent Rust V1 synthesis.
for planner, fmt, digest, status, experiment, placement in [
    ("simple", "midnight", "071bd29aef0bffdb7b699b467df54fcc8e76ac5644b31245368bb9e5fcf89183",
     {"PASS", "PASS-UNPINNED-ZK"}, None, "same"),
    ("v1", "halo2", "245b780ce7de64db37196f3c3a232216cb21e269f4250d8c66854a3db64f719f",
     {"ALTERNATE"}, "alternate-key", "not compared"),
]:
    report = json.loads((Path(sys.argv[1]) / planner / "report.json").read_text())
    if (report["status"] not in status or report["key_status"] != "PASS" or report["planner"] != planner
            or report["candidate_planner"] != "simple" or report["experiment"] != experiment
            or report["contract_placement"] != placement
            or any(v != "ok" for v in report["certified_checks"].values())
            or report["format"] != {"lean": fmt, "rust": fmt}
            or report["lean_raw_sha256"] != digest or report["rust_raw_sha256"] != digest):
        sys.exit(f"{planner} baseline differs from its reference key: {json.dumps(report)[:2000]}")
    print(f"{planner}: {report['status']} {fmt} {digest}")

# V1 packs SHA's regions differently from Simple, so both keys come from different absolute layouts.
simple, v1 = (json.loads((Path(sys.argv[1]) / p / "export.json").read_text()) for p in ["simple", "v1"])
if simple["region_starts"] == v1["region_starts"] or (simple["fixed"], simple["copies"]) == (v1["fixed"], v1["copies"]):
    sys.exit("V1 export has Simple's layout")
print(f"layouts differ: {sum(a != b for a, b in zip(simple['region_starts'], v1['region_starts']))} region starts")
PYTEST
