"""Compare Lean's derived key with Rust's for one exported circuit.

Usage: compare.py OUT_DIR. OUT_DIR holds export.json and lean.json (MidnightExport),
rust.json (native/), checks.json (the driver) and optionally midnight-zk.json, project.json and
timings.json (run.sh). Writes OUT_DIR/report.json. key_status is PASS when the key format (`MidnightVK` or
halo2), the raw and processed bytes and the transcript representative agree; on a mismatch it names
the first differing field: format, `MidnightVK` header, commitment (with its column), pinned
constraint system text, or the domain part of the transcript input. status is FAIL unless the keys
agree and checks.json has all three certified checks ok, the exported planner and the contract
placement (`same`, or `not compared` for another planner); then ALTERNATE (exit 3) for another planner than the
candidate's, PASS-UNPINNED-ZK for a midnight-zk other than a clean 1e39c120 or a setup file off its pin (allowed by run.sh), else
PASS. `vk` is the circuit's fingerprint, the transcript representative in hex: unlike the raw bytes' SHA-256 it
covers the constraint system. compare.py --failed STAGE OUT_DIR writes a FAIL report for a run that stopped at STAGE."""
import hashlib, json, sys
from pathlib import Path

HEADER = [("architecture", 0, 19), ("k", 19, 20), ("public_inputs", 20, 24), ("inner_version", 24, 25), ("inner_k", 25, 26)]

def column_names(export):
    """Commitment order: fixed columns, then one per selector, then the permutation columns."""
    fixed, selectors = export["num_fixed"], len(export["selectors"])
    return ([f"fixed column {i}" for i in range(fixed)]
            + [f"selector {j} (fixed column {fixed + j})" for j in range(selectors)]
            + [f"permutation column {j} ({kind} {index})" for j, (kind, index) in enumerate(export["permutation"])])

def text_diff(a, b, context=60):
    i = next((i for i, (x, y) in enumerate(zip(a, b)) if x != y), min(len(a), len(b)))
    return {"offset": i, "lean": a[max(0, i - context):i + context], "rust": b[max(0, i - context):i + context]}

def differences(export, lean, rust):
    found = []
    if lean.get("format") != rust.get("format"):
        found.append({"field": "format", "lean": lean.get("format"), "rust": rust.get("format")})
    raw_l, raw_r = bytes.fromhex(lean["raw"]), bytes.fromhex(rust["raw"])
    for name, a, b in (HEADER if lean.get("format") == rust.get("format") == "midnight" else []):
        if raw_l[a:b] != raw_r[a:b]:
            found.append({"field": f"header.{name}", "lean": raw_l[a:b].hex(), "rust": raw_r[a:b].hex()})
    names = column_names(export)
    if len(lean["points"]) != len(rust["points"]):
        found.append({"field": "commitment_count", "lean": len(lean["points"]), "rust": len(rust["points"])})
    for i, (p, q) in enumerate(zip(lean["points"], rust["points"])):
        if p != q:
            found.append({"field": f"commitment {i}", "column": names[i] if i < len(names) else None})
    for key in ["degree", "blinding_factors", "num_fixed", "permutation_columns"]:
        if lean[key] != rust[key]:
            found.append({"field": f"cs.{key}", "lean": lean[key], "rust": rust[key]})
    if lean["pinned_cs"] != rust["pinned_cs"]:
        found.append({"field": "cs.pinned", **text_diff(lean["pinned_cs"], rust["pinned_cs"])})
    if not found and lean["transcript_input"] != rust["transcript_input"]:
        found.append({"field": "transcript_input (domain)", **text_diff(lean["transcript_input"], rust["transcript_input"])})
    if not found and (lean["processed"] != rust["processed"] or lean["transcript_repr"] != rust["transcript_repr"]):
        found.append({"field": "processed or transcript_repr"})
    return found

def optional(out, name):
    return json.loads((out / name).read_text()) if (out / name).exists() else None

CHECKS = {"usize_check", "keyed", "key_layout"}

def evidence(checks, planner):
    """Why the driver's checks.json does not back a PASS or ALTERNATE for keys under `planner`."""
    if checks.get("schema") != "midnight-vk-export-checks-v1":
        return ["checks.json missing or not midnight-vk-export-checks-v1"]
    found = list(checks.get("failed") or [])
    certified = checks.get("certified_checks") or {}
    if set(certified) != CHECKS or any(v != "ok" for v in certified.values()):
        found.append(f"certified checks not all ok: {certified}")
    own, alternate = checks.get("candidate_planner"), checks.get("experiment") == "alternate-key"
    if checks.get("experiment") not in (None, "alternate-key"):
        found.append(f"unknown experiment {checks.get('experiment')}")
    if checks.get("planner") != planner:
        found.append(f"checks.json planner {checks.get('planner')} is not the exported {planner}")
    if alternate != (own != planner):
        found.append(f"experiment {checks.get('experiment')} with candidate planner {own} and planner {planner}")
    if checks.get("contract_placement") != ("not compared" if alternate else "same"):
        found.append(f"contract placement {checks.get('contract_placement')}")
    return found

CONTRACT_PROOF = "not checked here: the challenge's trusted comparator checks it"

def context(out, build):
    """The report fields that do not depend on the keys. lean_build says how the module built; a
    kernel-checking build is not a proof verdict, so contract_proof says who checks the proof."""
    checks, zk = optional(out, "checks.json") or {}, optional(out, "midnight-zk.json")
    project = optional(out, "project.json")
    return {"lean_build": build, "contract_proof": CONTRACT_PROOF, "candidate_planner": checks.get("candidate_planner"),
            "experiment": checks.get("experiment"), "contract_placement": checks.get("contract_placement"),
            "certified_checks": checks.get("certified_checks"), "check_failures": checks.get("failed", []),
            "midnight_zk": zk, "project": project}

def failed(out, stage):
    build = (optional(out, "timings.json") or {}).get("lean_build")
    report = {"schema": "midnight-vk-export-report-v2", "status": "FAIL", "key_status": None, "failed_stage": stage,
              "planner": (optional(out, "checks.json") or {}).get("planner"), **context(out, build)}
    (out / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    print(f"FAIL {stage} (see {out}/*.log)" if stage == "elaborate" else f"FAIL {stage}")
    for m in report["check_failures"]: print("  check:", m)
    return 1

def main(out):
    export = json.loads((out / "export.json").read_text())
    lean, rust = json.loads((out / "lean.json").read_text()), json.loads((out / "rust.json").read_text())
    timings = optional(out, "timings.json") or {}
    build = timings.pop("lean_build", None)
    lk, rk = lean["key"], rust["key"]
    equal = {f: lk.get(f) == rk.get(f) for f in ["format", "raw", "processed", "transcript_repr"]}
    planner = export.get("planner", "simple")
    rust_planner = rust.get("planner", "simple")
    equal["planner"] = planner == rust_planner
    diffs = [] if all(equal.values()) else differences(export, lk, rk)
    if not equal["planner"]:
        diffs.insert(0, {"field": "planner", "lean": planner, "rust": rust_planner})
    digest = lambda key, f: hashlib.sha256(bytes.fromhex(key[f])).hexdigest()
    extra = context(out, build)
    # The setup file both sides read (Export.lean's and lib.rs's choice for k).
    srs = lean.get("srs")
    extra["setup"] = {"file": srs, **(((extra["midnight_zk"] or {}).get("setup") or {}).get(srs) or {"sha256": None, "pinned": False})}
    key_status = "PASS" if all(equal.values()) else "FAIL"
    extra["check_failures"] = evidence(optional(out, "checks.json") or {}, planner)
    zk = extra["midnight_zk"] or {}
    status = ("FAIL" if key_status == "FAIL" or extra["check_failures"] else "ALTERNATE" if extra["experiment"]
              else "PASS-UNPINNED-ZK" if not (zk.get("pinned", False) and extra["setup"]["pinned"]) else "PASS")
    report = {"schema": "midnight-vk-export-report-v2", "status": status, "key_status": key_status,
        "format": {"lean": lk.get("format"), "rust": rk.get("format")},
        "planner": planner, **extra, "k": export["k"], "equal": equal, "differences": diffs,
        "vk": {"lean": f"0x{int(lk['transcript_repr']):064x}", "rust": f"0x{int(rk['transcript_repr']):064x}"},
        "lean_raw_sha256": digest(lk, "raw"), "rust_raw_sha256": digest(rk, "raw"),
        "lean_processed_sha256": digest(lk, "processed"), "rust_processed_sha256": digest(rk, "processed"),
        "transcript_repr": {"lean": lk["transcript_repr"], "rust": rk["transcript_repr"]},
        "rust_static_vks": rust["static_vks"], "negative": {"corrupt_fixed": lean.get("corrupt_fixed"),
        "drop_copy": rust.get("drop_copy")}, "counts": {"commitments": len(lk["points"]), "fixed_cells": len(export["fixed"]),
        "copies": len(export["copies"]), "regions": len(export["region_starts"])},
        "ms": {**{f"lean_{k}": v for k, v in lean["ms"].items()}, **{f"rust_{k}": v for k, v in rust["ms"].items()}, **timings}}
    (out / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    vk = report["vk"]["lean"] if report["vk"]["lean"] == report["vk"]["rust"] else f"lean {report['vk']['lean']} rust {report['vk']['rust']}"
    print(f"{report['status']} k={export['k']} [{lk.get('format')}, {planner}, {build}] vk {vk}, raw sha256 lean {report['lean_raw_sha256'][:16]} rust {report['rust_raw_sha256'][:16]}"
          + (f" static {','.join(rust['static_vks'])}" if rust["static_vks"] else ""))
    for d in diffs[:10]: print("  differs:", json.dumps(d)[:300])
    return {"PASS": 0, "PASS-UNPINNED-ZK": 0, "ALTERNATE": 3}.get(status, 1)

if __name__ == "__main__":
    if sys.argv[1] == "--failed": sys.exit(failed(Path(sys.argv[3]), sys.argv[2]))
    sys.exit(main(Path(sys.argv[1])))
