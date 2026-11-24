"""Compare Lean's lowering with Rust's replay of the same pre-lowering circuit.

Usage: compare.py FIXTURE_DIR OUT_DIR. OUT_DIR holds replay.json, lean.json (MidnightExport.Replay),
schedule.json and rust.json (native/). Writes OUT_DIR/report.json and exits non-zero unless the
outcome is the fixture's expect.json `expect` (and its `first` difference and `static_vk`, if given).
`expect.json` may also pin `format` (midnight or halo2, both sides), and `rust_error`/`lean_error`,
substrings of each side's rejection; its `v1` object overrides the
expectation when the replay uses the V1 planner, and `origin` (midnight-zk or external, for fixtures
built from a chip's configuration; synthetic if absent) only groups run.sh's summary.
Outcomes: exact, differs, lean-rejects (Lean does not admit, Rust keys it), rust-rejects (a Rust API
errs or Rust's code panics), unrepresentable (Lean admits a stream no Rust API call spells), both-reject,
lean-rejects-unrepresentable (Lean rejects a stream no Rust API call spells, so Rust's half is the harness's judgement),
and harness-error (a harness limitation or bug; never a pass).
Differences are listed in lowering order, so the first one is where the two lowerings part."""
import hashlib, json, sys
from pathlib import Path

HEADER = [("architecture", 0, 19), ("k", 19, 20), ("public_inputs", 20, 24), ("inner_version", 24, 25), ("inner_k", 25, 26)]

def first_index(a, b):
    return next((i for i, (x, y) in enumerate(zip(a, b)) if x != y), min(len(a), len(b)))

def seq_diff(field, a, b):
    if a == b: return []
    i = first_index(a, b)
    return [{"field": field, "index": i, "lean": a[i] if i < len(a) else None, "rust": b[i] if i < len(b) else None,
             "lean_len": len(a), "rust_len": len(b)}]

def text_diff(field, a, b, context=60):
    if a == b: return []
    i = first_index(a, b)
    return [{"field": field, "offset": i, "lean": a[max(0, i - context):i + context], "rust": b[max(0, i - context):i + context]}]

def column_names(cs):
    fixed, selectors = cs["num_fixed"], len(cs["selectors"])
    return ([f"fixed column {i}" for i in range(fixed)]
            + [f"selector {j} (fixed column {fixed + j})" for j in range(selectors)]
            + [f"permutation column {j} ({kind} {index})" for j, (kind, index) in enumerate(cs["permutation"])])

def differences(replay, lean, rust):
    cs, found = replay["cs"], []
    conf = rust.get("configured")
    if conf:
        for key in ["advice_queries", "fixed_queries", "instance_queries", "permutation", "constants"]:
            found += seq_diff(f"configure.{key}", cs[key], conf[key])
    ld, rd = lean["derived"], rust.get("derived")
    if rd:
        for key in ["region_starts", "fixed", "selector_rows", "copies"]:
            found += seq_diff(f"layout.{key}", ld[key], rd[key])
    lk, rk = lean.get("key"), rust.get("key")
    if lk and rk:
        for key in ["degree", "blinding_factors", "num_fixed", "permutation_columns"]:
            if lk[key] != rk[key]: found.append({"field": f"cs.{key}", "lean": lk[key], "rust": rk[key]})
        found += text_diff("cs.pinned", lk["pinned_cs"], rk["pinned_cs"])
        if lk["format"] != rk["format"]: found.append({"field": "key.format", "lean": lk["format"], "rust": rk["format"]})
        raw_l, raw_r = bytes.fromhex(lk["raw"]), bytes.fromhex(rk["raw"])
        for name, a, b in (HEADER if lk["format"] == rk["format"] == "midnight" else []):
            if raw_l[a:b] != raw_r[a:b]:
                found.append({"field": f"header.{name}", "lean": raw_l[a:b].hex(), "rust": raw_r[a:b].hex()})
        names = column_names(cs)
        if len(lk["points"]) != len(rk["points"]):
            found.append({"field": "commitment_count", "lean": len(lk["points"]), "rust": len(rk["points"])})
        for i, (p, q) in enumerate(zip(lk["points"], rk["points"])):
            if p != q: found.append({"field": f"commitment {i}", "column": names[i] if i < len(names) else None})
        for key in ["raw", "processed", "transcript_input", "transcript_repr"]:
            if lk[key] != rk[key]: found.append({"field": f"key.{key}"})
    return found

def normalize_expect(expect, planner):
    """A V1 key is no static key; `v1` overrides the rest (`null` drops a key)."""
    if planner != "v1": return expect
    return {k: v for k, v in {**expect, "static_vk": None, **expect.get("v1", {})}.items()
            if k != "v1" and v is not None}

def main(fixture, out):
    replay, lean, rust = (json.loads((out / f).read_text()) for f in ["replay.json", "lean.json", "rust.json"])
    schedule = json.loads((out / "schedule.json").read_text())
    expect = json.loads((fixture / "expect.json").read_text())
    expect = normalize_expect(expect, replay.get("planner", "simple"))
    diffs = differences(replay, lean, rust)
    lean_ok, rust_ok, kind = lean["admitted"] and "key" in lean, rust["error"] is None, rust.get("error_kind")
    if kind == "harness": outcome = "harness-error"
    elif lean_ok and rust_ok: outcome = "exact" if not diffs and not schedule["forced"] else "differs"
    elif rust_ok: outcome = "lean-rejects"
    elif lean_ok: outcome = "unrepresentable" if kind == "unrepresentable" else "rust-rejects"
    else: outcome = "lean-rejects-unrepresentable" if kind == "unrepresentable" else "both-reject"
    first = diffs[0]["field"] if diffs else ("configure.schedule (forced)" if schedule["forced"] else None)
    digest = lambda k: hashlib.sha256(bytes.fromhex(k["raw"])).hexdigest() if k else None
    problems = []
    if outcome == "harness-error": problems.append("harness error")
    elif outcome != expect["expect"]: problems.append(f"outcome {outcome}, expected {expect['expect']}")
    if "first" in expect and not (first or "").startswith(expect["first"]):
        problems.append(f"first difference {first}, expected {expect['first']}")
    formats = [k["format"] for k in (lean.get("key"), rust.get("key")) if k]
    if "format" in expect and formats != [expect["format"]] * 2:
        problems.append(f"key formats {formats}, expected {expect['format']}")
    # Where each side rejects: a substring of Rust's error (file:line of its panic, or the error
    # variant) and of Lean's rejections.
    lean_text = "; ".join(lean["rejections"] + ([lean["key_error"]] if lean.get("key_error") else []))
    if "rust_error" in expect and expect["rust_error"] not in (rust["error"] or ""):
        problems.append(f"Rust error {(rust['error'] or '')[:120]!r}, expected {expect['rust_error']!r}")
    if "lean_error" in expect and expect["lean_error"] not in lean_text:
        problems.append(f"Lean rejections {lean_text[:120]!r}, expected {expect['lean_error']!r}")
    if "static_vk" in expect and expect["static_vk"] not in rust.get("static_vks", []):
        problems.append(f"Rust key is not {expect['static_vk']}")
    report = {"schema": "midnight-lowering-report-v1", "fixture": fixture.name, "planner": replay.get("planner", "simple"),
        "status": "FAIL" if problems else "PASS",
        "outcome": outcome, "expect": expect, "problems": problems, "first_difference": first,
        "differences": diffs, "lean_rejections": lean["rejections"], "lean_key_error": lean.get("key_error"),
        "rust_error": rust["error"], "rust_error_kind": kind, "schedule_forced": schedule["forced"],
        "lean_raw_sha256": digest(lean.get("key")), "rust_raw_sha256": digest(rust.get("key")),
        "rust_static_vks": rust.get("static_vks", []), "formats": formats,
        "counts": {"regions": len(lean["derived"]["region_starts"]), "copies": len(lean["derived"]["copies"]),
                   "fixed_cells": len(lean["derived"]["fixed"])},
        "ms": {**{f"lean_{k}": v for k, v in lean["ms"].items()}, **{f"rust_{k}": v for k, v in rust.get("ms", {}).items()}}}
    (out / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    pending = f" [pending {expect['pending']}]" if "pending" in expect else ""
    print(f"{report['status']} {fixture.name}: {outcome}{pending}" + (f" [{formats[0]}]" if formats and len(set(formats)) == 1 else "") + (f", first difference {first}" if first else "")
          + (f", lean {report['lean_raw_sha256'][:16]}" if report["lean_raw_sha256"] else "")
          + (f", rust {report['rust_raw_sha256'][:16]}" if report["rust_raw_sha256"] else "")
          + (f" = {','.join(report['rust_static_vks'])}" if report["rust_static_vks"] else ""))
    for p in problems: print("  problem:", p)
    for d in diffs[:4]: print("  differs:", json.dumps(d)[:300])
    if lean["rejections"]: print("  lean rejects:", "; ".join(lean["rejections"])[:300])
    if rust["error"]: print(f"  rust error ({kind}):", rust["error"][:300])
    return 1 if problems else 0

if __name__ == "__main__":
    sys.exit(main(Path(sys.argv[1]), Path(sys.argv[2])))
