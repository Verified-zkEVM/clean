#!/usr/bin/env python3
"""Vendor the EthLib modules Midnight imports into vendor/ethlib, with per-file SHA-256 provenance.

Usage: vendor.py ETHLIB_CHECKOUT [--check]
ETHLIB_CHECKOUT is a clone of https://github.com/ethereum/EthLib at REVISION (only read).
Copies the import closure of ROOTS and writes vendor/ethlib/provenance.json. --check instead
verifies that the vendored files, their hashes and the closure all match the checkout, and that
the vendored tree holds no other file.
"""
import hashlib, json, re, shutil, subprocess, sys
from pathlib import Path

REPOSITORY = "https://github.com/ethereum/EthLib"
REVISION = "3bd2b3c6ce78ecec9cef1471e2b957e55269729e"
ROOTS = ["EthLib.Cryptography.Hash.Blake2b"]
OUT = Path(__file__).resolve().parents[2] / "vendor/ethlib"
IMPORT = re.compile(r"^(?:public |meta )*import\s+(?:all\s+)?(EthLib\S*)", re.M)


def fail(message):
    sys.exit(f"vendor.py: {message}")


def closure(src):
    seen, todo = set(), list(ROOTS)
    while todo:
        module = todo.pop()
        if module not in seen:
            seen.add(module)
            todo += IMPORT.findall((src / (module.replace(".", "/") + ".lean")).read_text())
    return sorted(m.replace(".", "/") + ".lean" for m in seen)


def main():
    args = [a for a in sys.argv[1:] if a != "--check"]
    if len(args) != 1:
        fail(__doc__)
    src = Path(args[0])
    head = subprocess.run(["git", "-C", src, "rev-parse", "HEAD"], capture_output=True, text=True).stdout.strip()
    if head != REVISION:
        fail(f"checkout is at {head or '?'}, expected {REVISION}")
    files = closure(src) + ["LICENSE"]
    hashes = {f: hashlib.sha256((src / f).read_bytes()).hexdigest() for f in files}
    provenance = json.dumps({"repository": REPOSITORY, "revision": REVISION, "roots": ROOTS,
                             "files": hashes}, indent=2) + "\n"
    if "--check" in sys.argv:
        present = sorted(str(p.relative_to(OUT)) for p in OUT.rglob("*") if p.is_file())
        if present != sorted(files + ["provenance.json"]):
            fail("vendored file set differs from the closure")
        for f, h in hashes.items():
            if hashlib.sha256((OUT / f).read_bytes()).hexdigest() != h:
                fail(f"{f} differs from upstream")
        if (OUT / "provenance.json").read_text() != provenance:
            fail("provenance.json differs")
        print(f"vendor/ethlib matches {REVISION[:7]} ({len(files) - 1} modules)")
        return
    if OUT.exists():
        shutil.rmtree(OUT)
    for f in files:
        (OUT / f).parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(src / f, OUT / f)
    (OUT / "provenance.json").write_text(provenance)
    print(f"vendored {len(files) - 1} modules into {OUT}")


if __name__ == "__main__":
    main()
