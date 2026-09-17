#!/usr/bin/env python3
"""Generate Lean Poseidon constants from a pinned circomlib source file."""

from __future__ import annotations

import argparse
import hashlib
import re
import sys
from pathlib import Path


SOURCE_COMMIT = "35e54ea21da3e8762557234298dbb553c175ea8d"
SOURCE_SHA256 = "94c9e4b5ea891ab4d1ba626f1d719f8c661014d9b628f6096c803f75f39e3eee"
N_PARTIAL = [56, 57, 56, 60, 60, 63, 64, 63, 60, 66, 60, 65, 70, 60, 64, 68]
KINDS = ("C", "M", "P", "S")


def matching_bracket(text: str, start: int) -> int:
    depth = 0
    for index in range(start, len(text)):
        if text[index] == "[":
            depth += 1
        elif text[index] == "]":
            depth -= 1
            if depth == 0:
                return index
    raise ValueError(f"unclosed array starting at byte {start}")


def parse_source(source: str) -> dict[tuple[str, int], list[str]]:
    tables: dict[tuple[str, int], list[str]] = {}
    function_matches = list(re.finditer(r"function POSEIDON_([CMPS])\(t\)\s*\{", source))
    for function_index, function_match in enumerate(function_matches):
        kind = function_match.group(1)
        function_end = (
            function_matches[function_index + 1].start()
            if function_index + 1 < len(function_matches)
            else len(source)
        )
        body = source[function_match.end() : function_end]
        for branch in re.finditer(r"(?:if|else if)\s*\(t\s*==\s*(\d+)\)\s*\{", body):
            width = int(branch.group(1))
            return_index = body.find("return", branch.end())
            array_start = body.find("[", return_index)
            if return_index < 0 or array_start < 0:
                raise ValueError(f"missing return array for POSEIDON_{kind}({width})")
            array_end = matching_bracket(body, array_start)
            values = re.findall(r"0x[0-9a-fA-F]+", body[array_start : array_end + 1])
            tables[(kind, width)] = [value.lower() for value in values]

    for width, n_partial in zip(range(2, 18), N_PARTIAL):
        expected = {
            "C": 8 * width + n_partial,
            "M": width * width,
            "P": width * width,
            "S": n_partial * (2 * width - 1),
        }
        for kind, length in expected.items():
            actual = len(tables.get((kind, width), []))
            if actual != length:
                raise ValueError(
                    f"POSEIDON_{kind}({width}) has {actual} values; expected {length}"
                )
    return tables


def vector(values: list[str], indent: str = "") -> str:
    body = "\n".join(f"{indent}  {value}," for value in values)
    return f"#v[\n{body}\n{indent}]"


def matrix(values: list[str], width: int) -> str:
    rows = []
    for row in range(width):
        entries = values[row * width : (row + 1) * width]
        rows.append("  " + vector(entries, "  ") + ",")
    return "#v[\n" + "\n".join(rows) + "\n]"


def render(tables: dict[tuple[str, int], list[str]]) -> str:
    lines = [
        "/-",
        "Poseidon constants generated from iden3/circomlib.",
        "",
        f"Source commit: {SOURCE_COMMIT}",
        "Source file: circuits/poseidon_constants.circom",
        f"Source SHA-256: {SOURCE_SHA256}",
        "",
        "DO NOT EDIT BY HAND. Regenerate with:",
        "  python3 scripts/generate_poseidon_constants.py --source <poseidon_constants.circom>",
        "Check a generated file with the same command plus `--check`.",
        "-/",
        "module",
        "",
        "public import Mathlib.Data.ZMod.Basic",
        "",
        "@[expose] public section",
        "",
        "namespace Specs.Poseidon",
        "",
    ]
    for kind in KINDS:
        if kind == "P":
            lines.extend(
                [
                    "end Specs.Poseidon",
                    "",
                    "namespace Specs.PoseidonOptimized",
                    "",
                ]
            )
        lines.extend(
            [
                "/-",
                "============================================================================",
                f"POSEIDON_{kind}",
                "============================================================================",
                "-/",
                "",
            ]
        )
        for width, n_partial in zip(range(2, 18), N_PARTIAL):
            values = tables[(kind, width)]
            if kind in ("M", "P"):
                type_text = f"Vector (Vector ℕ {width}) {width}"
                value_text = matrix(values, width)
            else:
                length = 8 * width + n_partial if kind == "C" else n_partial * (2 * width - 1)
                type_text = f"Vector ℕ {length}"
                value_text = vector(values)
                recursion_depth = max(1024, 1 << (8 * length - 1).bit_length())
                lines.append(f"set_option maxRecDepth {recursion_depth} in")
            lines.extend(
                [
                    f"def {kind}_t{width} : {type_text} := {value_text}",
                    "",
                ]
            )
    lines.extend(["end Specs.PoseidonOptimized", ""])
    return "\n".join(lines)


def verify_existing(path: Path, tables: dict[tuple[str, int], list[str]]) -> None:
    existing = path.read_text()
    declarations = list(re.finditer(r"^def ([CMPS])_t(\d+)\b", existing, re.MULTILINE))
    if not declarations:
        raise ValueError(f"no Poseidon constant declarations found in {path}")
    for index, declaration in enumerate(declarations):
        kind = declaration.group(1)
        width = int(declaration.group(2))
        end = declarations[index + 1].start() if index + 1 < len(declarations) else len(existing)
        actual = [value.lower() for value in re.findall(r"0x[0-9a-fA-F]+", existing[declaration.start() : end])]
        expected = tables[(kind, width)]
        if actual != expected:
            raise ValueError(f"existing {kind}_t{width} does not match pinned circomlib source")
    print(f"verified {len(declarations)} existing tables against pinned circomlib source")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--source", required=True, type=Path)
    parser.add_argument(
        "--output", type=Path, default=Path("Clean/Specs/PoseidonConstants.lean")
    )
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--check", action="store_true")
    mode.add_argument("--verify-existing", action="store_true")
    args = parser.parse_args()

    source_bytes = args.source.read_bytes()
    digest = hashlib.sha256(source_bytes).hexdigest()
    if digest != SOURCE_SHA256:
        raise ValueError(f"source SHA-256 is {digest}; expected {SOURCE_SHA256}")
    tables = parse_source(source_bytes.decode())

    if args.verify_existing:
        verify_existing(args.output, tables)
        return 0

    generated = render(tables)
    if args.check:
        if not args.output.exists() or args.output.read_text() != generated:
            print(f"{args.output} is not generated from the pinned source", file=sys.stderr)
            return 1
        print(f"{args.output} matches the pinned circomlib source")
        return 0

    args.output.write_text(generated)
    print(f"wrote {args.output}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
