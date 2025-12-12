#!/usr/bin/env python3

"""
Script to detect consecutive empty lines in Lean files.
This script is used in CI to ensure code quality.
"""

import sys
from pathlib import Path


def is_empty_line(line: str) -> bool:
    """Check if a line is empty or contains only whitespace."""
    return line.strip() == ""


def check_file(file_path: Path) -> list[tuple[int, int]]:
    """
    Check a file for consecutive empty lines.

    Returns a list of tuples (start_line, end_line) where consecutive empty lines were found.
    """
    violations = []

    with open(file_path, 'r', encoding='utf-8') as f:
        lines = f.readlines()

    empty_start = None
    empty_count = 0

    for i, line in enumerate(lines, start=1):
        if is_empty_line(line):
            if empty_count == 0:
                empty_start = i
            empty_count += 1
        else:
            if empty_count >= 2:
                violations.append((empty_start, i - 1))
            empty_count = 0
            empty_start = None

    # Check if file ends with consecutive empty lines
    if empty_count >= 2:
        violations.append((empty_start, len(lines)))

    return violations


def main():
    """Main function to check all Lean files for consecutive empty lines."""
    print("Checking for consecutive empty lines in Lean files...")

    # Find all .lean files, excluding the .lake build directory
    root = Path(".")
    lean_files = [f for f in root.rglob("*.lean") if ".lake" not in f.parts]

    if not lean_files:
        print("No Lean files found to check.")
        return 0

    violations_found = False

    for file_path in sorted(lean_files):
        violations = check_file(file_path)

        if violations:
            if not violations_found:
                print()
            print(f"✗ Found consecutive empty lines in: {file_path}")
            for start, end in violations:
                print(f"  Lines: {start}-{end}")
            violations_found = True

    print()

    if violations_found:
        print("ERROR: Consecutive empty lines detected!")
        print("Please remove consecutive empty lines from the files listed above.")
        print("Each file should have at most one empty line between code blocks.")
        return 1
    else:
        print("✓ No consecutive empty lines found.")
        return 0


if __name__ == "__main__":
    sys.exit(main())
