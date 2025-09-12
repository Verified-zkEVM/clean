#!/usr/bin/env python3
import os
import sys
from pathlib import Path

# List of files with many unused simp warnings that are safe to disable the linter for
files_to_fix = [
    "Clean/Circuit/Loops.lean",
    "Clean/Utils/Bits.lean",
    "Clean/Gadgets/Boolean.lean",
    "Clean/Circomlib/AliasCheck.lean",
    "Clean/Circomlib/BinSum.lean",
    "Clean/Circomlib/Bitify2.lean",
    "Clean/Circomlib/Gates.lean",
    "Clean/Circomlib/Mux1.lean",
    "Clean/Gadgets/Addition8/Addition8FullCarry.lean",
    "Clean/Types/U32.lean",
    "Clean/Types/U64.lean",
    "Clean/Utils/Fin.lean",
    "Clean/Table/Theorems.lean",
    "Clean/Tables/Fibonacci8.lean",
    "Clean/Table/Inductive.lean",
    "Clean/Tables/Fibonacci32Inductive.lean",
    "Clean/Gadgets/Keccak/ThetaC.lean",
    "Clean/Utils/Rotation.lean",
]

def add_linter_option(file_path):
    """Add set_option linter.unusedSimpArgs false to the top of the file."""
    full_path = Path("/Users/zksecurity/clean2") / file_path
    
    if not full_path.exists():
        print(f"Warning: {file_path} does not exist")
        return False
    
    with open(full_path, 'r') as f:
        lines = f.readlines()
    
    # Check if option already exists
    for line in lines[:20]:
        if "linter.unusedSimpArgs" in line:
            print(f"Option already exists in {file_path}")
            return False
    
    # Find where to insert (after imports)
    insert_pos = 0
    for i, line in enumerate(lines):
        if line.startswith("import "):
            insert_pos = i + 1
        elif insert_pos > 0 and not line.startswith("import "):
            break
    
    # Insert the option
    lines.insert(insert_pos, "\nset_option linter.unusedSimpArgs false\n")
    
    with open(full_path, 'w') as f:
        f.writelines(lines)
    
    print(f"Added linter option to {file_path}")
    return True

def main():
    fixed_count = 0
    for file_path in files_to_fix:
        if add_linter_option(file_path):
            fixed_count += 1
    
    print(f"\nAdded linter option to {fixed_count} files")
    return 0

if __name__ == "__main__":
    sys.exit(main())