#!/usr/bin/env python3
import re
import subprocess
import sys
from pathlib import Path

def get_unused_simp_warnings():
    """Run lake build and capture unused simp warnings."""
    print("Running lake build to capture warnings...")
    result = subprocess.run(["lake", "build"], capture_output=True, text=True)
    
    warnings = []
    lines = result.stderr.split('\n')
    
    for i, line in enumerate(lines):
        if "This simp argument is unused:" in line and i+1 < len(lines):
            # Parse the file and location from previous lines
            for j in range(max(0, i-5), i):
                if "warning:" in lines[j] and ".lean:" in lines[j]:
                    parts = lines[j].split(":")
                    if len(parts) >= 3:
                        file_path = parts[0].replace("warning", "").strip()
                        line_col = parts[1] + ":" + parts[2]
                        unused_arg = lines[i+1].strip()
                        warnings.append((file_path, line_col, unused_arg))
                        break
    
    return warnings

def fix_file_warnings(file_path, warnings):
    """Fix warnings in a specific file."""
    if not Path(file_path).exists():
        return False
    
    with open(file_path, 'r') as f:
        content = f.read()
    
    original_content = content
    
    # Sort warnings by line number in reverse order to avoid offset issues
    file_warnings = [(w[1], w[2]) for w in warnings if w[0] == file_path]
    file_warnings.sort(reverse=True)
    
    for line_col, unused_arg in file_warnings:
        # Remove the unused argument from simp calls
        # Match patterns like: simp [..., unused_arg, ...]
        patterns = [
            (rf'simp\s+only\s*\[[^]]*,\s*{re.escape(unused_arg)}\s*,', 'simp only ['),
            (rf'simp\s+only\s*\[[^]]*,\s*{re.escape(unused_arg)}\s*\]', ']'),
            (rf'simp\s*\[[^]]*,\s*{re.escape(unused_arg)}\s*,', 'simp ['),
            (rf'simp\s*\[[^]]*,\s*{re.escape(unused_arg)}\s*\]', ']'),
            (rf'simp_all\s+only\s*\[[^]]*,\s*{re.escape(unused_arg)}\s*,', 'simp_all only ['),
            (rf'simp_all\s+only\s*\[[^]]*,\s*{re.escape(unused_arg)}\s*\]', ']'),
            (rf'simp_all\s*\[[^]]*,\s*{re.escape(unused_arg)}\s*,', 'simp_all ['),
            (rf'simp_all\s*\[[^]]*,\s*{re.escape(unused_arg)}\s*\]', ']'),
        ]
        
        for pattern, replacement in patterns:
            new_content = re.sub(pattern, lambda m: m.group(0).replace(f", {unused_arg}", "").replace(f"{unused_arg}, ", "").replace(f"{unused_arg}", ""), content)
            if new_content != content:
                content = new_content
                break
    
    if content != original_content:
        with open(file_path, 'w') as f:
            f.write(content)
        return True
    
    return False

def main():
    warnings = get_unused_simp_warnings()
    
    if not warnings:
        print("No unused simp warnings found!")
        return 0
    
    print(f"Found {len(warnings)} unused simp warnings")
    
    # Group warnings by file
    files_to_fix = {}
    for file_path, line_col, unused_arg in warnings:
        if file_path not in files_to_fix:
            files_to_fix[file_path] = []
        files_to_fix[file_path].append((file_path, line_col, unused_arg))
    
    print(f"Warnings found in {len(files_to_fix)} files")
    
    fixed_count = 0
    for file_path, file_warnings in files_to_fix.items():
        print(f"Fixing {len(file_warnings)} warnings in {file_path}")
        if fix_file_warnings(file_path, file_warnings):
            fixed_count += 1
    
    print(f"Fixed warnings in {fixed_count} files")
    
    # Run lake build again to check
    print("\nRunning lake build again to verify fixes...")
    result = subprocess.run(["lake", "build"], capture_output=True, text=True)
    
    remaining_warnings = len([line for line in result.stderr.split('\n') if "This simp argument is unused:" in line])
    
    if remaining_warnings > 0:
        print(f"Still {remaining_warnings} warnings remaining. May need manual intervention.")
        return 1
    else:
        print("All unused simp warnings fixed!")
        return 0

if __name__ == "__main__":
    sys.exit(main())