#!/bin/bash
# Generic Lean script runner.
# Usage: run_lean.sh <lean_file> [extra_args...] <output_path>

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
CLEAN_ROOT="$(cd "$SCRIPT_DIR/../../../.." && pwd)"

if [ $# -lt 2 ]; then
    echo "Usage: $0 <lean_file> [extra_args...] <output_path>"
    exit 1
fi

lean_file="$1"; shift
# Last remaining arg is output_path; everything in between is extra args
args=("$@")
output_path="${args[-1]}"
extra_args=("${args[@]:0:${#args[@]}-1}")

echo "Running $lean_file -> $output_path"

cd "$CLEAN_ROOT" || exit 1
lake env lean --run "$SCRIPT_DIR/$lean_file" "${extra_args[@]}" "$SCRIPT_DIR/$output_path"
exit_code=$?

if [ $exit_code -eq 0 ]; then
    echo "Successfully generated: $output_path"
else
    echo "Failed to run $lean_file"
fi
exit $exit_code
