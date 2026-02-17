#!/bin/bash

# Simplified script to generate Fibonacci traces from Lean
# Usage: ./generate_trace.sh <steps> <output_path>

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
CLEAN_ROOT="$(cd "$SCRIPT_DIR/../../.." && pwd)"
TESTS_DIR="$SCRIPT_DIR"

# Check arguments
if [ $# -ne 2 ]; then
    echo "Usage: $0 <steps> <output_path>"
    echo "Example: $0 256 tests/generated_trace.json"
    exit 1
fi

steps="$1"
output_path="$2"

echo "Generating trace with $steps steps -> $output_path"

# Change to Clean root directory to run Lean
cd "$CLEAN_ROOT" || exit 1

# Run Lean with the trace generator using lake
lake env lean --run "$TESTS_DIR/TraceGen.lean" "$steps" "$TESTS_DIR/$output_path"

exit_code=$?
cd "$TESTS_DIR" || exit 1

if [ $exit_code -eq 0 ]; then
    echo "Successfully generated trace: $output_path"
else
    echo "Failed to generate trace"
    exit 1
fi
