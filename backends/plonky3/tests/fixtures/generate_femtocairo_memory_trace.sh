#!/bin/bash

# Script to generate FemtoCairo memory trace JSON from Lean
# Usage: ./generate_femtocairo_memory_trace.sh <output_path>

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
CLEAN_ROOT="$(cd "$SCRIPT_DIR/../../../.." && pwd)"

# Check arguments
if [ $# -ne 1 ]; then
    echo "Usage: $0 <output_path>"
    echo "Example: $0 output/femtocairo_memory_trace.json"
    exit 1
fi

output_path="$1"

echo "Generating FemtoCairo memory trace -> $output_path"

# Change to Clean root directory to run Lean
cd "$CLEAN_ROOT" || exit 1

# Run Lean with the trace generator using lake
lake env lean --run "$SCRIPT_DIR/FemtoCairoMemoryTraceGen.lean" "$SCRIPT_DIR/$output_path"

exit_code=$?
cd "$SCRIPT_DIR" || exit 1

if [ $exit_code -eq 0 ]; then
    echo "Successfully generated memory trace: $output_path"
else
    echo "Failed to generate memory trace"
    exit 1
fi
