#!/bin/bash

# Script to generate FemtoCairo circuit and trace JSON from Lean
# Usage: ./generate_femtocairo_trace.sh <circuit_output_path> <trace_output_path>

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
CLEAN_ROOT="$(cd "$SCRIPT_DIR/../../.." && pwd)"
TESTS_DIR="$SCRIPT_DIR"

# Default output paths
circuit_path="${1:-test_data/femtocairo_circuit.json}"
trace_path="${2:-test_data/femtocairo_trace.json}"

echo "Generating FemtoCairo circuit and trace..."
echo "  Circuit: $circuit_path"
echo "  Trace:   $trace_path"

# Ensure output directory exists
mkdir -p "$TESTS_DIR/$(dirname "$circuit_path")"
mkdir -p "$TESTS_DIR/$(dirname "$trace_path")"

# Change to Clean root directory to run Lean
cd "$CLEAN_ROOT" || exit 1

# Run Lean with the FemtoCairo generator
lake env lean --run "$TESTS_DIR/FemtoCairoGen.lean" "$TESTS_DIR/$circuit_path" "$TESTS_DIR/$trace_path"

exit_code=$?
cd "$TESTS_DIR" || exit 1

if [ $exit_code -eq 0 ]; then
    echo "Successfully generated FemtoCairo data"
else
    echo "Failed to generate FemtoCairo data"
    exit 1
fi
