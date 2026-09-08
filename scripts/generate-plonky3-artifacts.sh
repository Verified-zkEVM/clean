#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "${BASH_SOURCE[0]}")/.."
if [[ $# -gt 1 || ($# -eq 1 && "$1" != --check) ]]; then
  echo "usage: $0 [--check]" >&2
  exit 2
fi

artifact_dir=$(mktemp -d)
trap 'rm -rf "$artifact_dir"' EXIT

lake build export_fibonacci_ensemble_rust export_backend_test_data
.lake/build/bin/export_fibonacci_ensemble_rust > "$artifact_dir/fibonacci_ensemble.rs"
.lake/build/bin/export_backend_test_data "$artifact_dir"
rustfmt --edition 2021 "$artifact_dir/fibonacci_ensemble.rs" "$artifact_dir/witness_edges.rs"

for artifact in fibonacci_ensemble.rs witness_edges.rs witness_reference.json; do
  destination="backends/plonky3/tests/generated/$artifact"
  if [[ ${1:-} == --check ]]; then
    diff -u "$destination" "$artifact_dir/$artifact"
  else
    cp "$artifact_dir/$artifact" "$destination"
  fi
done
