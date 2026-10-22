#!/usr/bin/env bash
# The keccak-air showcase: Clean's keccak-air proved by CompStark, against Plonky3.
#
#   scripts/showcase.sh check L        CompStark's known answers from Plonky3, then the evidence on
#                                      2^L rows against Plonky3 (`lake exe keccak_showcase check`)
#   scripts/showcase.sh bench L REPS   trace generation, proof and verification on 2^L rows, Lean
#                                      and Plonky3 interleaved, both configurations, medians of REPS
#
# Builds Plonky3's side (`rust/`, Plonky3 a4982ec, target-cpu=native) and the Lean executable first.
set -euo pipefail
cd "$(dirname "$0")/.."
RUSTFLAGS="-C target-cpu=native" cargo build --quiet --release --manifest-path rust/Cargo.toml
lake build keccak_showcase
rust=rust/target/release/keccak-showcase
case "${1:-}" in
  check)
    lake exe keccak_showcase kat
    lake exe keccak_showcase check "$2" "$rust"
    ;;
  bench)
    mkdir -p .lake/showcase
    "$rust" inputs "$2" ".lake/showcase/inputs_$2.txt"
    for config in example proven; do
      for _ in 1 2; do
        lake exe keccak_showcase bench "$config" "$2" "$3"
        "$rust" bench "$config" "$2" "$3"
      done
    done
    ;;
  *)
    echo "usage: scripts/showcase.sh check L | bench L REPS" >&2
    exit 1
    ;;
esac
