# Fibonacci VM example

This directory contains the channel-based Fibonacci VM used to exercise generic ensemble witness
generation and the Rust/Plonky3 extraction path.

- `Circuit.lean` defines the byte and addition chips, the Fibonacci VM, its formally sound
  ensemble, and the explicit witness-generation and semantic-padding configuration.
- `WitnessGenerationTest.lean` executes the generic ensemble witness builder in Lean. It checks
  constraints and channel balance, repeated-pull coalescing, byte multiplicities greater than one,
  and fuel exhaustion.
- `EnsembleRust.lean` lowers the ensemble to direct Rust witness and AIR code.

Build the Lean tests with:

```bash
lake build CleanTests
```

Regenerate and format the checked-in Rust artifact with:

```bash
lake exe export_fibonacci_ensemble_rust \
  | rustfmt --edition 2021 --emit stdout \
  > backends/plonky3/tests/generated/fibonacci_ensemble.rs
```

Run the generated Rust witness and proof tests with:

```bash
cargo test --release --manifest-path backends/plonky3/Cargo.toml \
  --test fibonacci_ensemble_tests -- --nocapture
```

The proof test takes public values `(steps, x, y)`, generates power-of-two component traces without
invoking Lean, proves the resulting Plonky3 batch, and verifies it. The verifier's initial and final
Fibonacci interactions are public contributions to the channel argument rather than a synthetic
trace. External `ProverData` and hint reads are not supported by this extraction slice.
