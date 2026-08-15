# Clean Plonky3 backend

This crate proves channel-based Clean AIR ensembles with Plonky3.

1. Lean lowers a `Clean.Air.Flat.Ensemble` into a typed extraction program.
2. The Rust renderer emits direct row witness functions, constraint expressions, and channel
   interactions. It does not emit generic Plonky3 plumbing.
3. `src/witness_generation.rs` runs the generated channel worklist and constructs all component
   traces without invoking Lean. Lean's witness configuration supplies semantic padding rows; the
   worklist executes them and balances any interactions they create until every trace has a
   power-of-two height.
4. `src/generated_air.rs` supplies the shared Plonky3 `Air` implementation and registers generated
   channel lookups.
5. `src/ensemble_prover.rs` proves or verifies an opaque generated statement containing every
   component AIR exactly once in canonical order. Verifier-only interactions are derived from
   public inputs and enter the global channel argument directly, without a synthetic verifier AIR
   or trace.

Statement construction binds component trace heights, exact fixed heights, and the complete
component inventory. It also checks the Clean channel-soundness side condition
`verifier interactions + Σ(trace height × interactions per row) < field order` before proving or
verification. Individual component AIRs cannot be assembled through the public API.

The Fibonacci example is documented in
[`Clean/Examples/FibonacciVm/README.md`](../../Clean/Examples/FibonacciVm/README.md). The generated
artifacts live in `tests/generated/` and are included by their corresponding Rust tests.

Regenerate the artifact from the repository root:

```bash
lake exe export_fibonacci_ensemble_rust \
  | rustfmt --edition 2021 --emit stdout \
  > backends/plonky3/tests/generated/fibonacci_ensemble.rs
```

Run the generated witness and end-to-end proof tests:

```bash
cargo test --release --manifest-path backends/plonky3/Cargo.toml \
  --test fibonacci_ensemble_tests -- --nocapture
cargo test --release --manifest-path backends/plonky3/Cargo.toml \
  --test femtocairo_flat_air_tests -- --nocapture
```

The largest test generates, proves, and verifies a 4,096-step Fibonacci execution and reports
witness generation, proving, verification, trace dimensions, and serialized proof size.

The generated ensemble path accepts a separately serialized runtime prover input for initializing
private committed columns. Clean's semantic `ProverData` is not supplied by the caller: it is
derived from the final component rows. Extracted witness programs may read stable cells of
preallocated component data; reads from demand-generated or mutable cells are rejected during
extraction. External hint reads remain unsupported.
