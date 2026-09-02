# Clean Plonky3 backend

This crate proves Clean AIR circuits with Plonky3. It currently contains two integration paths
while the older JSON backend is being replaced.

## Generated ensemble path

This is the maintained path for new channel-based AIR work.

1. Lean lowers a `Clean.Air.Flat.Ensemble` into a typed extraction program.
2. The Rust renderer emits direct row witness functions, constraint expressions, and channel
   interactions. It does not emit generic Plonky3 plumbing.
3. `src/witness_generation.rs` runs the generated channel worklist and constructs all component
   traces without invoking Lean. Lean's witness configuration supplies semantic padding rows; the
   worklist executes them and balances any interactions they create until every trace has a
   power-of-two height.
4. `src/generated_air.rs` supplies the shared Plonky3 `Air` implementation and registers generated
   channel lookups.
5. `src/ensemble_prover.rs` validates statement shape and proves or verifies the component batch.
   Verifier-only interactions are derived from public inputs and enter the global channel argument
   directly, without a synthetic verifier AIR or trace.

The complete example is documented in
[`Clean/Examples/FibonacciVm/README.md`](../../Clean/Examples/FibonacciVm/README.md). Its generated
artifact is `tests/generated/fibonacci_ensemble.rs`, included by `tests/fibonacci_ensemble_tests.rs`.

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
```

The largest test generates, proves, and verifies a 4,096-step Fibonacci execution and reports
witness generation, proving, verification, trace dimensions, and serialized proof size.

## Legacy JSON path

The original backend reads constraints serialized as JSON and interprets their expression trees at
runtime:

- `src/clean_ast.rs` parses the serialized operations.
- `src/clean_air.rs` evaluates them through a generic `Air` implementation.
- `src/lookup.rs` and `src/lookup_trace.rs` implement the older lookup-table integration.
- `src/prover.rs` and `src/verifier.rs` prove and verify that representation.

`tests/fib_tests.rs`, `tests/lookup_tests.rs`, and `tests/lookup_negative_tests.rs` cover this path.
`tests/femtocairo_tests.rs` is the existing FemtoCairo adapter and still generates its fixtures by
running Lean. This path remains for regression coverage; new functionality should use generated
ensembles and channels.

Run all backend tests with:

```bash
cargo test --manifest-path backends/plonky3/Cargo.toml
cargo test --release --manifest-path backends/plonky3/Cargo.toml
```

The backend is still experimental. In particular, the generated ensemble path intentionally rejects
external `ProverData` and hint reads until their proof-system semantics are defined.
