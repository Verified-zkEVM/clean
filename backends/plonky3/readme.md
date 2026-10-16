# Clean Plonky3 backend

This crate proves channel-based Clean AIR ensembles with Plonky3.

1. Lean lowers a `Clean.Air.Flat.Ensemble` into a backend-agnostic extraction program (`Clean/Backends/Program.lean`). Lowering validates the ensemble and resolves everything the printer would otherwise have to compute.
2. `Clean/Backends/Plonky3/Print.lean` prints the program mechanically, one constructor at a time: a Rust module per component with its shape, witness and fixed-column programs, constraints, and interactions, followed by a `clean_backend::ensemble!` invocation. Constraints and interactions are printed once, generic over the ring of values, and read a complete row whose fixed columns come first. The printer is part of the trusted computing base.
3. The `ensemble!` macro (`src/ensemble_macro.rs`) implements the crate's witness generation and AIR traits on top of the component modules.
4. `src/witness_generation.rs` runs the generated channel worklist and constructs all component traces without invoking Lean, building preallocated rows from the generated row functions. Lean's witness configuration supplies semantic padding rows; the worklist executes them and balances any interactions they create until every trace has a power-of-two height.
5. `src/generated_air.rs` supplies the shared Plonky3 `Air` implementation, builds fixed traces from the generated fixed-row functions, and registers the generated channel interactions as lookups.
6. `src/ensemble_prover.rs` proves or verifies an opaque generated statement containing every component AIR exactly once in canonical order. Verifier-only interactions are derived from public inputs and enter the global channel argument directly, without a synthetic verifier AIR or trace.

Statement construction binds component trace heights, exact fixed heights, and the complete component inventory. It also checks the Clean channel-soundness side condition `verifier interactions + Σ(trace height × interactions per row) < field order` before proving or verification. Individual component AIRs cannot be assembled through the public API.

The Fibonacci example is documented in [`Clean/Examples/FibonacciVm/README.md`](../../Clean/Examples/FibonacciVm/README.md). The generated artifacts live in `tests/generated/` and are included by their corresponding Rust tests.

Regenerate the artifacts from the repository root. CI regenerates all of them and fails if the checked-in files differ:

```bash
lake exe export_fibonacci_ensemble_rust \
  | rustfmt --edition 2021 --emit stdout \
  > backends/plonky3/tests/generated/fibonacci_ensemble.rs
lake exe export_femtocairo_flat_air_rust \
  | rustfmt --edition 2021 --emit stdout \
  > backends/plonky3/tests/generated/femtocairo_flat_air.rs
lake exe export_witness_ir_reference_rust \
  | rustfmt --edition 2021 --emit stdout \
  > backends/plonky3/tests/generated/witness_ir_reference.rs
```

Run the generated witness and end-to-end proof tests:

```bash
cargo test --locked --release --manifest-path backends/plonky3/Cargo.toml \
  --test fibonacci_ensemble_tests -- --nocapture
cargo test --locked --release --manifest-path backends/plonky3/Cargo.toml \
  --test femtocairo_flat_air_tests -- --nocapture
cargo test --locked --release --manifest-path backends/plonky3/Cargo.toml \
  --test witness_ir_reference_tests
```

`witness_ir_reference_tests` checks the printed witness IR against Lean's semantics. Its cases (`Clean/Backends/Plonky3/Test/Reference.lean`) cover every witness IR constructor with wrapping, out-of-range, and division-by-zero edge cases.

The largest test generates, proves, and verifies a 4,096-step Fibonacci execution and reports witness generation, proving, verification, trace dimensions, and serialized proof size.

The generated ensemble path takes the public input and the flattened private input of the formal ensemble. The ensemble declares named hint tables as views of the private input, and the generated program builds them for the row programs of preallocated components and the witness programs of all rows to read, exactly as Lean's `FormalEnsemble.hint` does. Clean's `ProverData` is derived from the final component rows. Witness programs may only read cells of preallocated components that channel balancing and padding don't change; extraction rejects other reads.
