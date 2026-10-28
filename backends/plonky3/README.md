# Clean Plonky3 backend

This crate proves channel-based Clean AIR ensembles with Plonky3.

1. Lean lowers a `Clean.Air.Flat.Ensemble` into a backend-agnostic extraction program (`Clean/Backends/Program.lean`). Lowering validates the ensemble and resolves everything the printer would otherwise have to compute.
2. `Clean/Backends/Plonky3/Print.lean` prints the program mechanically, one constructor at a time: a Rust module per component with its shape, witness and fixed-column programs, constraints, and interactions, followed by a `clean_backend::ensemble!` invocation. Constraints and interactions are printed once, generic over the ring of values, and read a complete row, with the fixed columns at their input cells. The printer is part of the trusted computing base.
3. The `ensemble!` macro (`src/ensemble_macro.rs`) implements the crate's witness generation and AIR traits on top of the component modules.
4. `src/witness_generation.rs` runs the generated channel worklist and constructs all component traces without invoking Lean, building preallocated rows from the generated row functions. Each demand-generated component supplies the input of its padding rows; the worklist completes them and balances any interactions they create until every trace has a power-of-two height. Traces are also padded to the minimum height the caller passes to `generate`, the smallest that the prover's FRI parameters accept; preallocated components, whose height is fixed, must have at least that many rows.
5. `src/generated_air.rs` supplies the shared Plonky3 `Air` implementation, builds fixed traces from the generated fixed-row functions, places them at their input columns of each row, and pushes the generated channel interactions to Plonky3's LogUp buses, one bus per channel name. Lean ensembles have unique channel names and declare every channel they use, so balancing each name balances each channel.
6. `src/ensemble_prover.rs` proves or verifies an opaque generated statement containing every component AIR exactly once in canonical order, followed by a verifier AIR. The verifier AIR makes the verifier's interactions on its first row, selected by a fixed column, from the public input, which are its public values. Its trace has no other content, and the minimum trace height that the statement is constructed with, the smallest that the proof configuration accepts, so verification cost doesn't depend on the prover's trace heights.

Statement construction binds component trace heights, exact fixed heights, and the complete component inventory. It also checks the interaction-count bound of Clean's LogUp balance check, `verifier interactions + Σ(trace height × interactions per row) < field order`, before proving or verification. The ensemble must be proven sound under that check, `Balance.logUp`. It balances sums of field multiplicities, a push counting its multiplicity and a pull its negation, so every interaction is a provided LogUp count, and the bound replaces Plonky3's multiplicity height check. Every channel must have one message width. Individual component AIRs cannot be assembled through the public API. Zero-knowledge configurations are rejected: a hiding PCS salts the fixed-column commitments, which the verifier recomputes.

The Fibonacci example is documented in [`Clean/Examples/FibonacciVm/README.md`](../../Clean/Examples/FibonacciVm/README.md). The generated artifacts live in `tests/generated/` and are included by their corresponding Rust tests.

Regenerate the artifacts from the repository root. CI regenerates all of them and fails if the checked-in files differ:

```bash
lake exe export_fibonacci_ensemble_rust \
  | rustfmt --edition 2021 --emit stdout \
  > backends/plonky3/tests/generated/fibonacci_ensemble.rs
lake exe export_femtocairo_flat_air_rust \
  | rustfmt --edition 2021 --emit stdout \
  > backends/plonky3/tests/generated/femtocairo_flat_air.rs
lake exe export_opcode_vm_rust \
  | rustfmt --edition 2021 --emit stdout \
  > backends/plonky3/tests/generated/opcode_vm.rs
lake exe export_witness_ir_reference_rust \
  | rustfmt --edition 2021 --emit stdout \
  > backends/plonky3/tests/generated/witness_ir_reference.rs
lake exe export_differential_rust \
  | rustfmt --edition 2021 --emit stdout \
  > backends/plonky3/tests/generated/differential.rs
```

Run the generated witness and end-to-end proof tests:

```bash
cargo test --locked --release --manifest-path backends/plonky3/Cargo.toml \
  --test fibonacci_ensemble_tests -- --nocapture
cargo test --locked --release --manifest-path backends/plonky3/Cargo.toml \
  --test femtocairo_flat_air_tests -- --nocapture
cargo test --locked --release --manifest-path backends/plonky3/Cargo.toml \
  --test opcode_vm_tests
cargo test --locked --release --manifest-path backends/plonky3/Cargo.toml \
  --test witness_ir_reference_tests
cargo test --locked --release --manifest-path backends/plonky3/Cargo.toml \
  --test differential_tests
```

`witness_ir_reference_tests` checks the printed witness IR against Lean's semantics. Its cases (`Clean/Backends/Plonky3/Test/Reference.lean`) cover every witness IR constructor with wrapping, out-of-range, and division-by-zero edge cases. `differential_tests` checks the printed AIRs and witness generators of the examples against Lean (`Clean/Backends/Plonky3/Test/Differential.lean`): constraints and interactions on pseudo-random rows, every fixed row, verifier interactions on pseudo-random public inputs, and the generated traces.

The largest test generates, proves, and verifies a 4,096-step Fibonacci execution and reports witness generation, proving, verification, trace dimensions, and serialized proof size.

The generated ensemble path takes the public input and the flattened private input of the ensemble. The ensemble declares named hint tables as views of the private input, and the generated program builds them for the row programs of preallocated components and the witness programs of all rows to read, exactly as Lean's `prepareHint` does. Clean's `ProverData` is derived from the final component rows. Witness programs may only read cells of preallocated components that channel balancing and padding don't change; extraction rejects other reads.
