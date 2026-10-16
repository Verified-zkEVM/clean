# Fibonacci VM example

`Ensemble.lean` specifies a global AIR ensemble end to end and proves it sound by construction. The ensemble consists of three components that communicate only through channels:

- a byte table, whose byte values are verifier-known fixed columns,
- an 8-bit addition chip that pulls from the byte channel,
- the Fibonacci VM step `fib8`, which pulls a state `(n, x, y)` from the Fibonacci channel and pushes the next one, using the addition chip.

The verifier pulls the claimed final state from the Fibonacci channel and pushes the initial state `(0, 0, 1)`. `fibonacciEnsemble` assembles the components and channels one at a time with the `SoundEnsemble` combinators. Each step only discharges local obligations about which channels a component adds guarantees and requirements for, and the result is a `FormalEnsemble`. `fibonacci_soundness` reads off its statement: any accepted public state `(n, x, y)` satisfies `(x, y) = fibonacci k` for some `k` with `k ≡ n (mod p)`.

The same file also configures generic ensemble witness generation for the example. `WitnessGenerationTest.lean` runs it in Lean, and `Rust.lean` extracts the ensemble to Rust witness and AIR code for Plonky3.

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
cargo test --locked --release --manifest-path backends/plonky3/Cargo.toml \
  --test fibonacci_ensemble_tests -- --nocapture
```

The proof test takes public values `(steps, x, y)`, generates power-of-two component traces without invoking Lean, proves the resulting Plonky3 batch, and verifies it. The verifier's initial and final Fibonacci interactions are public contributions to the channel argument.
