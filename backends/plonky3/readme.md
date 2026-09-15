This is a plonky3 backend to demonstrate how to integrate with circuits written in Clean. 

THIS IS A NOT-PRODUCTION-READY POC!

Overall workflow:
1. Import the circuit written in Clean, and convert it to a plonky3 air `MainAir`.
2. Generate a trace corresponding to the circuit.
3. Prove and verify under the plonky3 backend.

This workflow is demonstrated by the tests in this repo, specifically in [`tests/fib_tests.rs`](tests/fib_tests.rs).

## Running the test

The integration test generates a Fibonacci trace from Lean and proves it with plonky3.

From the repository root, build Clean using the toolchain specified in [`lean-toolchain`](../../lean-toolchain), then run the test:

```bash
lake build
cd backends/plonky3
cargo test --locked --release --test fib_tests test_lean_circuit_end_to_end -- --exact --nocapture
```

Expected output: `test test_lean_circuit_end_to_end ... ok`.

todo: For more details in how it works, check out the [blog post](https://example.com).
