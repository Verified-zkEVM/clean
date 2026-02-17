This is a plonky3 backend to demonstrate how to integrate with circuits written in Clean. 

THIS IS A NOT-PRODUCTION-READY POC!

Overall workflow:
1. Import the circuit written in Clean, and convert it to a plonky3 air `MainAir`.
2. Generate a trace corresponding to the circuit.
3. Prove and verify under the plonky3 backend.

This workflow is demonstrated by the tests in this repo, specifically in [`tests/clean_air.rs`](tests/clean_air.rs).

## Running the test

The integration test generates a Fibonacci trace from Lean and proves it with plonky3:

```bash
cd backends/plonky3
cargo test --release -- --nocapture test_clean_fib
```

Expected output: `test test_clean_fib ... ok` (test execution takes ~2 seconds in release mode)

todo: For more details in how it works, check out the [blog post](https://example.com).