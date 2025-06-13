This is a plonky3 backend to demonstrate how to integrate with circuits written in Clean. 

THIS IS A NOT-PRODUCTION-READY POC!

Overall workflow:
1. Import the circuit written in Clean, and convert it to a plonky3 air `MainAir`.
2. Generate a trace corresponding to the circuit.
3. Prove and verify under the plonky3 backend.

This workflow is demonstrated by the tests in this repo, specifically in [`tests/clean_air.rs`](tests/clean_air.rs).

todo: For more details in how it works, check out the [blog post](https://example.com).