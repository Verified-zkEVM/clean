# Clean Plonky3 backend

Plonky3 backend to demonstrate how to integrate with circuits written in Clean.

> **This is a proof of concept and not production-ready!**

Overall workflow:

1. Import the circuit written in Clean, and convert it to a plonky3 air `MainAir`.
2. Generate a trace corresponding to the circuit.
3. Prove and verify under the plonky3 backend.

This workflow is demonstrated by the tests in this repo, specifically in [`tests/clean_air.rs`](tests/clean_air.rs).
