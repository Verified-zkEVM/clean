# Halo2-Clean Plan

Goal:

1. Decide on and implement a Clean-derived way to model Halo2 circuits.
2. Use it to formalize the Orchard circuits.

The uncertain part is the Halo2-Clean design. Orchard formalization should become mostly mechanical and parallelizable once the infrastructure and proof UX are in shape.

## Direction

Model Halo2 with two Clean-derived DSLs:

- A `configure` DSL for defining custom gates and lookups. Gate constraints are written as expressions over local row/column queries. This needs generalized variable locations rather than only Nat-indexed variables.
- A `synthesize` DSL for laying out the concrete circuit. This phase should add wires/equality constraints, assign cells, enable configured gates/selectors, and produce the final circuit object.

The final low-level object should be faithful enough to compute the Halo2 verification key in Lean and compare it against the verification key extracted from Rust.

## Milestones

1. Generalize Clean's variable/environment index while keeping existing Clean behavior as `Nat`.
2. Add `Clean/Halo2` core types for the configure and synthesize models.
3. Establish a small Rust Halo2 circuit fixture and reproduce its verification key in Lean.
4. Build a small user-facing DSL prototype and use it on a minimal circuit.
5. Start formalizing real Orchard gadgets early, in parallel with hardening the infrastructure.
6. Scale from small fixtures and gadgets toward the full Orchard circuit.

