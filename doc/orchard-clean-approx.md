# Orchard Clean approximation plan

This PR starts a new Orchard formalization path with a deliberately narrower goal than
`halo2-in-clean`.

The goal is to implement the Orchard circuit logic in Clean as an arithmetic model of the
real circuit, without faithfully modelling Halo2, PLONK, selector compression, regions,
rotations, permutation arguments, pinned verification keys, or the exact layout machinery.

## Scope

- Port Orchard and `halo2_gadgets` gadget relations into ordinary Clean circuits.
- Model Halo2 custom gates as `FormalAssertion`s or small `FormalCircuit`s.
- Model Halo2 copy constraints with shared Clean values or `===`.
- Use Clean subcircuits for composition.
- Keep specs over high-level typed inputs whenever practical.
- Leave faithful Halo2 arithmetization modelling for a separate design effort.

This is an approximation: it can verify that the intended arithmetic relations are
consistent and compose correctly, but it does not prove that the deployed Halo2 circuit has
the same selectors, layout, copy constraints, lookup arguments, or verifying key.

## Hard reference rule

Every gadget must be ported from the actual Halo2/Orchard implementation. Do not infer a
gadget from memory, from the protocol description alone, or from a simplified mathematical
guess.

Reference sources for this branch:

- Orchard: `/mnt/data-2tb/zks/audits/zcash-orchard/orchard-0.14.0`
- halo2_gadgets: `/mnt/data-2tb/zks/audits/zcash-orchard/halo2-halo2_gadgets-0.5.0/halo2_gadgets`
- halo2_proofs, if needed for utility semantics:
  `/mnt/data-2tb/zks/audits/zcash-orchard/halo2-halo2_gadgets-0.5.0/halo2_proofs`

If a future agent cannot find the relevant source code, it must stop and ask Gregor instead
of guessing the implementation.

## Suggested order

1. Build the small ECC assertion layer from `halo2_gadgets/src/ecc/chip`.
2. Port simple utilities used pervasively by Orchard, especially range checks and running
   sums, from `halo2_gadgets/src/utilities`.
3. Port Sinsemilla gates from `halo2_gadgets/src/sinsemilla`.
4. Port Orchard-specific custom gates from `orchard-0.14.0/src/circuit.rs`,
   `commit_ivk.rs`, and `note_commit.rs`.
5. Compose higher-level Orchard pieces: note commitment, value commitment, nullifier,
   spend authorization, and action checks.
6. Keep a source map in comments as files grow, so each Clean gadget names the exact Rust
   source it follows.

## First milestone

The first gadget is the Pallas witness-point assertion from:

`halo2_gadgets/src/ecc/chip/witness_point.rs`

It ports the two Halo2 gates:

- `witness point`: accepts either `(0, 0)` for the identity encoding or a point satisfying
  `y^2 = x^3 + 5`.
- `witness non-identity point`: requires the curve equation directly.
