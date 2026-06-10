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

- Orchard: `orchard@orchard-0.14.0`
- halo2_gadgets: `halo2@halo2_gadgets-0.5.0/halo2_gadgets`
- halo2_proofs, if needed for utility semantics:
  `halo2@halo2_gadgets-0.5.0/halo2_proofs`

If a future agent cannot find the relevant source code, it must stop and ask Gregor instead
of guessing the implementation.

## Suggested order

1. Build the small ECC assertion layer from `halo2_gadgets/src/ecc/chip`.
2. Port simple utilities used pervasively by Orchard, especially range checks and running
   sums, from `halo2_gadgets/src/utilities`.
3. Port Sinsemilla gates from `halo2_gadgets/src/sinsemilla`.
4. Port Orchard-specific custom gates from `orchard@orchard-0.14.0/src/circuit.rs`,
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

## Current source dependency map

Authoritative source tags:

- `halo2_gadgets`: `/root/code/halo2`, tag `halo2_gadgets-0.5.0`
- `orchard`: `/root/code/orchard`, tag `0.14.0` (the Orchard 0.14.0 release tag)

Bottom-up implementation order currently inferred from those tagged sources:

1. ECC point assertions:
   `halo2_gadgets/src/ecc/chip/witness_point.rs`
   - Clean module: `Clean.Orchard.Ecc`
   - Status: ported as `PointOrIdentity.circuit` and `NonIdentityPoint.circuit`.
2. Utility conditional swap/mux gate:
   `halo2_gadgets/src/utilities/cond_swap.rs`
   - Clean module: `Clean.Orchard.Utilities`
   - Status: `CondSwap.circuit` ports the three gate constraints for scalar field values.
   - Point muxes are expected to reuse the scalar circuit on `x` and `y`.
3. ECC addition layer:
   `halo2_gadgets/src/ecc/chip/add_incomplete.rs`,
   `halo2_gadgets/src/ecc/chip/add.rs`
   - Depends on non-identity point assertions.
   - Status: incomplete addition is ported as `IncompleteAdd.circuit`; complete
     addition custom-gate constraints are ported as `CompleteAdd.circuit`.
4. Running sums and range checks:
   `halo2_gadgets/src/utilities/decompose_running_sum.rs`,
   `halo2_gadgets/src/utilities/lookup_range_check.rs`
   - Depends on the Sinsemilla window size constants and generator-table lookup semantics.
   - Status: the short running-sum row range-check gate from
     `decompose_running_sum.rs` is ported as `Orchard.Utilities.RunningSum.circuit`.
     The short lookup bitshift gate from `lookup_range_check.rs` is ported as
     `Orchard.Utilities.LookupRangeCheck.circuit`.
5. Fixed-base and variable-base scalar multiplication:
   `halo2_gadgets/src/ecc/chip/mul*.rs`
   - Depends on ECC addition, conditional selection/swap, running sums, range checks, and
     fixed-base lookup tables.
6. Sinsemilla:
   `halo2_gadgets/src/sinsemilla/chip.rs`,
   `halo2_gadgets/src/sinsemilla/chip/hash_to_point.rs`,
   `halo2_gadgets/src/sinsemilla/merkle*.rs`
   - Depends on generator-table lookup, range checks, ECC addition, and conditional swap.
   - Status: `Initial y_Q` and `Sinsemilla gate` arithmetic constraints from
     `chip.rs` are ported as `Orchard.Sinsemilla.InitialYQ.circuit` and
     `Orchard.Sinsemilla.Gate.circuit`. The MerkleCRH decomposition gate from
     `merkle/chip.rs` is ported as `Orchard.Sinsemilla.Merkle.circuit`.
7. Orchard custom gates and composition:
   `orchard/src/circuit.rs`,
   `orchard/src/circuit/commit_ivk.rs`,
   `orchard/src/circuit/note_commit.rs`,
   `orchard/src/circuit/gadget.rs`,
   `orchard/src/circuit/gadget/add_chip.rs`
   - Depends on Sinsemilla, ECC fixed-base/variable-base multiplication, and Orchard-specific
     decomposition/canonicity gates.
   - Status: `gadget/add_chip.rs` is ported as `Orchard.Utilities.AddChip.circuit`.
     The four `Orchard circuit checks` constraints from `circuit.rs` are ported as
     `Orchard.ActionChecks.circuit`. `note_commit.rs` gates `NoteCommit MessagePiece b`,
     `d`, `e`, `g`, `h`, and `NoteCommit input value` are ported as
     `Orchard.NoteCommit.DecomposeB.circuit`, `Orchard.NoteCommit.DecomposeD.circuit`,
     `Orchard.NoteCommit.DecomposeE.circuit`, `Orchard.NoteCommit.DecomposeG.circuit`,
     `Orchard.NoteCommit.DecomposeH.circuit`, and
     `Orchard.NoteCommit.ValueCanonicity.circuit`.
