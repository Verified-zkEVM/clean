# Orchard conformance audit

This file records the current survey of `Clean/Orchard` against Orchard 0.14.0 and `halo2_gadgets-0.5.0` sources.

Rule for naming: a Clean circuit gets `name := "GATE <source name>"` only when it is
intended to correspond to a concrete source `meta.create_gate("<source name>", ...)`.

## Named source gates

The following Clean circuits now carry source-derived gate names:

- `GATE witness point`
- `GATE witness non-identity point`
- `GATE complete addition`
- `GATE range check`
- `GATE Short lookup bitshift`
- `GATE LSB check`
- `GATE Decompose scalar for complete bits of variable-base mul`
- `GATE q_mul_1 == 1 checks`
- `GATE q_mul_2 == 1 checks`
- `GATE q_mul_3 == 1 checks`
- `GATE overflow checks`
- `GATE Running sum coordinates check`
- `GATE Full-width fixed-base scalar mul`
- `GATE Canonicity checks`
- `GATE Short fixed-base mul gate`
- `GATE full round`
- `GATE partial rounds`
- `GATE pad-and-add`
- `GATE Initial y_Q`
- `GATE Sinsemilla gate`
- `GATE Decomposition check`
- `GATE NoteCommit MessagePiece b`
- `GATE NoteCommit MessagePiece d`
- `GATE NoteCommit MessagePiece e`
- `GATE NoteCommit MessagePiece g`
- `GATE NoteCommit MessagePiece h`
- `GATE NoteCommit input g_d`
- `GATE NoteCommit input pk_d`
- `GATE NoteCommit input value`
- `GATE NoteCommit input rho`
- `GATE NoteCommit input psi`
- `GATE y coordinate checks`
- `GATE CommitIvk canonicity check`
- `GATE Orchard circuit checks`

## Known non-conformances

These items should not be treated as exact Halo2 gate/API ports until repaired.

- **Missing factored gate assertions for entry circuits:** `Ecc.IncompleteAdd.circuit`,
  `Utilities.CondSwap.circuit`, and `Utilities.AddChip.circuit` are entry-level
  `FormalCircuit`s that witness outputs internally. That is the right API shape for their
  callers, but the source custom gates should still be factored out as named
  `FormalAssertion`s and composed by these entry circuits:
  - `GATE incomplete addition`
  - `GATE a' = b ⋅ swap + a ⋅ (1-swap)`
  - `GATE Field element addition: c = a + b`

- **`GATE range check` and `LookupRangeCheck.shortRangeCircuit`:** Clean uses polynomial
  range membership for some range checks. Source lookup-backed range checks must be ported
  using Clean lookups, not polynomial stand-ins, when layout/source conformance matters.

- **`GATE q_mul_1 == 1 checks`, `GATE q_mul_2 == 1 checks`, and
  `GATE q_mul_3 == 1 checks`:** Clean splits/shared the incomplete-mul loop equations into
  helper rows. The source has three selector-enabled gates with specific rotations; q_mul_2
  additionally includes base-coordinate constancy checks.

- **`ScalarMul.FixedBase.Coords.circuit`:** this is a helper for `coords_check`, not a
  source `meta.create_gate` by itself. It intentionally has no `GATE` name.

- **`GATE Canonicity checks`:** Clean ports the arithmetic checks, but not the surrounding
  lookup/running-sum API or exact fixed/advice column and rotation layout for base-field
  fixed-base mul.

- **Poseidon entry APIs:** exact ports of `Pow5Chip::permute`,
  `PoseidonSpongeInstructions::initial_state`, `PoseidonSpongeInstructions::add_input`,
  `Hash::init`, and `Hash::hash` are not implemented. Current Clean coverage is limited
  to the named `full round`, `partial rounds`, and `pad-and-add` gate assertions.

- **`GATE Initial y_Q` and `GATE Sinsemilla gate`:** Clean exposes source-rotated advice
  values as row fields and does not encode the exact fixed/advice/rotation layout.

- **Sinsemilla entry APIs:** `hash_to_point`, `HashDomain::hash`,
  `CommitDomain::commit`, `CommitDomain::short_commit`, `MerkleInstructions::hash_layer`,
  and `MerklePath::calculate_root` are not implemented. Current Clean coverage is limited
  to the named custom gates and the Merkle decomposition gate.

- **`GATE Decomposition check`:** Clean ports the Merkle decomposition arithmetic but does
  not encode the source copy constraints, fixed/advice roles, or hash-to-point child API.

- **NoteCommit and CommitIvk named gates:** Clean ports their arithmetic identities, but
  does not yet record the exact advice column roles, rotations, or selector layout.

- **Orchard source entry APIs:** `value_commit_orchard`, `derive_nullifier`,
  spend-authority key derivation, `gadgets::note_commit`, `gadgets::commit_ivk`, and the
  full `Circuit::synthesize` action entry circuit are not implemented. They must compose
  source-conformant child entry circuits rather than accept intermediate hash, commitment,
  or scalar-multiplication products as inputs.

- (known issue for reproducing VKs, fix not currently in scope) **All named gates:**
  current Clean rows do not distinguish advice cells, fixed cells, selector cells,
  equality-enabled columns, column identity, or rotations such as current/next/previous
  row queries. This is enough for arithmetic proof work, but not enough to reconstruct the
  Halo2 layout or pinned VK.
