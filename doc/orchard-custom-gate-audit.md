# Orchard custom gate audit

This file records the current survey of `Clean/Orchard` custom-gate assertions against
the gate names in the Orchard 0.14.0 and `halo2_gadgets-0.5.0` sources.

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

- **`GATE LSB check`:** Clean exposes the rotated advice values as row fields. The source
  gate queries `z_1`, `z_0`, `x_p`, `y_p`, `base_x`, and `base_y` from specific columns and
  rotations.

- **`GATE q_mul_1 == 1 checks`, `GATE q_mul_2 == 1 checks`, and
  `GATE q_mul_3 == 1 checks`:** Clean splits/shared the incomplete-mul loop equations into
  helper rows. The source has three selector-enabled gates with specific rotations; q_mul_2
  additionally includes base-coordinate constancy checks.

- **`ScalarMul.FixedBase.Coords.circuit`:** this is a helper for `coords_check`, not a
  source `meta.create_gate` by itself. It intentionally has no `GATE` name.

- **`GATE Running sum coordinates check` and `GATE Full-width fixed-base scalar mul`:**
  Clean represents interpolation coefficients and `z` values as ordinary row inputs. The
  source uses fixed columns and configured advice columns.

- **`GATE Canonicity checks`:** Clean ports the arithmetic checks, but not the surrounding
  lookup/running-sum API or exact column/rotation layout for base-field fixed-base mul.

- **`GATE full round`, `GATE partial rounds`, and `GATE pad-and-add`:** Clean represents
  round constants as row values. The source uses fixed columns supplied by the Poseidon
  chip configuration.

- **Poseidon permutation/link/hash wrappers:** `Permutation.InitialToFull`,
  `FullToFull`, `FullToPartial`, `PartialToPartial`, `PartialToFull`, `FullToOutput`,
  `FullRowsBlock`, `InitialFullBlock`, `FinalFullBlock`, `PartialPairBlock`,
  `PartialRows4Block`, `PartialRows8Block`, `Hash2`, and
  `Hash2PermutationBoundary` are not source `meta.create_gate` definitions. They should
  remain unnamed as `GATE`s unless replaced by an exact source API port.

- **`GATE Initial y_Q` and `GATE Sinsemilla gate`:** Clean exposes source-rotated values
  as row fields and does not encode the exact fixed/advice/rotation layout.

- **`Sinsemilla.InitWiring`, `Commit.Entry`, `ShortCommit.Entry`, `Merkle.Wiring`, and
  `Merkle.PathStep`:** these are wiring/partial-entry helpers, not direct source custom
  gates. They should not receive `GATE` names.

- **`GATE Decomposition check`:** Clean ports the Merkle decomposition arithmetic but does
  not encode the source copy constraints, fixed/advice roles, or hash-to-point child API.

- **NoteCommit and CommitIvk named gates:** Clean ports their arithmetic identities, but
  does not yet record the exact fixed/advice column roles or selector layout.

- **`ActionWiring`, `ActionComputedWiring.Entry`, `ActionNoteCommitWiring`, and
  `ActionAddressWiring`:** these are not custom gates. They are higher-level wiring or
  partial-entry circuits and must not be used as evidence that the Orchard synthesize path
  has been ported.

- **`Gadget.ValueCommitment.Entry`, `Gadget.Nullifier.Entry`,
  `Gadget.NullifierWithHash.Entry`, `Gadget.NullifierWithPoseidonBoundary.Entry`, and
  `Gadget.SpendAuth.Entry`:** these are not custom gates and currently have the wrong
  source API boundary because scalar-multiplication products are explicit inputs.

- **`NoteCommit.Wiring`, `NoteCommit.WiringWithCommit`, `CommitIvk.Wiring`, and
  `CommitIvk.WiringWithShortCommit`:** these are not custom gates. They expose values that
  the source APIs compute internally and should be deleted, renamed, or rebuilt after the
  missing scalar-mul and Sinsemilla entry APIs exist.

- (known issue for reproducing VKs, fix not currently in scope) **All named gates:** current Clean rows do not distinguish advice cells, fixed cells,
  selector cells, rotations, or equality-enabled columns. This is enough for arithmetic
  proof work, but not enough to reconstruct the Halo2 layout or pinned VK.
