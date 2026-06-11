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

- **`GATE q_mul_1 == 1 checks`, `GATE q_mul_2 == 1 checks`, and
  `GATE q_mul_3 == 1 checks`:** Clean splits/shared the incomplete-mul loop equations into
  helper rows. The source has three selector-enabled gates with specific rotations; q_mul_2
  additionally includes base-coordinate constancy checks.

- **`ScalarMul.FixedBase.Coords.circuit`:** this is a helper for `coords_check`, not a
  source `meta.create_gate` by itself. It intentionally has no `GATE` name.

- **`GATE Running sum coordinates check` and `GATE Full-width fixed-base scalar mul`:**
  Clean currently represents some verifier-known table/interpolation values as ordinary
  row inputs. That is dangerous because it gives the prover control over values that are
  fixed by the configured fixed base. In idiomatic Clean, locally fixed constants should be
  Lean constants, and fixed-base/table parameters should be ordinary Lean arguments that
  the `FormalAssertion` depends on. This is not enough to reproduce Halo2 fixed-column
  layout, but it does preserve the contract that these values are fixed before proving.

- **`GATE Canonicity checks`:** Clean ports the arithmetic checks, but not the surrounding
  lookup/running-sum API or exact column/rotation layout for base-field fixed-base mul.

- **`GATE full round`, `GATE partial rounds`, and `GATE pad-and-add`:** Clean represents
  round constants as row values. These should not be witness inputs. Locally fixed
  constants should be Lean constants, and Poseidon parameter data such as round constants
  and MDS coefficients should be Lean parameters to the gate/formal assertion. The source
  uses fixed columns supplied by the Poseidon chip configuration; Lean parameters are the
  appropriate Clean-level contract even before exact fixed-column layout is modeled.

- **Poseidon permutation/link/hash wrappers:** `Permutation.InitialToFull`,
  `FullToFull`, `FullToPartial`, `PartialToPartial`, `PartialToFull`, `FullToOutput`,
  `FullRowsBlock`, `InitialFullBlock`, `FinalFullBlock`, `PartialPairBlock`,
  `PartialRows4Block`, `PartialRows8Block`, `Hash2`, and
  `Hash2PermutationBoundary` are not source `meta.create_gate` definitions. They should
  remain unnamed as `GATE`s unless replaced by an exact source API port.

- **`GATE Initial y_Q` and `GATE Sinsemilla gate`:** Clean exposes source-rotated values
  as row fields and does not encode the exact fixed/advice/rotation layout. Any generator
  table entries or domain constants used by these gates should be Lean constants or
  template parameters rather than witness-controlled row fields.

- **`Sinsemilla.InitWiring`, `Commit.Entry`, `ShortCommit.Entry`, `Merkle.Wiring`, and
  `Merkle.PathStep`:** these are wiring/partial-entry helpers, not direct source custom
  gates. They should not receive `GATE` names.

- **`GATE Decomposition check`:** Clean ports the Merkle decomposition arithmetic but does
  not encode the source copy constraints, fixed/advice roles, or hash-to-point child API.
  Fixed layer/domain constants should be Lean constants or template parameters, not row
  inputs.

- **NoteCommit and CommitIvk named gates:** Clean ports their arithmetic identities, but
  does not yet record the exact fixed/advice column roles or selector layout. Literal
  constants such as powers of two and field offsets should be Lean constants; if a gate is
  parameterized by verifier-known table/domain data, that data should be a Lean argument to
  the assertion rather than part of the witness row.

- **Action-level wiring wrappers:** the non-conformant `ActionWiring`,
  `ActionComputedWiring`, `ActionNoteCommitWiring`, `ActionMerkleWiring`, and
  `ActionAddressWiring` circuits were deleted. Rebuild action-level public-input,
  equality, Merkle, note-commitment, value-commitment, nullifier, spend-authority, and
  address-integrity wiring only inside a final source-conformant action entry circuit.

- **`Gadget.ValueCommitment.Entry`, `Gadget.Nullifier.Entry`,
  `Gadget.NullifierWithHash.Entry`, `Gadget.NullifierWithPoseidonBoundary.Entry`, and
  `Gadget.SpendAuth.Entry`:** these non-conformant wrappers were deleted. Their
  replacements must compute fixed-base products, Poseidon outputs, and complete additions
  through source-conformant child entry circuits instead of accepting those products as row
  inputs.

- **`NoteCommit.Wiring` and `CommitIvk.Wiring`:** these are not custom gates. They record
  message/canonicity wiring around custom gates. The non-conformant
  `NoteCommit.WiringWithCommit` and `CommitIvk.WiringWithShortCommit` wrappers were
  deleted; rebuild them only after the missing scalar-mul and Sinsemilla entry APIs exist.

- (known issue for reproducing VKs, fix not currently in scope) **All named gates:**
  current Clean rows do not distinguish advice cells, fixed cells, selector cells,
  equality-enabled columns, column identity, or rotations such as current/next/previous
  row queries. This is enough for arithmetic proof work, but not enough to reconstruct the
  Halo2 layout or pinned VK.
