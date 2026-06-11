# Orchard Conformance Map

This file records the current implementation map and known gaps for `Clean/Orchard`
against Orchard 0.14.0 and `halo2_gadgets-0.5.0`. It is current-state guidance for agent
runs; the desired end state is specified in `orchard-clean-plan.md`.

Authoritative local source checkouts:

- `halo2_gadgets`, tag `halo2_gadgets-0.5.0`:
  `../audits/zcash-orchard/halo2-halo2_gadgets-0.5.0` (relative to the repo root) or
  `/root/code/halo2`, depending on the machine
- `orchard`, tag `0.14.0`: `../audits/zcash-orchard/orchard-0.14.0` or
  `/root/code/orchard`

## Source Map

### ECC

Source:

- `halo2_gadgets/src/ecc/chip/witness_point.rs`
- `halo2_gadgets/src/ecc/chip/add_incomplete.rs`
- `halo2_gadgets/src/ecc/chip/add.rs`

Current Clean coverage:

- `Clean.Orchard.Ecc.Defs`: shared Pallas field, point, and row-layout definitions
- `Clean.Orchard.Ecc.Theorems`: shared ECC lemmas actually used by current circuits
- `Clean.Orchard.Ecc.WitnessPoint.circuit`: `EccInstructions::witness_point`
- `Clean.Orchard.Ecc.WitnessPoint.Gate.circuit`: `GATE witness point`
- `Clean.Orchard.Ecc.WitnessNonIdentityPoint.circuit`: `EccInstructions::witness_point_non_id`
- `Clean.Orchard.Ecc.WitnessNonIdentityPoint.Gate.circuit`: `GATE witness non-identity point`
- `Clean.Orchard.Ecc.AddIncomplete.Gate.circuit`: `GATE incomplete addition`
- `Clean.Orchard.Ecc.AddIncomplete.circuit`: `EccInstructions::add_incomplete`
- `Clean.Orchard.Ecc.Add.Gate.circuit`: `GATE complete addition`
- `Clean.Orchard.Ecc.Add.circuit`: `EccInstructions::add`

### Utilities

Source:

- `halo2_gadgets/src/utilities/cond_swap.rs`
- `halo2_gadgets/src/utilities/decompose_running_sum.rs`
- `halo2_gadgets/src/utilities/lookup_range_check.rs`
- `orchard/src/circuit/gadget/add_chip.rs`

Current Clean coverage:

- `Clean.Orchard.Utilities.CondSwap.circuit`: entry-level conditional swap/mux over
  scalar field values
- `Clean.Orchard.Utilities.PointMux.circuit`: `mux_on_points`
- `Clean.Orchard.Utilities.NonIdentityPointMux.circuit`: `mux_on_non_identity_points`
- `Clean.Orchard.Utilities.AddChip.circuit`: field addition entry circuit
- `Clean.Orchard.Utilities.RunningSum.circuit`: `GATE range check`
- `Clean.Orchard.Utilities.LookupRangeCheck.circuit`: `GATE Short lookup bitshift`
- `Clean.Orchard.Utilities.LookupRangeCheck.shortRangeCircuit`: short range-check helper

### Scalar Multiplication

Source:

- `halo2_gadgets/src/ecc/chip/mul.rs`
- `halo2_gadgets/src/ecc/chip/mul/incomplete.rs`
- `halo2_gadgets/src/ecc/chip/mul/complete.rs`
- `halo2_gadgets/src/ecc/chip/mul/overflow.rs`
- `halo2_gadgets/src/ecc/chip/mul_fixed.rs`
- `halo2_gadgets/src/ecc/chip/mul_fixed/full_width.rs`
- `halo2_gadgets/src/ecc/chip/mul_fixed/base_field_elem.rs`
- `halo2_gadgets/src/ecc/chip/mul_fixed/short.rs`

Current Clean coverage:

- `Clean.Orchard.Ecc.ScalarMul.Defs`: shared scalar-mul gate helpers
- `Clean.Orchard.Ecc.ScalarMul.Mul.circuit`: `GATE LSB check`
- `Clean.Orchard.Ecc.ScalarMul.Mul.Complete.circuit`:
  `GATE Decompose scalar for complete bits of variable-base mul`
- `Clean.Orchard.Ecc.ScalarMul.Mul.Incomplete.Init.circuit`:
  `GATE q_mul_1 == 1 checks`
- `Clean.Orchard.Ecc.ScalarMul.Mul.Incomplete.MainLoop.circuit`:
  `GATE q_mul_2 == 1 checks`
- `Clean.Orchard.Ecc.ScalarMul.Mul.Incomplete.Loop.circuit`:
  `GATE q_mul_3 == 1 checks`
- `Clean.Orchard.Ecc.ScalarMul.Mul.Overflow.circuit`: `GATE overflow checks`
- `Clean.Orchard.Ecc.ScalarMul.MulFixed.Coords.circuit`: helper for `coords_check`,
  without a `GATE` name
- `Clean.Orchard.Ecc.ScalarMul.MulFixed.RunningSumCoords.circuit`:
  `GATE Running sum coordinates check`
- `Clean.Orchard.Ecc.ScalarMul.MulFixed.FullWidth.circuit`:
  `GATE Full-width fixed-base scalar mul`
- `Clean.Orchard.Ecc.ScalarMul.MulFixed.BaseFieldElem.circuit`:
  `GATE Canonicity checks`
- `Clean.Orchard.Ecc.ScalarMul.MulFixed.Short.circuit`:
  `GATE Short fixed-base mul gate`

### Poseidon

Source:

- `halo2_gadgets/src/poseidon/pow5.rs`
- `halo2_gadgets/src/poseidon.rs`

Current Clean coverage:

- `Clean.Orchard.Poseidon.Pow5` mirrors `poseidon/pow5.rs`.
- `Clean.Orchard.Poseidon.FullRound.circuit`: `GATE full round`
- `Clean.Orchard.Poseidon.PartialRounds.circuit`: `GATE partial rounds`
- `Clean.Orchard.Poseidon.PadAndAdd.circuit`: `GATE pad-and-add`
- `Clean.Orchard.Poseidon.Sponge` mirrors the `Sponge` /
  `PoseidonSpongeInstructions` part of `poseidon.rs` and currently contains only the
  source-shaped namespace stub.
- `Clean.Orchard.Poseidon.Hash` mirrors `poseidon.rs::Hash` and currently contains only
  the source-shaped namespace stub.

`FullRound` and `PartialRounds` already take fixed-column round constants and matrix
entries as Lean parameters. No source-level permutation or hash API is currently
implemented.

### Sinsemilla And Merkle

Source:

- `halo2_gadgets/src/sinsemilla/chip.rs`
- `halo2_gadgets/src/sinsemilla/chip/hash_to_point.rs`
- `halo2_gadgets/src/sinsemilla.rs`
- `halo2_gadgets/src/sinsemilla/merkle/chip.rs`
- `halo2_gadgets/src/sinsemilla/merkle.rs`

Current Clean coverage:

- `Clean.Orchard.Sinsemilla.InitialYQ.circuit`: `GATE Initial y_Q`
- `Clean.Orchard.Sinsemilla.Gate.circuit`: `GATE Sinsemilla gate`
- `Clean.Orchard.Sinsemilla.Merkle.circuit`: `GATE Decomposition check`

`InitialYQ` and `Gate` already take their fixed-column inputs as Lean parameters.

### Orchard Custom Gates And Actions

Source:

- `orchard/src/circuit.rs`
- `orchard/src/circuit/gadget.rs`
- `orchard/src/circuit/note_commit.rs`
- `orchard/src/circuit/commit_ivk.rs`

Current Clean coverage:

- `Clean.Orchard.ActionChecks.circuit`: `GATE Orchard circuit checks`
- `Clean.Orchard.NoteCommit.DecomposeB.circuit`:
  `GATE NoteCommit MessagePiece b`
- `Clean.Orchard.NoteCommit.DecomposeD.circuit`:
  `GATE NoteCommit MessagePiece d`
- `Clean.Orchard.NoteCommit.DecomposeE.circuit`:
  `GATE NoteCommit MessagePiece e`
- `Clean.Orchard.NoteCommit.DecomposeG.circuit`:
  `GATE NoteCommit MessagePiece g`
- `Clean.Orchard.NoteCommit.DecomposeH.circuit`:
  `GATE NoteCommit MessagePiece h`
- `Clean.Orchard.NoteCommit.GdCanonicity.circuit`: `GATE NoteCommit input g_d`
- `Clean.Orchard.NoteCommit.PkdCanonicity.circuit`: `GATE NoteCommit input pk_d`
- `Clean.Orchard.NoteCommit.ValueCanonicity.circuit`: `GATE NoteCommit input value`
- `Clean.Orchard.NoteCommit.RhoCanonicity.circuit`: `GATE NoteCommit input rho`
- `Clean.Orchard.NoteCommit.PsiCanonicity.circuit`: `GATE NoteCommit input psi`
- `Clean.Orchard.NoteCommit.YCanonicity.circuit`: `GATE y coordinate checks`
- `Clean.Orchard.CommitIvk.circuit`: `GATE CommitIvk canonicity check`

## Known Non-Conformances

### Naming And Gate Factoring

The plan says that when a Halo2 API has both a low-level gate and a synthesis-level entry
point, the gate should live in a `.Gate` namespace and the entry point should use the
source API name. Current code does not consistently follow that rule.

Current concrete cases:

- `Utilities.CondSwap.circuit` and `Utilities.AddChip.circuit` are entry-level circuits
  but do not yet compose separately factored named gate assertions:
  - `GATE a' = b * swap + a * (1-swap)`
  - `GATE Field element addition: c = a + b`

### Concrete Circuit Field

The plan requires Orchard circuits to use `Ecc.Fp` concretely. Several
modules still define helper functions and some assertions generically over
`{F : Type} [Field F]` or generic semiring-like typeclass sets. These should be
specialized or isolated so Orchard circuit packages themselves are Pallas-base circuits,
and field facts needed by specs are proved for that concrete field instead of assumed by
callers.

### Lookup And Range-Check Conformance

Clean has arithmetic stand-ins for some lookup-backed range checks:

- `GATE range check`
- `LookupRangeCheck.shortRangeCircuit`

Source-conformant repairs should use Clean `lookup` and explicit `Table` definitions
where Halo2 uses lookup tables. This is required before higher-level range-dependent
gadgets can be considered source-conformant.

### Scalar Multiplication Entry APIs

Current scalar-mul coverage is mostly row-level gate assertions. Missing source-level
entry circuits:

- `NonIdentityPoint::mul` / `EccInstructions::mul`, implemented by
  `ecc/chip/mul.rs::Config::assign`: variable-base scalar multiplication
  `[scalar] base`.
- `FixedPoint::mul`, implemented by `ecc/chip/mul_fixed/full_width.rs`: full-width
  fixed-base scalar multiplication `[scalar] B`.
- `FixedPointShort::mul`, implemented by `ecc/chip/mul_fixed/short.rs`: signed short
  fixed-base scalar multiplication used by `ValueCommitV`.
- `FixedPointBaseField::mul`, implemented by
  `ecc/chip/mul_fixed/base_field_elem.rs`: fixed-base multiplication by a base-field
  element, used by nullifier derivation.

These entry circuits must witness internal decomposition/addition/window values and
specify actual elliptic-curve scalar multiplication. Downstream Orchard gadgets must not
accept scalar-multiplication products as free inputs.

### Scalar Multiplication Gate Layout Gaps

The scalar-mul row assertions are source-shaped as separate gate modules, but still do
not fully match source row layout:

- `GATE q_mul_1 == 1 checks`, `GATE q_mul_2 == 1 checks`, and
  `GATE q_mul_3 == 1 checks` are source-named, but their Clean row structs are still
  contractual bundles rather than exact Halo2 advice-column/rotation layouts.
- `ScalarMul.MulFixed.Coords.circuit` intentionally remains an unbranded helper for
  `mul_fixed.rs::Config::coords_check`, which is not a source `meta.create_gate` by
  itself. It is used by `RunningSumCoords` and `FullWidth`.
- `GATE Canonicity checks` lacks the surrounding lookup/running-sum API and exact
  fixed/advice column and rotation layout for base-field fixed-base mul.

### Poseidon Entry APIs

The named custom gates are present, but the source-level APIs are not:

- `Pow5Chip::permute`
- `PoseidonSpongeInstructions::initial_state`
- `PoseidonSpongeInstructions::add_input`
- `Hash::init`
- `Hash::hash`

Do not reintroduce wrapper circuits that expose explicit permutation rows or hash
boundary values as caller inputs. The source APIs witness/copy cells internally and should
be ported with that surface.

### Sinsemilla And Merkle Entry APIs

Missing source-level APIs:

- `SinsemillaInstructions::hash_to_point`
- `SinsemillaInstructions::hash_to_point_with_private_init`
- `HashDomain::hash`
- `CommitDomain::blinding_factor`
- `CommitDomain::commit`
- `CommitDomain::short_commit`
- `MerkleInstructions::hash_layer`
- `MerklePath::calculate_root`

The current `Initial y_Q`, `Sinsemilla gate`, and Merkle decomposition assertions are
local gates only. Full repairs depend on lookup/range checks, complete addition,
fixed-base scalar multiplication, and source-shaped `hash_to_point` composition.

### Orchard Entry APIs

Missing source-level APIs:

- `value_commit_orchard`
- `derive_nullifier`
- spend-authority key derivation in `Circuit::synthesize`
- address-integrity wiring in `Circuit::synthesize`
- `gadgets::note_commit`
- `gadgets::commit_ivk`
- full `Circuit::synthesize` action circuit

These must compose source-conformant child circuits. In particular:

- `value_commit_orchard` is `[v] ValueCommitV + [rcv] ValueCommitR`.
- `derive_nullifier` is `ExtractP(cm + [poseidon_hash(nk, rho) + psi] NullifierK)`.
- Spend authority is `[alpha] SpendAuthG + ak_P`.
- Address integrity computes `ivk = CommitIvk(ak, nk, rivk)` and then `[ivk] g_d_old`.

### Gate Layout Metadata For VK Reconstruction

Current Clean rows generally do not distinguish advice cells, fixed cells, selector
cells, equality-enabled columns, column identity, or rotations such as current, next, and
previous row queries. This is enough for arithmetic proof work, but not enough to
reconstruct the Halo2 layout or pinned VK.

The intended direction is not to add selectors as circuit inputs. Selectors are modeled
by subcircuit calls. Fixed columns should remain Lean parameters to gate assertions.
Advice row structs should make source rotations explicit enough for later serialization
and layout reconstruction.
