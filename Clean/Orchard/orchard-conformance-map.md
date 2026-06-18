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

- `Clean.Orchard.Utilities.CondSwap.Gate.circuit`:
  `GATE a' = b ⋅ swap + a ⋅ (1-swap)`
- `Clean.Orchard.Utilities.CondSwap.Swap.circuit`: `CondSwapInstructions::swap`,
  the CondSwap entry API used by Orchard Merkle path calculation
- `Clean.Orchard.Utilities.CondSwap.circuit`: entry-level conditional swap/mux over
  scalar field values, implemented by composing the factored CondSwap gate
- `Clean.Orchard.Utilities.PointMux.circuit`: `mux_on_points`
- `Clean.Orchard.Utilities.NonIdentityPointMux.circuit`: `mux_on_non_identity_points`
- `Clean.Orchard.Utilities.AddChip.Gate.circuit`:
  `GATE Field element addition: c = a + b`
- `Clean.Orchard.Utilities.AddChip.circuit`: field addition entry circuit
- `Clean.Orchard.Utilities.RunningSum.circuit`: `GATE range check`
- `Clean.Orchard.Utilities.LookupRangeCheck.circuit`: `GATE Short lookup bitshift`
- `Clean.Orchard.Utilities.LookupRangeCheck.shortRangeCircuit`: short range-check helper
- `Clean.Orchard.Utilities.LookupRangeCheck.taggedShortRangeCircuit`: optimized 4/5-bit
  tagged short range-check helper
- `Clean.Orchard.Utilities.LookupRangeCheck.WitnessShort.circuit`:
  `RangeConstrained::witness_short` / `LookupRangeCheck::witness_short_check`
- `Clean.Orchard.Utilities.LookupRangeCheck.WitnessShort.taggedCircuit`:
  4/5-bit tagged `RangeConstrained::witness_short` path
- `Clean.Orchard.Utilities.LookupRangeCheck.CopyCheck.circuit`: lookup-backed running-sum
  copy/decomposition helper
- `Clean.Orchard.Utilities.LookupRangeCheck.CopyCheck.Telescoped.circuit`: projected
  `z_0`/`z_last` wrapper exposing the telescoped decomposition used by canonicity gates
- `Clean.Orchard.Utilities.LookupRangeCheck.CopyCheck.Decomposed.circuit`: full
  25-word decomposition wrapper exposing exact `z_1`/`z_13` reads for y-canonicity

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
- `Clean.Orchard.Ecc.ScalarMul.Mul.Gate.circuit`: `GATE LSB check`
- `Clean.Orchard.Ecc.ScalarMul.Mul.Complete.circuit`:
  `GATE Decompose scalar for complete bits of variable-base mul`
- `Clean.Orchard.Ecc.ScalarMul.Mul.Incomplete.Init.circuit`:
  `GATE q_mul_1 == 1 checks`
- `Clean.Orchard.Ecc.ScalarMul.Mul.Incomplete.MainLoop.circuit`:
  `GATE q_mul_2 == 1 checks`
- `Clean.Orchard.Ecc.ScalarMul.Mul.Incomplete.Loop.circuit`:
  `GATE q_mul_3 == 1 checks`
- `Clean.Orchard.Ecc.ScalarMul.Mul.Incomplete.DoubleAndAdd.circuit`:
  `incomplete.rs::Config::double_and_add` (`CircuitVersion::AnchoredBase`). Witness
  cells are created in the source's assignment order: the three starting copies (`z`,
  `x_a`, `y_a`), then per loop row `z, x_p, y_p, λ1, λ2, x_a(next)` exactly as
  `assign_advice`/`copy_advice` are called, then the final `y_a`.
- `Clean.Orchard.Ecc.ScalarMul.Mul.Overflow.circuit`: `GATE overflow checks`
- `Clean.Orchard.Ecc.ScalarMul.MulFixed.Coords.circuit`: helper for `coords_check`,
  without a `GATE` name
- `Clean.Orchard.Ecc.ScalarMul.MulFixed.RunningSumCoords.circuit`:
  `GATE Running sum coordinates check`
- `Clean.Orchard.Ecc.ScalarMul.MulFixed.FixedBase`: value-level model of a fixed base
  point with its precomputed window tables (`z`/`u` values, Lagrange coefficients),
  parameterizing the fixed-base entry circuits
- `Clean.Orchard.Ecc.ScalarMul.MulFixed.FullWidth.Gate.circuit`:
  `GATE Full-width fixed-base scalar mul`
- `Clean.Orchard.Ecc.ScalarMul.MulFixed.FullWidth.circuit`: `FixedPoint::mul`
  (`mul_fixed/full_width.rs::Config::assign`), the full-width fixed-base scalar
  multiplication entry circuit `[scalar] B`
- `Clean.Orchard.Ecc.ScalarMul.MulFixed.BaseFieldElem.Gate.circuit`:
  `GATE Canonicity checks`
- `Clean.Orchard.Ecc.ScalarMul.MulFixed.BaseFieldElem.RunningSumMul.circuit`: the strict
  85-window running-sum decomposition, shared fixed-base windowed multiplication, and
  final complete addition producing `[alpha] B`; exposes the running-sum cells `z_43`,
  `z_44`, `z_84` that the canonicity check copies in
- `Clean.Orchard.Ecc.ScalarMul.MulFixed.BaseFieldElem.circuit`:
  `FixedPointBaseField::mul` (`mul_fixed/base_field_elem.rs::Config::assign`), the
  base-field-element fixed-base scalar multiplication entry circuit `[alpha] B`, composing
  `RunningSumMul` with the canonicity tail (13-window lookup range check on
  `alpha_0 + 2^130 - t_p` and the `GATE Canonicity checks` gate)
- `Clean.Orchard.Ecc.ScalarMul.MulFixed.Short.Gate.circuit`:
  `GATE Short fixed-base mul gate`
- `Clean.Orchard.Ecc.ScalarMul.MulFixed.Short.FixedBase`: value-level model of a short
  fixed base point with its 22-window tables, parameterizing the short entry circuit
- `Clean.Orchard.Ecc.ScalarMul.MulFixed.Short.circuit`: `FixedPointShort::mul`
  (`mul_fixed/short.rs::Config::assign`), the signed short fixed-base scalar
  multiplication entry circuit `[±magnitude] B`, composing the strict running-sum
  decomposition (`GATE range check` and `GATE Running sum coordinates check` per window),
  incomplete and complete addition, and the final conditional negation gate

### Poseidon

Source:

- `halo2_gadgets/src/poseidon/pow5.rs`
- `halo2_gadgets/src/poseidon.rs`

Current Clean coverage:

- Source-shaped Poseidon modules live in `Clean.Orchard.Poseidon.Pow5`,
  `Clean.Orchard.Poseidon.Sponge`, and `Clean.Orchard.Poseidon.Hash`; concrete Pallas
  constants from `halo2_poseidon/src/fp.rs` live in
  `Clean.Orchard.Poseidon.Pow5.Constants`.
- Custom gates are packaged:
  - `Clean.Orchard.Poseidon.FullRound.Gate.circuit`: `GATE full round`
  - `Clean.Orchard.Poseidon.PartialRounds.Gate.circuit`: `GATE partial rounds`
  - `Clean.Orchard.Poseidon.PadAndAdd.circuit`: `GATE pad-and-add`
- Source entry-point circuits are packaged:
  - `Clean.Orchard.Poseidon.Permute.mainP128ConcreteCircuit`: concrete P128
    `Pow5Chip::permute`
  - `Clean.Orchard.Poseidon.Sponge.InitialState.circuit`:
    `Pow5Chip::initial_state`
  - `Clean.Orchard.Poseidon.Sponge.AddInput.circuit`: `Pow5Chip::add_input`
  - `Clean.Orchard.Poseidon.Sponge.GetOutput.circuit`:
    `PoseidonSpongeInstructions::get_output`
  - `Clean.Orchard.Poseidon.Hash.Init.circuit`: `Hash::init`
  - `Clean.Orchard.Poseidon.Hash.HashPaddedBlock.concreteCircuit`: one-padded-block
    P128 `Hash::hash`
  - `Clean.Orchard.Poseidon.Hash.ConstantLength.circuit`: generic rate-2
    `Hash::hash` for `ConstantLength<L>` with `L > 0`

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

- `Clean.Orchard.Action.ValueCommit.circuit`: `gadget.rs::value_commit_orchard`,
  the value-commitment entry circuit
  `cv = [v] ValueCommitV + [rcv] ValueCommitR`, composing the short and full-width
  fixed-base mul entry circuits and complete addition
- `Clean.Orchard.Action.Gate.circuit`: `GATE Orchard circuit checks`
- `Clean.Orchard.Action.NoteCommit.DecomposeB.Gate.circuit`:
  `GATE NoteCommit MessagePiece b`
- `Clean.Orchard.Action.NoteCommit.DecomposeD.Gate.circuit`:
  `GATE NoteCommit MessagePiece d`
- `Clean.Orchard.Action.NoteCommit.DecomposeE.Gate.circuit`:
  `GATE NoteCommit MessagePiece e`
- `Clean.Orchard.Action.NoteCommit.DecomposeG.Gate.circuit`:
  `GATE NoteCommit MessagePiece g`
- `Clean.Orchard.Action.NoteCommit.DecomposeH.Gate.circuit`:
  `GATE NoteCommit MessagePiece h`
- `Clean.Orchard.Action.NoteCommit.GdCanonicity.Gate.circuit`: `GATE NoteCommit input g_d`
- `Clean.Orchard.Action.NoteCommit.PkdCanonicity.Gate.circuit`: `GATE NoteCommit input pk_d`
- `Clean.Orchard.Action.NoteCommit.ValueCanonicity.Gate.circuit`: `GATE NoteCommit input value`
- `Clean.Orchard.Action.NoteCommit.RhoCanonicity.Gate.circuit`: `GATE NoteCommit input rho`
- `Clean.Orchard.Action.NoteCommit.PsiCanonicity.Gate.circuit`: `GATE NoteCommit input psi`
- `Clean.Orchard.Action.NoteCommit.YCanonicity.Gate.circuit`: `GATE y coordinate checks`
- `Clean.Orchard.Action.NoteCommit.AssignMessagePieces.circuit`: source-shaped assignment of
  the note-commit message cells; the consumer-facing spec exports range facts, while the
  prover spec records honest bit-slice facts
- `Clean.Orchard.Action.NoteCommit.MessagePieceChecks.circuit`: source decomposition-gate
  block for the five decomposed message pieces
- `Clean.Orchard.Action.NoteCommit.Commit.circuit`: Sinsemilla
  `CommitDomain::commit` block specialized to note-commit message-piece sizes, using
  `CommitDomain.WithZs.circuit` so the subsequent canonicity checks can read the hash
  running sums
- `Clean.Orchard.Action.NoteCommit.circuit`: `gadgets::note_commit` entry, implemented
  with semantic specs; entry completeness remains pending
- `Clean.Orchard.Action.CommitIvk.Gate.circuit`: `GATE CommitIvk canonicity check`
- `Clean.Orchard.Action.CommitIvk.circuit`: `gadgets::commit_ivk` entry, factored into
  `Commit` (witnessing + `WithZs` hash) and `Canonicity` (CopyCheck decompositions + gate)
  subcircuits

## Known Non-Conformances

### Concrete Circuit Field

The plan requires Orchard circuits to use the concrete Orchard `Fp` circuit field.
Several modules still define helper functions and some assertions generically over
`{F : Type} [Field F]` or generic semiring-like typeclass sets. These should be
specialized or isolated so Orchard circuit packages themselves are Pallas-base circuits,
and field facts needed by specs are established for that concrete field instead of
assumed by callers.

### Scalar Multiplication Output Signatures

Halo2's `FixedPoint::mul`
(`mul_fixed/full_width.rs::Config::assign`) returns `(EccPoint, EccScalarFixed)` and
`FixedPointShort::mul` (`mul_fixed/short.rs::Config::assign`) returns
`(EccPoint, EccScalarFixedShort)` — the second component is the witnessed scalar
*decomposition* (the assigned window / running-sum cells). Clean's
`MulFixed.FullWidth.circuit` and `MulFixed.Short.circuit` return only `Point`, dropping
that scalar. This is the same class of gap as the hash running sums (Output omits a value
Halo2 returns); fix by returning `(Point, scalar-decomposition)` to match. (The variable-
base `Mul.circuit` similarly returns only `Point` where `EccInstructions::mul`
returns `(EccPoint, ScalarVar)`, but there `ScalarVar = BaseFieldElem(alpha)` merely
re-wraps the already-present input `alpha`, so it is benign and not tracked as a gap.)

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

### Sinsemilla And Merkle Entry APIs

Implemented building blocks:

- `chip/generator_table.rs` lookup table: `Sinsemilla.generatorTable` (the `2^K`-entry
  `(idx, x, y)` table over abstract `Specs.Sinsemilla.Generators`).
- `hash_to_point.rs::hash_piece`: `Sinsemilla.HashPiece.circuit`
  (`GeneralFormalCircuit.WithHint`): running-sum decomposition with per-word generator
  lookups (including the derived `y_p = Y_A/2 - λ₁(x_A - x_P)` lookup expression),
  in-piece `q_s2 = 1` gates, and the accumulator `y` threaded as a prover hint, matching
  the source cell layout. The value-level spec layer (`Specs.Sinsemilla`: incomplete `⸭`,
  `⊥`-propagating chain) is the semantic anchor.

- `hash_to_point.rs::hash_all_pieces` + public-`Q` initialization:
  `Sinsemilla.Entry.circuit` (`GeneralFormalCircuit.WithHint`). Pieces are chained by
  a recursive bundled tower (`Sinsemilla.Chain.circuit`): each level emits the gate
  completing its own piece's last double-and-add step against the next level's exposed
  first row (`q_s2 = 0` between pieces, `q_s2 = 2` for the final gate whose dummy row
  carries the witnessed final `y_a`), and the entry adds the constant `x_Q` cell plus
  the `q_sinsemilla4` (`Initial y_Q`) gate. The `Spec` lands at
  `Specs.Sinsemilla.hashToPoint` from the protocol-spec value layer.

- `sinsemilla.rs` domain APIs (`Clean/Orchard/Sinsemilla/Domain.lean`):
  - `HashDomain::hash`: `Sinsemilla.HashDomain.circuit` (entry + `x`-extraction).
  - `CommitDomain::commit`: `Sinsemilla.CommitDomain.circuit`
    (`M.hash_to_point(msg) + [r] R` via the full-width fixed-base mul and complete
    addition, mirroring `value_commit_orchard`'s composition).
  - `CommitDomain::commit` with running sums: `Sinsemilla.CommitDomain.WithZs.circuit`,
    used by `Action.CommitIvk` and `Action.NoteCommit` when source callers copy specific
    Sinsemilla running-sum cells into later gates.
  - `CommitDomain::short_commit`: `Sinsemilla.CommitDomain.Short.circuit`.
  - `CommitDomain::blinding_factor`: `Sinsemilla.CommitDomain.blindingFactor`
    (the bare `[r] R`, an alias of `MulFixed.FullWidth.circuit`).

- `MerkleInstructions::hash_layer`: `Sinsemilla.Merkle.HashLayer.circuit`
  (`Clean/Orchard/Sinsemilla/Merkle.lean`): witnesses the three message pieces
  `a`/`b`/`c` and the 5-bit sub-pieces `b_1`/`b_2` (range-checked), hashes via the
  `hash_to_point` entry, and ties the pieces to `(l, left, right)` with the
  `q_decompose` gate reading the hash's own `z_1` running-sum cells. Spec: the output is
  the `x`-coordinate of
  `SinsemillaHashToPoint(Q, merkleChunks l lv rv)` for 255-bit encodings `lv`, `rv`
  of the child nodes (non-canonical encodings allowed, as in the source).

- `MerklePath::calculate_root`: `Sinsemilla.Merkle.CalculateRoot.circuit`
  (`Clean/Orchard/Sinsemilla/Merkle.lean`): the `MERKLE_DEPTH = 32` authentication-path
  fold, a `Circuit.foldl` over 32 `Sinsemilla.Merkle.Layer` sub-circuits (each composing
  `CondSwap.Swap.circuit` with `Merkle.HashLayer.circuit`). `Spec` is the value-level
  32-layer `MerkleCRH` fold from the leaf (`MerkleRoot`); `ProverSpec` is the honest root
  (`honestNode`). The 32-fold bundle passes `elaborated` explicitly.

Missing source-level APIs:

- `SinsemillaInstructions::hash_to_point_with_private_init`

### Sinsemilla Output Signature: Base APIs Still Point-Only

This gap is resolved for the canonicity-checking action circuits:
`CommitDomain.WithZs.circuit` exposes each piece's full running sum
`Output.zs : HVec (Chain.zLengths ns)`, and both consumers that copy hash-region running
sums now use it:

- `gadgets::note_commit` (`Action.NoteCommit`) reads `zs[i][13]` / `zs[i][1]` for the
  note-commit canonicity and decomposition checks.
- `gadgets::commit_ivk` (`Action.CommitIvk`) reads `zs[0][13]` / `zs[2][13]` for its
  canonicity check.

The remaining source-signature gap is in the base Sinsemilla APIs. Halo2 returns the
per-piece running sums as part of the output:

```rust
// halo2_gadgets/src/sinsemilla.rs
fn hash_to_point(...) -> Result<(NonIdentityPoint, Vec<Vec<AssignedCell<...>>>), Error>
fn commit(...)        -> Result<(Point,            Vec<Vec<AssignedCell<...>>>), Error>
// zs[i] = [z_0, ..., z_{w_i}] is piece i's running sum
```

`HashPiece` computes the full running sum internally, but the base
`HashPiece`/`Chain`/`Entry` outputs expose only the `z_1` cells used by Merkle, and
`HashDomain.circuit` / `CommitDomain.circuit` return only the point. If those base APIs
are brought into exact source-signature conformance, thread full `zs` through the
recursive tower (an `HVec` shape, not a flat vector) and return `(Point, zs)` from the
source-shaped domain circuits. Until then, `WithZs` is the conformant path for action
circuits that need running-sum cells.

### Orchard Entry APIs

`value_commit_orchard` is implemented (`Gadget.ValueCommitOrchard.circuit`),
`derive_nullifier` is implemented (`Gadget.DeriveNullifier.circuit`), and the
`Circuit::synthesize` spend-authority block is implemented (`SpendAuthority.circuit`).

`gadgets::commit_ivk` (`Action.CommitIvk.circuit`) uses the message-piece bridge
`pieceChunks_eq_commitIvkChunks_of_indexed_piece_values` /
`honestChunks_eq_commitIvkChunks` and the generic shared running-sum theory in
`Specs.Sinsemilla` (`sum_suffix_div`, `running_sum_telescope`) and `HashToPoint`
(`piece_recombine`, `pieceChunks_honestChunks`, public `chain_eq_sum`).

`gadgets::note_commit` (`Action.NoteCommit.circuit`) is implemented with semantic specs
and source-shaped subcircuits for assignment, Sinsemilla commit with `zs`, message-piece
checks, y-canonicity, and coordinate canonicity. Entry completeness remains pending.

Missing source-level APIs:

- address-integrity wiring in `Circuit::synthesize`
- completeness proof for `gadgets::note_commit`
- full `Circuit::synthesize` action circuit

These must compose source-conformant child circuits. In particular:

- `derive_nullifier` (done) is `ExtractP(cm + [poseidon_hash(nk, rho) + psi] NullifierK)`,
  parameterized by the `NullifierK` fixed base.
- Spend authority (done) is `[alpha] SpendAuthG + ak_P`, parameterized by the
  `SpendAuthG` fixed base. The enclosing action circuit still needs to constrain the
  resulting coordinates to `RK_X` and `RK_Y`.
- Address integrity computes `ivk = CommitIvk(ak, nk, rivk)` and then `[ivk] g_d_old`.

### Gate Layout Metadata For VK Reconstruction

Current Clean rows generally do not distinguish advice cells, fixed cells, selector
cells, equality-enabled columns, column identity, or rotations such as current, next, and
previous row queries. This is enough for arithmetic reasoning, but not enough to reconstruct
the Halo2 layout or pinned VK.

The intended direction is not to add selectors as circuit inputs. Selectors are modeled
by subcircuit calls. Fixed columns should remain Lean parameters to gate assertions.
Advice row structs should make source rotations explicit enough for later serialization
and layout reconstruction.
