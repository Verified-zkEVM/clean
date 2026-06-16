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
  `incomplete.rs::Config::double_and_add` (`CircuitVersion::AnchoredBase`), fully
  proven (soundness and completeness). Witness cells are created in the source's
  assignment order: the three starting copies (`z`, `x_a`, `y_a`), then per loop row
  `z, x_p, y_p, λ1, λ2, x_a(next)` exactly as `assign_advice`/`copy_advice` are
  called, then the final `y_a`.
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
  multiplication entry circuit `[scalar] B`, with soundness and completeness proved
- `Clean.Orchard.Ecc.ScalarMul.MulFixed.BaseFieldElem.Gate.circuit`:
  `GATE Canonicity checks`
- `Clean.Orchard.Ecc.ScalarMul.MulFixed.BaseFieldElem.RunningSumMul.circuit`: the strict
  85-window running-sum decomposition, shared fixed-base windowed multiplication, and
  final complete addition producing `[alpha] B` (`GeneralFormalCircuit.WithHint`,
  soundness and completeness proved); exposes the running-sum cells `z_43`, `z_44`, `z_84`
  that the canonicity check copies in
- `Clean.Orchard.Ecc.ScalarMul.MulFixed.BaseFieldElem.circuit`:
  `FixedPointBaseField::mul` (`mul_fixed/base_field_elem.rs::Config::assign`), the
  base-field-element fixed-base scalar multiplication entry circuit `[alpha] B`, with
  soundness and completeness proved; composes `RunningSumMul` with the canonicity tail
  (13-window lookup range check on `alpha_0 + 2^130 - t_p` and the `GATE Canonicity
  checks` gate)
- `Clean.Orchard.Ecc.ScalarMul.MulFixed.Short.Gate.circuit`:
  `GATE Short fixed-base mul gate`
- `Clean.Orchard.Ecc.ScalarMul.MulFixed.Short.FixedBase`: value-level model of a short
  fixed base point with its 22-window tables, parameterizing the short entry circuit
- `Clean.Orchard.Ecc.ScalarMul.MulFixed.Short.circuit`: `FixedPointShort::mul`
  (`mul_fixed/short.rs::Config::assign`), the signed short fixed-base scalar
  multiplication entry circuit `[±magnitude] B`, with soundness and completeness proved;
  composes the strict running-sum decomposition (`GATE range check` and
  `GATE Running sum coordinates check` per window), incomplete and complete addition,
  and the final conditional negation gate

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
  fixed-base mul entry circuits and complete addition, with soundness and completeness
  proved
- `Clean.Orchard.Action.Gate.circuit`: `GATE Orchard circuit checks`
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
- `Clean.Orchard.Action.CommitIvk.Gate.circuit`: `GATE CommitIvk canonicity check`
- `Clean.Orchard.Action.CommitIvk.circuit`: `gadgets::commit_ivk` entry (circuit + specs +
  elaboration done; `soundness`/`completeness` are `sorry`, pending the shared message-piece
  canonicity-encoding bridge also outstanding for `note_commit`)

## Known Non-Conformances

### Concrete Circuit Field

The plan requires Orchard circuits to use the concrete Orchard `Fp` circuit field.
Several modules still define helper functions and some assertions generically over
`{F : Type} [Field F]` or generic semiring-like typeclass sets. These should be
specialized or isolated so Orchard circuit packages themselves are Pallas-base circuits,
and field facts needed by specs are proved for that concrete field instead of assumed by
callers.

### Lookup And Range-Check Conformance

Clean now models the short lookup-backed range-check paths with Clean `lookup`
operations:

- `LookupRangeCheck.shortRangeCircuit`: looks up `word` in `table_idx`, witnesses and
  looks up `word * 2^(K - num_bits)`, and composes `GATE Short lookup bitshift`.
- `LookupRangeCheck.taggedShortRangeCircuit`: models
  `LookupRangeCheck4_5BConfig::short_range_check` for `num_bits = 4` and `5` with a
  two-column tagged table `(table_idx, table_range_check_tag)`.
- `LookupRangeCheck.WitnessShort.circuit`: witnesses the prover-only bitrange subset
  and calls the generic short range-check path.
- `LookupRangeCheck.WitnessShort.taggedCircuit`: witnesses the prover-only bitrange
  subset and calls the optimized tagged 4/5-bit path.

Note that `GATE range check` (`decompose_running_sum.rs`) is _not_ lookup-backed in
halo2: it is the polynomial constraint `range_check(word, 8)` and the Clean port is
source-conformant.

### Scalar Multiplication Entry APIs

Full-width and signed short fixed-base mul, base-field-element fixed-base mul, and
variable-base mul are all source-level entry circuits, each fully verified (soundness and
completeness, no sorries).

- `NonIdentityPoint::mul` / `EccInstructions::mul`, implemented by
  `ecc/chip/mul.rs::Config::assign` (`CircuitVersion::AnchoredBase`), is modeled by
  `Clean.Orchard.Ecc.ScalarMul.Mul.circuit` — fully verified (soundness and
  completeness, no sorries). Its `Spec` is the semantic contract: for any nonzero curve
  point `B` matching the base coordinates, the output is `([alpha.val] B).coords`. The
  composition follows the source: `[2]base` by complete addition, `z_init = 0`, the
  `hi`/`lo` incomplete halves, the three complete bits, `process_lsb`, and
  `overflow_check`; the scalar bits are prover-side hints derived from
  `k = alpha + t_q`, as in the source. Two purely virtual subcircuit boundaries
  (`Assign.Decompose` for the decomposition region, `Assign.ProcessLsb` mirroring
  `mul.rs::Config::process_lsb`) factor the proofs without changing operations,
  witnesses, or cell order relative to the inlined source.
- `FixedPointBaseField::mul`, implemented by
  `ecc/chip/mul_fixed/base_field_elem.rs::Config::assign`: fixed-base multiplication by a
  base-field element (used by nullifier derivation), is modeled by
  `Clean.Orchard.Ecc.ScalarMul.MulFixed.BaseFieldElem.circuit` — fully verified
  (soundness and completeness, no sorries). Its `Spec` is the semantic contract: the
  output is `([alpha.val] B).coords`. It composes the strict 85-window running-sum
  decomposition + shared windowed multiplication + complete addition (`RunningSumMul`)
  with the canonicity tail — a 13-window lookup range check on `alpha_0 + 2^130 - t_p` and
  the `GATE Canonicity checks` gate — following `base_field_elem.rs::Config::assign`. The
  output is just `Point`, matching the source `FixedPointBaseField::mul` (which returns a
  single `EccPoint`), so it carries none of the output-signature gap noted below.

NON-CONFORMANT output signature (fixed-base mul entries): Halo2's `FixedPoint::mul`
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
  (`GeneralFormalCircuit.WithHint`, proven sound and complete for any word count):
  running-sum decomposition with per-word generator lookups (including the derived
  `y_p = Y_A/2 - λ₁(x_A - x_P)` lookup expression), in-piece `q_s2 = 1` gates, and the
  accumulator `y` threaded as a prover hint, matching the source cell layout. The
  value-level spec layer (`Specs.Sinsemilla`: incomplete `⸭`, `⊥`-propagating chain) is
  the semantic anchor.

- `hash_to_point.rs::hash_all_pieces` + public-`Q` initialization:
  `Sinsemilla.Entry.circuit` (`GeneralFormalCircuit.WithHint`, proven sound and
  complete for any nonempty list of per-piece word counts). Pieces are chained by a
  recursive bundled tower (`Sinsemilla.Chain.circuit`): each level emits the gate
  completing its own piece's last double-and-add step against the next level's
  exposed first row (`q_s2 = 0` between pieces, `q_s2 = 2` for the final gate whose
  dummy row carries the witnessed final `y_a`), and the entry adds the constant
  `x_Q` cell plus the `q_sinsemilla4` (`Initial y_Q`) gate. The `Spec` lands at
  `Specs.Sinsemilla.hashToPoint` from the protocol-spec value layer.

- `sinsemilla.rs` domain APIs (`Clean/Orchard/Sinsemilla/Domain.lean`, all proven
  sound and complete):
  - `HashDomain::hash`: `Sinsemilla.HashDomain.circuit` (entry + `x`-extraction).
  - `CommitDomain::commit`: `Sinsemilla.CommitDomain.circuit`
    (`M.hash_to_point(msg) + [r] R` via the full-width fixed-base mul and complete
    addition, mirroring `value_commit_orchard`'s composition).
  - `CommitDomain::short_commit`: `Sinsemilla.CommitDomain.Short.circuit`.
  - `CommitDomain::blinding_factor`: `Sinsemilla.CommitDomain.blindingFactor`
    (the bare `[r] R`, an alias of `MulFixed.FullWidth.circuit`).

- `MerkleInstructions::hash_layer`: `Sinsemilla.Merkle.HashLayer.circuit`
  (`Clean/Orchard/Sinsemilla/Merkle.lean`, proven sound and complete): witnesses the
  three message pieces `a`/`b`/`c` and the 5-bit sub-pieces `b_1`/`b_2`
  (range-checked), hashes via the `hash_to_point` entry, and ties the pieces to
  `(l, left, right)` with the `q_decompose` gate reading the hash's own `z_1`
  running-sum cells. Spec: the output is the `x`-coordinate of
  `SinsemillaHashToPoint(Q, merkleChunks l lv rv)` for 255-bit encodings `lv`, `rv`
  of the child nodes (non-canonical encodings allowed, as in the source).

- `MerklePath::calculate_root`: `Sinsemilla.Merkle.CalculateRoot.circuit`
  (`Clean/Orchard/Sinsemilla/Merkle.lean`, proven sound and complete): the
  `MERKLE_DEPTH = 32` authentication-path fold, a `Circuit.foldl` over 32
  `Sinsemilla.Merkle.Layer` sub-circuits (each composing `CondSwap.Swap.circuit` with
  `Merkle.HashLayer.circuit`). `Spec` is the value-level 32-layer `MerkleCRH` fold from
  the leaf (`MerkleRoot`); `ProverSpec` is the honest root (`honestNode`). The
  kernel-heavy 32-fold proof relies on a `bridge` lemma so the non-opaque hash output
  is never reduced (see `lean-perf-debugging` notes); the bundle passes `elaborated`
  explicitly.

Missing source-level APIs:

- `SinsemillaInstructions::hash_to_point_with_private_init`

### Hash Output Signature: Running Sums (NON-CONFORMANT)

The Sinsemilla hash output type does **not** match Halo2, violating the input/output
signature requirement (plan "Goal" and "Synthesize" §: the I/O schema of a Clean circuit
must precisely match the Halo2 method).

Halo2 returns the per-piece running sums as part of the output:

```rust
// halo2_gadgets/src/sinsemilla.rs
fn hash_to_point(...) -> Result<(NonIdentityPoint, Vec<Vec<AssignedCell<…>>>), Error>
fn commit(...)        -> Result<(Point,            Vec<Vec<AssignedCell<…>>>), Error>
// zs[i] = [z_0, …, z_{w_i}] is piece i's running sum
// (hash_to_point.rs::hash_piece builds zs; hash_all_pieces collects zs_sum;
//  note_commit.rs reads zs[0][13], zs[3][1], …)
```

Current Clean state (under-models the output):

- `HashPiece` computes the full running sum `zs : Vector field (w + 1)` internally
  (`HashToPoint.lean`, in `main`) but its `Output` exposes only `z1 = zs[1]` — a one-off
  added by the z1-refactor for the single cell Merkle's decomposition gate needed.
- `Chain.Output` / `Entry.Output` carry only `z1s` (the per-piece `z_1`), not the full
  `zs`.
- `CommitDomain.circuit` / `HashDomain.circuit` return only the point, dropping `zs`.

Resolution: `CommitDomain.WithZs.circuit` now exposes each piece's full running sum `zs`
(the `Output.zs : HVec (Chain.zLengths ns)`), unblocking the canonicity-checking entries
that copy specific running-sum cells out of the hash region. Both consumers are now
implemented on top of it — `gadgets::note_commit` (`Action.NoteCommit`, reads `zs[i][13]`,
`zs[i][1]`) and `gadgets::commit_ivk` (`Action.CommitIvk`, reads `zs[0][13]`, `zs[2][13]`).
The legacy `z1`-only `Output` exposure below is retained for the Merkle decomposition gate.

Fix (faithful, supersedes the z1-only exposure): expose each piece's full running sum
`zs` through `HashPiece.Output` (so `z1` becomes `zs[1]`), thread per-piece `zs` through
the recursive `Chain`/`Entry` tower (a flat `Vector (Vector …) …` does not type — pieces
have different `w`), and return `(Point, zs)` from `CommitDomain.circuit` to match
`commit`. Re-prove the four hash circuits accordingly.

### Orchard Entry APIs

`value_commit_orchard` is implemented (`Gadget.ValueCommitOrchard.circuit`),
`derive_nullifier` is implemented (`Gadget.DeriveNullifier.circuit`, soundness and
completeness proved), and the `Circuit::synthesize` spend-authority block is implemented
(`SpendAuthority.circuit`, soundness and completeness proved).

`gadgets::note_commit` (`Action.NoteCommit`) and `gadgets::commit_ivk`
(`Action.CommitIvk.circuit`) are both implemented as circuits with semantic specs and
elaboration; their entry-level `soundness`/`completeness` proofs are still `sorry`, blocked
on the shared message-piece canonicity-encoding bridge (relating the witnessed Sinsemilla
pieces to the canonical `*Chunks` of the input scalars via the decomposition/canonicity
gates). Missing source-level APIs:

- address-integrity wiring in `Circuit::synthesize`
- entry proofs for `gadgets::note_commit` and `gadgets::commit_ivk`
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
previous row queries. This is enough for arithmetic proof work, but not enough to
reconstruct the Halo2 layout or pinned VK.

The intended direction is not to add selectors as circuit inputs. Selectors are modeled
by subcircuit calls. Fixed columns should remain Lean parameters to gate assertions.
Advice row structs should make source rotations explicit enough for later serialization
and layout reconstruction.
