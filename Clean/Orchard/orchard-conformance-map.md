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
- `Clean.Orchard.Ecc.ScalarMul.Mul.circuit`: `GATE LSB check`
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
- `Clean.Orchard.Ecc.ScalarMul.MulFixed.BaseFieldElem.circuit`:
  `GATE Canonicity checks`
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

- `Clean.Orchard.Gadget.ValueCommitOrchard.circuit`: `gadget.rs::value_commit_orchard`,
  the value-commitment entry circuit
  `cv = [v] ValueCommitV + [rcv] ValueCommitR`, composing the short and full-width
  fixed-base mul entry circuits and complete addition, with soundness and completeness
  proved
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

Full-width and signed short fixed-base mul are source-level entry circuits; the rest of
the scalar-mul coverage is row-level gate assertions.

- `NonIdentityPoint::mul` / `EccInstructions::mul`, implemented by
  `ecc/chip/mul.rs::Config::assign` (`CircuitVersion::AnchoredBase`), is modeled by
  `Clean.Orchard.Ecc.ScalarMul.Mul.Assign.circuit` — fully verified (soundness and
  completeness, no sorries). Its `Spec` is the semantic contract: for any nonzero curve
  point `B` matching the base coordinates, the output is `([alpha.val] B).coords`. The
  composition follows the source: `[2]base` by complete addition, `z_init = 0`, the
  `hi`/`lo` incomplete halves, the three complete bits, `process_lsb`, and
  `overflow_check`; the scalar bits are prover-side hints derived from
  `k = alpha + t_q`, as in the source. Two purely virtual subcircuit boundaries
  (`Assign.Decompose` for the decomposition region, `Assign.ProcessLsb` mirroring
  `mul.rs::Config::process_lsb`) factor the proofs without changing operations,
  witnesses, or cell order relative to the inlined source.
- Missing source-level entry circuit: `FixedPointBaseField::mul`, implemented by
  `ecc/chip/mul_fixed/base_field_elem.rs`: fixed-base multiplication by a base-field
  element, used by nullifier derivation.

The missing entry circuit must witness internal decomposition/addition/window values
and specify actual elliptic-curve scalar multiplication. Downstream Orchard gadgets must
not accept scalar-multiplication products as free inputs.

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

Missing source-level APIs:

- `SinsemillaInstructions::hash_to_point_with_private_init`
- `MerkleInstructions::hash_layer`
- `MerklePath::calculate_root`

### Orchard Entry APIs

`value_commit_orchard` is implemented (`Gadget.ValueCommitOrchard.circuit`). Missing
source-level APIs:

- `derive_nullifier`
- spend-authority key derivation in `Circuit::synthesize`
- address-integrity wiring in `Circuit::synthesize`
- `gadgets::note_commit`
- `gadgets::commit_ivk`
- full `Circuit::synthesize` action circuit

These must compose source-conformant child circuits. In particular:

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
