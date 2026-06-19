# Orchard Conformance Map

Source → Clean coverage for `Clean/Orchard` against Orchard 0.14.0 and `halo2_gadgets-0.5.0`.
Implementations are assumed proven (soundness + completeness) unless noted; the "Known
Non-Conformances" section is the list of gaps and signature mismatches. The desired end
state is in `orchard-clean-plan.md`.

Authoritative local source checkouts:

- `halo2_gadgets`, tag `halo2_gadgets-0.5.0`:
  `../audits/zcash-orchard/halo2-halo2_gadgets-0.5.0` or `/root/code/halo2`
- `orchard`, tag `0.14.0`: `../audits/zcash-orchard/orchard-0.14.0` or `/root/code/orchard`

## Source Map

### ECC

Source: `halo2_gadgets/src/ecc/chip/{witness_point,add_incomplete,add}.rs`

- `Ecc.Defs`, `Ecc.Theorems`: shared definitions and lemmas
- `Ecc.WitnessPoint.circuit`: `EccInstructions::witness_point` (gate `WitnessPoint.Gate.circuit`)
- `Ecc.WitnessNonIdentityPoint.circuit`: `EccInstructions::witness_point_non_id`
  (gate `WitnessNonIdentityPoint.Gate.circuit`)
- `Ecc.AddIncomplete.circuit`: `EccInstructions::add_incomplete` (gate `AddIncomplete.Gate.circuit`)
- `Ecc.Add.circuit`: `EccInstructions::add` (gate `Add.Gate.circuit`)

### Utilities

Source: `halo2_gadgets/src/utilities/{cond_swap,decompose_running_sum,lookup_range_check}.rs`,
`orchard/src/circuit/gadget/add_chip.rs`

- `Utilities.CondSwap.Swap.circuit`: `CondSwapInstructions::swap` (gate `CondSwap.Gate.circuit`)
- `Utilities.CondSwap.circuit`: entry-level conditional swap/mux over field values
- `Utilities.PointMux.circuit`: `mux_on_points`
- `Utilities.NonIdentityPointMux.circuit`: `mux_on_non_identity_points`
- `Utilities.AddChip.circuit`: field addition `c = a + b` (gate `AddChip.Gate.circuit`)
- `Utilities.RunningSum.circuit`: `GATE range check`
- `Utilities.LookupRangeCheck.circuit`: `GATE Short lookup bitshift`
- `Utilities.LookupRangeCheck.shortRangeCircuit` / `taggedShortRangeCircuit`: short / tagged
  4–5-bit range-check helpers
- `Utilities.LookupRangeCheck.WitnessShort.circuit` / `taggedCircuit`:
  `RangeConstrained::witness_short` (generic / tagged)
- `Utilities.LookupRangeCheck.CopyCheck.circuit`: lookup-backed running-sum copy/decomposition
- `Utilities.LookupRangeCheck.CopyCheck.Telescoped.circuit`: `z_0`/`z_last` projection wrapper
- `Utilities.LookupRangeCheck.CopyCheck.Decomposed.circuit`: 25-word decomposition wrapper
  exposing `z_1`/`z_13`

### Scalar Multiplication

Source: `halo2_gadgets/src/ecc/chip/mul*.rs`, `mul_fixed*.rs`

- `Ecc.ScalarMul.Defs`: shared gate helpers
- `Ecc.ScalarMul.Mul.Gate.circuit`: `GATE LSB check`
- `Ecc.ScalarMul.Mul.Complete.circuit`: `GATE Decompose scalar for complete bits`
- `Ecc.ScalarMul.Mul.Incomplete.{Init,MainLoop,Loop}.circuit`: `GATE q_mul_{1,2,3} == 1 checks`
- `Ecc.ScalarMul.Mul.Incomplete.DoubleAndAdd.circuit`:
  `incomplete.rs::Config::double_and_add` (`CircuitVersion::AnchoredBase`)
- `Ecc.ScalarMul.Mul.Overflow.circuit`: `GATE overflow checks`
- `Ecc.ScalarMul.MulFixed.Coords.circuit`: `coords_check` helper (no source `GATE` name)
- `Ecc.ScalarMul.MulFixed.RunningSumCoords.circuit`: `GATE Running sum coordinates check`
- `Ecc.ScalarMul.MulFixed.FixedBase`: value-level fixed-base model (window tables) parameterizing
  the fixed-base entries
- `Ecc.ScalarMul.MulFixed.FullWidth.circuit`: `FixedPoint::mul` (gate `FullWidth.Gate.circuit`)
- `Ecc.ScalarMul.MulFixed.BaseFieldElem.circuit`: `FixedPointBaseField::mul`
  (gate `BaseFieldElem.Gate.circuit`; running-sum decomposition `RunningSumMul.circuit`)
- `Ecc.ScalarMul.MulFixed.Short.circuit`: `FixedPointShort::mul` (gate `Short.Gate.circuit`;
  value-level `Short.FixedBase` model)

### Poseidon

Source: `halo2_gadgets/src/poseidon/pow5.rs`, `poseidon.rs`

- Modules `Poseidon.{Pow5,Sponge,Hash}`; Pallas constants in `Poseidon.Pow5.Constants`
- Gates: `Poseidon.FullRound.Gate.circuit`, `Poseidon.PartialRounds.Gate.circuit`,
  `Poseidon.PadAndAdd.circuit`
- `Poseidon.Permute.mainP128ConcreteCircuit`: concrete P128 `Pow5Chip::permute`
- `Poseidon.Sponge.InitialState.circuit`: `Pow5Chip::initial_state`
- `Poseidon.Sponge.AddInput.circuit`: `Pow5Chip::add_input`
- `Poseidon.Sponge.GetOutput.circuit`: `PoseidonSpongeInstructions::get_output`
- `Poseidon.Hash.Init.circuit`: `Hash::init`
- `Poseidon.Hash.HashPaddedBlock.concreteCircuit`: one-padded-block P128 `Hash::hash`
- `Poseidon.Hash.ConstantLength.circuit`: rate-2 `Hash::hash` for `ConstantLength<L>`, `L > 0`

### Sinsemilla And Merkle

Source: `halo2_gadgets/src/sinsemilla{.rs,/chip.rs,/chip/hash_to_point.rs,/merkle.rs,/merkle/chip.rs}`

- `Sinsemilla.generatorTable`: `chip/generator_table.rs` lookup table
- `Sinsemilla.HashPiece.circuit`: `hash_to_point.rs::hash_piece`
- `Sinsemilla.Entry.circuit` (with `HashPiece`/`Chain`): `hash_all_pieces` + public-`Q` init;
  lands at `Specs.Sinsemilla.hashToPoint`
- `Sinsemilla.InitialYQ.circuit`: `GATE Initial y_Q`
- `Sinsemilla.Gate.circuit`: `GATE Sinsemilla gate`
- `Sinsemilla.HashDomain.circuit`: `HashDomain::hash`
- `Sinsemilla.CommitDomain.circuit`: `CommitDomain::commit`
- `Sinsemilla.CommitDomain.WithZs.circuit`: `CommitDomain::commit` exposing per-piece running
  sums (used by `note_commit`/`commit_ivk`)
- `Sinsemilla.CommitDomain.Short.circuit`: `CommitDomain::short_commit`
- `Sinsemilla.CommitDomain.blindingFactor`: `CommitDomain::blinding_factor` (`[r] R`)
- `Sinsemilla.Merkle.circuit`: `GATE Decomposition check`
- `Sinsemilla.Merkle.HashLayer.circuit`: `MerkleInstructions::hash_layer`
- `Sinsemilla.Merkle.CalculateRoot.circuit`: `MerklePath::calculate_root` (`MERKLE_DEPTH = 32`)

### Orchard Custom Gates And Actions

Source: `orchard/src/circuit.rs`, `circuit/gadget.rs`, `circuit/note_commit.rs`, `circuit/commit_ivk.rs`

- `Action.ValueCommit.circuit`: `gadget.rs::value_commit_orchard`
- `Action.Gate.circuit`: `GATE Orchard circuit checks`
- `Action.NoteCommit.{DecomposeB,D,E,G,H}.Gate.circuit`: `GATE NoteCommit MessagePiece {b,d,e,g,h}`
- `Action.NoteCommit.{Gd,Pkd,Value,Rho,Psi}Canonicity.Gate.circuit`:
  `GATE NoteCommit input {g_d,pk_d,value,rho,psi}`
- `Action.NoteCommit.YCanonicity.Gate.circuit`: `GATE y coordinate checks`
- `Action.NoteCommit.AssignMessagePieces.circuit`: message-cell assignment
- `Action.NoteCommit.MessagePieceChecks.circuit`: decomposition-gate block for the five pieces
- `Action.NoteCommit.Commit.circuit`: `CommitDomain::commit` specialized to note-commit piece
  sizes, over `CommitDomain.WithZs` (exposes hash running sums for canonicity)
- `Action.NoteCommit.circuit`: `gadgets::note_commit` entry
- `Action.CommitIvk.Gate.circuit`: `GATE CommitIvk canonicity check`
- `Action.CommitIvk.circuit`: `gadgets::commit_ivk` entry
- `Action.AddressIntegrity.circuit`: diversified-address integrity block
  (`ivk = CommitIvk(ak, nk, rivk)`, `[ivk] g_d_old`, constrained to `pk_d_old`)
- Entry circuits `Gadget.ValueCommitOrchard.circuit`, `Gadget.DeriveNullifier.circuit`,
  `SpendAuthority.circuit`
- `Orchard.Action.circuit` in `Clean/Orchard/Action.lean`: `Circuit::synthesize`, the
  top-level action circuit (gadget blocks + public-instance wiring + `q_orchard` gate)

## Known Non-Conformances

### Concrete Circuit Field

Some circuit packages and helpers are still generic over `{F : Type} [Field F]` rather than
the concrete Pallas base field `Fp` — e.g. `Utilities.RunningSum.circuit` and
`Utilities.LookupRangeCheck.circuit` (the short-lookup-bitshift gate), plus shared helper
lemmas in several modules. These should be specialized so Orchard circuit packages are
concrete `Fp` circuits, with field facts established for that field rather than assumed by
callers.

### Scalar Multiplication Output Signatures

`FixedPoint::mul` returns `(EccPoint, EccScalarFixed)` and `FixedPointShort::mul` returns
`(EccPoint, EccScalarFixedShort)` — the second component is the witnessed scalar decomposition.
`MulFixed.FullWidth.circuit` and `MulFixed.Short.circuit` return only `Point`, dropping it.
Fix by returning `(Point, scalar-decomposition)`. (The variable-base `Mul.circuit` similarly
returns only `Point` where `EccInstructions::mul` returns `(EccPoint, ScalarVar)`, but there
`ScalarVar` merely re-wraps the input `alpha`, so it is benign.)

### Sinsemilla Output Signature: Base APIs Point-Only

`CommitDomain.WithZs.circuit` exposes each piece's full running sum
(`Output.zs : HVec (Chain.zLengths ns)`), and `note_commit`/`commit_ivk` use it. The base
APIs still mismatch the source: Halo2's `hash_to_point`/`commit` return `(Point, zs)`
(per-piece running sums `zs[i] = [z_0, ..., z_{w_i}]`), but `HashPiece`/`Chain`/`Entry` expose
only the `z_1` cells and `HashDomain.circuit`/`CommitDomain.circuit` return only the point.
Exact conformance would thread full `zs` (an `HVec`) through the recursive tower. Also missing:
`SinsemillaInstructions::hash_to_point_with_private_init`.

### Gate Layout Metadata For VK Reconstruction

Clean rows generally do not distinguish advice/fixed/selector cells, equality-enabled columns,
column identity, or rotations — e.g. the `GATE q_mul_{1,2,3} == 1 checks` row structs are
contractual bundles, not exact column/rotation layouts. This suffices for arithmetic reasoning
but not for reconstructing the Halo2 layout or pinned VK. Intended direction: selectors stay
modeled by subcircuit calls (not inputs), fixed columns stay Lean parameters, and advice row
structs make source rotations explicit for later serialization.
