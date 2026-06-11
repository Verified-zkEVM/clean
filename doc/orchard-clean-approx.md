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
     `PointMux.circuit` ports `mux_on_points` by composing the scalar field mux on
     `x` and `y` and returning the selected Pallas point.
     `NonIdentityPointMux.circuit` ports `mux_on_non_identity_points` by adding the
     non-identity point assertion for the selected output.
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
     `Orchard.Utilities.LookupRangeCheck.circuit`. The optimized 4- and 5-bit short
     range-check cases from `LookupRangeCheck4_5BConfig::short_range_check` are modeled
     as `Orchard.Utilities.LookupRangeCheck.shortRangeCircuit`.
5. Fixed-base and variable-base scalar multiplication:
   `halo2_gadgets/src/ecc/chip/mul*.rs`
   - Depends on ECC addition, conditional selection/swap, running sums, range checks, and
     fixed-base lookup tables.
   - Status: variable-base `LSB check`, variable-base incomplete-mul init/loop
     checks, variable-base complete-bit scalar decomposition, overflow checks,
     fixed-base coordinate checks, full-width fixed-base window checks, and the short
     fixed-base final sign gate are ported as
     `Orchard.ScalarMul.VarBaseLSB.circuit`,
     `Orchard.ScalarMul.VarBaseIncomplete.Init.circuit`,
     `Orchard.ScalarMul.VarBaseIncomplete.Loop.circuit`,
     `Orchard.ScalarMul.VarBaseIncomplete.MainLoop.circuit`,
     `Orchard.ScalarMul.VarBaseCompleteBit.circuit`,
     `Orchard.ScalarMul.VarBaseOverflow.circuit`,
     `Orchard.ScalarMul.FixedBase.Coords.circuit`,
     `Orchard.ScalarMul.FixedBase.RunningSumCoords.circuit`,
     `Orchard.ScalarMul.FixedBase.FullWidth.circuit`,
     `Orchard.ScalarMul.FixedBase.BaseFieldCanonicity.circuit`, and
     `Orchard.ScalarMul.FixedShort.circuit`. The standalone signed-point helper
     `mul_fixed/short.rs::assign_scalar_sign` is ported as the Pallas-specific
     `Orchard.ScalarMul.FixedShort.SignEntry.circuit`.
   - Semantic-spec gap: these are still row-level gate assertions, not composed scalar
     multiplication circuits. The higher Orchard gadgets need wrappers whose input/output
     surface contains the scalar, base point, and product point together, so their specs can
     state relations such as `product = [scalar] base`. In particular,
     `value_commit_orchard`, `derive_nullifier`, spend authority, and address integrity
     must not claim scalar-multiplication semantics merely from explicit product
     coordinates; those product coordinates need to come from scalar-mul child circuits.
6. Poseidon:
   `halo2_gadgets/src/poseidon/pow5.rs`
   - Depends on fixed round constants and MDS matrices supplied by the Poseidon spec.
   - Status: Orchard's width-3, rate-2 Pow5 custom gates `full round`,
     `partial rounds`, and `pad-and-add` are ported as
     `Orchard.Poseidon.FullRound.circuit`,
     `Orchard.Poseidon.PartialRounds.circuit`, and
     `Orchard.Poseidon.PadAndAdd.circuit`. Fixed-column constants are explicit row
     values in this approximation. The `ConstantLength<2>` hash wiring used by
     Orchard nullifiers, from initial state through absorb and squeezed state word 0,
     is ported as `Orchard.Poseidon.Hash2.circuit`. The `P128Pow5T3` permutation row
     schedule is represented by reusable endpoint-copy assertions
     `Orchard.Poseidon.Permutation.InitialToFull.circuit`,
     `FullToFull.circuit`, `FullToPartial.circuit`, `PartialToPartial.circuit`,
     `PartialToFull.circuit`, and `FullToOutput.circuit`; the hash-to-permutation
     endpoint copy wiring is ported as
     `Orchard.Poseidon.Hash2PermutationBoundary.circuit`.
7. Sinsemilla:
   `halo2_gadgets/src/sinsemilla/chip.rs`,
   `halo2_gadgets/src/sinsemilla/chip/hash_to_point.rs`,
   `halo2_gadgets/src/sinsemilla/merkle*.rs`
   - Depends on generator-table lookup, range checks, ECC addition, and conditional swap.
   - Status: `Initial y_Q` and `Sinsemilla gate` arithmetic constraints from
     `chip.rs` are ported as `Orchard.Sinsemilla.InitialYQ.circuit` and
     `Orchard.Sinsemilla.Gate.circuit`. The public/private `hash_to_point`
     initialization copy wiring around `Initial y_Q` is ported as
     `Orchard.Sinsemilla.InitWiring.circuit`. `CommitDomain::commit` and
     `CommitDomain::short_commit` output wiring are ported as
     `Orchard.Sinsemilla.Commit.circuit` and `Orchard.Sinsemilla.ShortCommit.circuit`.
     Pallas-specific wrappers `Orchard.Sinsemilla.Commit.Entry.circuit` and
     `Orchard.Sinsemilla.ShortCommit.Entry.circuit` use
     `Orchard.Ecc.CompleteAdd.Entry.circuit` for the final commitment addition and
     extraction over explicit hash/blinding product points.
     The MerkleCRH decomposition gate from
     `merkle/chip.rs` is ported as `Orchard.Sinsemilla.Merkle.circuit`; the
     fixed three-piece `MerkleInstructions::hash_layer` assignment and extracted hash
     wiring is ported as `Orchard.Sinsemilla.Merkle.Wiring.circuit`. One layer of
     `MerklePath::calculate_root`, including the position-bit conditional swap through
     `Orchard.Utilities.CondSwap.circuit` and `hash_layer` transition, is ported as
     `Orchard.Sinsemilla.Merkle.PathStep.circuit` with a conditional-selection spec.
8. Orchard custom gates and composition:
   `orchard/src/circuit.rs`,
   `orchard/src/circuit/commit_ivk.rs`,
   `orchard/src/circuit/note_commit.rs`,
   `orchard/src/circuit/gadget.rs`,
   `orchard/src/circuit/gadget/add_chip.rs`
   - Depends on Sinsemilla, ECC fixed-base/variable-base multiplication, and Orchard-specific
     decomposition/canonicity gates.
   - Status: `gadget/add_chip.rs` is ported as `Orchard.Utilities.AddChip.circuit`.
     The `gadget.rs` source-level wiring for `value_commit_orchard` and
     `derive_nullifier` is ported as `Orchard.Gadget.ValueCommitment.circuit`
     and `Orchard.Gadget.Nullifier.circuit`; Pallas-specific wrappers
     `Orchard.Gadget.ValueCommitment.Entry.circuit` and
     `Orchard.Gadget.Nullifier.Entry.circuit` now use
     `Orchard.Ecc.CompleteAdd.Entry.circuit` for their final additions over explicit
     fixed-base product points. The `derive_nullifier` edge
     `hash = PoseidonHash(nk, rho)` is connected to the nullifier wiring in
     `Orchard.Gadget.NullifierWithHash.circuit`; Pallas-specific wrappers
     `Orchard.Gadget.NullifierWithHash.Entry.circuit` and
     `Orchard.Gadget.NullifierWithPoseidonBoundary.Entry.circuit` compose the
     two-input Poseidon hash or hash/permutation boundary with
     `Orchard.Gadget.Nullifier.Entry.circuit`. The `circuit.rs` spend-authority wiring
     `rk = [alpha] SpendAuthG + ak_P` is ported as `Orchard.Gadget.SpendAuth.circuit`,
     with `Orchard.Gadget.SpendAuth.Entry.circuit` providing the Pallas complete-add
     entry wrapper over the explicit `[alpha] SpendAuthG` product.
     The four `Orchard circuit checks` constraints from `circuit.rs` are ported as
     `Orchard.ActionChecks.circuit`; the surrounding source-level action wiring from
     `Circuit::synthesize` is ported as `Orchard.ActionWiring.circuit`. The selected
     computed action outputs `cv_net`, `nf_old`, and `rk` are connected from
     `Orchard.Gadget.ValueCommitment.circuit`, `Orchard.Gadget.Nullifier.circuit`,
     and `Orchard.Gadget.SpendAuth.circuit` into the action row by
     `Orchard.ActionComputedWiring.circuit`; the Pallas-specific
     `Orchard.ActionComputedWiring.Entry.circuit` composes the corresponding entry
     wrappers for value commitment, nullifier-with-Poseidon-boundary, and spend
     authority. The final Merkle path-step output is
     connected to the action `root` consumed by the Orchard checks in
     `Orchard.ActionMerkleWiring.circuit`.
     `note_commit.rs` gates `NoteCommit MessagePiece b`,
     `d`, `e`, `g`, `h`, `NoteCommit input g_d`, `NoteCommit input pk_d`,
     `NoteCommit input rho`, `NoteCommit input psi`, `NoteCommit input value`, and
     `y coordinate checks` are ported as
     `Orchard.NoteCommit.DecomposeB.circuit`, `Orchard.NoteCommit.DecomposeD.circuit`,
     `Orchard.NoteCommit.DecomposeE.circuit`, `Orchard.NoteCommit.DecomposeG.circuit`,
     `Orchard.NoteCommit.DecomposeH.circuit`,
     `Orchard.NoteCommit.GdCanonicity.circuit`,
     `Orchard.NoteCommit.PkdCanonicity.circuit`,
     `Orchard.NoteCommit.RhoCanonicity.circuit`,
     `Orchard.NoteCommit.PsiCanonicity.circuit`, and
     `Orchard.NoteCommit.ValueCanonicity.circuit`, plus
     `Orchard.NoteCommit.YCanonicity.circuit`. The source-level
     `gadgets::note_commit` assignment and copy wiring is ported as
     `Orchard.NoteCommit.Wiring.circuit`; its explicit computed commitment output is
     connected to `Orchard.Sinsemilla.Commit.Entry.circuit` by
     `Orchard.NoteCommit.WiringWithCommit.circuit`, whose Orchard-level spec records the
     fixed-base blinding relation `[rcm] NoteCommitR`. The old
     `derived_cm_old = cm_old` action edge and new `cmx = ExtractP(cm_new)` public edge
     are connected to `Orchard.ActionWiring.circuit` by
     `Orchard.ActionNoteCommitWiring.circuit`, which composes the two
     `WiringWithCommit` children.
     `commit_ivk.rs` gate
     `CommitIvk canonicity check` is ported as `Orchard.CommitIvk.circuit`; the
     source-level `gadgets::commit_ivk` gate assignment and returned `ivk` wiring is
     ported as `Orchard.CommitIvk.Wiring.circuit`, and its explicit computed `ivk`
     output is connected to `Orchard.Sinsemilla.ShortCommit.Entry.circuit` by
     `Orchard.CommitIvk.WiringWithShortCommit.circuit`, whose Orchard-level spec records
     the fixed-base blinding relation `[rivk] CommitIvkR`. The action-level
     address-integrity copy edges from `ak` into `commit_ivk`, from `ivk` into the
     variable-base scalar input, and from the explicit `[ivk] g_d_old` result into
     `derived_pk_d_old` are recorded by `Orchard.ActionAddressWiring.circuit`, which
     composes `Orchard.Gadget.SpendAuth.Entry.circuit` and
     `Orchard.CommitIvk.WiringWithShortCommit.circuit`.

## Entry-point API audit against Halo2/Orchard

The source-map above distinguishes custom-gate rows from the public chip/gadget APIs.
The next bottom-up repairs should close the gaps where Clean currently has only the row
assertion but the Rust source exposes a higher-level entry point that witnesses auxiliary
values and returns a clean result.

| Rust source API | Rust semantics | Current Clean equivalent | Status |
| --- | --- | --- | --- |
| `EccInstructions::add` in `halo2_gadgets/src/ecc/chip.rs`, implemented by `add::Config::assign_region` in `ecc/chip/add.rs` | Complete affine addition. Inputs are two `EccPoint`s, auxiliaries `lambda`, `alpha`, `beta`, `gamma`, `delta` and the output point are witnessed internally, and the API returns `P + Q`, including identity and inverse cases. | `Orchard.Ecc.CompleteAdd.Entry.circuit` over `PallasBaseField`; row assertion remains `Orchard.Ecc.CompleteAdd.circuit` | Present. The entry circuit witnesses the output point and auxiliary row values, composes the complete-add row assertion internally, and specifies CompElliptic short-Weierstrass addition over Pallas. |
| `EccInstructions::add_incomplete`, implemented by `add_incomplete::Config::assign_region` | Incomplete non-identity addition. Inputs are non-identity points with exceptional cases rejected; output is witnessed and returned. | `Orchard.Ecc.IncompleteAdd.circuit` | Present as a `FormalCircuit` with input/output point surface and semantic short-Weierstrass addition spec. |
| `NonIdentityPoint::mul` / `EccInstructions::mul`, implemented by `ecc/chip/mul.rs::Config::assign` | Variable-base scalar multiplication `[scalar] base`, including scalar decomposition, complete and incomplete additions, LSB correction, and overflow check. | Row assertions in `Orchard.ScalarMul.VarBase*` plus copy edges in `Orchard.ActionAddressWiring` | Missing entry-point circuit. Clean does not yet have a composed variable-base scalar-mul circuit whose surface contains scalar, base, and product with spec `product = [scalar] base`. |
| `FixedPoint::mul`, implemented by `ecc/chip/mul_fixed/full_width.rs` | Full-width fixed-base scalar multiplication `[scalar] B`. Used by Orchard for `ValueCommitR`, `SpendAuthG`, Sinsemilla blinding factors, note commitments, and `CommitIvk`. | Row assertions in `Orchard.ScalarMul.FixedBase.*`; higher gadgets accept product coordinates | Missing entry-point circuit. Clean currently does not connect a scalar and fixed-base identifier to the returned product. |
| `FixedPointShort::mul`, implemented by `ecc/chip/mul_fixed/short.rs` | Signed short fixed-base scalar multiplication `[sign * magnitude] B`, including magnitude decomposition and final conditional negation. Used by `ValueCommitV`. | `Orchard.ScalarMul.FixedShort.circuit` plus other row assertions | Missing entry-point circuit. The final-row sign semantics are present, but not the composed short fixed-base multiplication API. |
| `mul_fixed/short.rs::Config::assign_scalar_sign` | Uses the short fixed-base sign gate by itself to return either an input point or its negation, with `sign ∈ {1, -1}`. | `Orchard.ScalarMul.FixedShort.SignEntry.circuit` | Present. The wrapper composes the bundled final-row gate and exposes the semantic signed-point relation over Pallas coordinates. |
| `FixedPointBaseField::mul`, implemented by `ecc/chip/mul_fixed/base_field_elem.rs` | Fixed-base scalar multiplication by a base-field element. Used by `derive_nullifier` for `[poseidon_hash(nk, rho) + psi] NullifierK`. | Row assertions in `Orchard.ScalarMul.FixedBase.*`; `Orchard.Gadget.Nullifier` accepts `productX/productY` | Missing entry-point circuit. Clean does not yet prove the nullifier product is the scalar multiplication result. |

Consequences for Orchard gadgets:

- `value_commit_orchard` in `orchard/src/circuit/gadget.rs` is
  `[v] ValueCommitV + [rcv] ValueCommitR`. `Orchard.Gadget.ValueCommitment.Entry.circuit`
  now uses the complete-add entry circuit for the final addition over explicit product
  points, but the fixed-base products themselves still need scalar-mul entry circuits.
- `derive_nullifier` in `orchard/src/circuit/gadget.rs` is
  `ExtractP(cm + [poseidon_hash(nk, rho) + psi] NullifierK)`.
  `Orchard.Gadget.Nullifier.Entry.circuit` now models the scalar field addition,
  final complete-add entry relation, and extraction edge, but not the fixed-base scalar
  multiplication. `Orchard.Gadget.NullifierWithHash.Entry.circuit` and
  `Orchard.Gadget.NullifierWithPoseidonBoundary.Entry.circuit` compose that entry wrapper
  with the existing Poseidon hash wiring.
- Spend authority in `orchard/src/circuit.rs` is
  `[alpha] SpendAuthG + ak_P`. `Orchard.Gadget.SpendAuth.Entry.circuit` now models the
  final complete-add entry relation over an explicit `[alpha] SpendAuthG` product, but
  not the fixed-base scalar multiplication.
- Address integrity in `orchard/src/circuit.rs` computes
  `ivk = CommitIvk(ak, nk, rivk)` and then `[ivk] g_d_old`.
  `Orchard.ActionAddressWiring` now composes the spend-authority entry wrapper and the
  `CommitIvk` short-commit wrapper, so its Orchard-level spec can state the
  `[rivk] CommitIvkR` and `[alpha] SpendAuthG` fixed-base relations alongside the
  variable-base relation for `[ivk] g_d_old`. It still does not compose a variable-base
  scalar-multiplication entry circuit for `[ivk] g_d_old`.

Complete-add modelling note:

- The Rust complete-add row is not intended to accept arbitrary field pairs. The public
  `EccInstructions::add` API receives `EccPoint`s, whose coordinates are expected to come
  from witness-point assertions, constants, scalar multiplication outputs, or previous ECC
  outputs.
- The row assignment branches on `x = 0` as the identity case. That is only a semantic group
  operation when the curve model knows that no non-identity Pallas point has `x = 0`.
  CompElliptic proves this as `Pallas.no_onCurve_x_zero` from `5` being a quadratic
  non-residue in the Pallas base field; the relevant Pasta field and curve facts are now
  vendored under `Clean.Orchard.Specs.Elliptic`.
- Therefore the Clean entry point assumes or proves valid point encodings for both inputs,
  composes the complete-add row internally, and specifies CompElliptic short-Weierstrass
  addition. Downstream gadgets should use `CompleteAdd.Entry.circuit` when they need the
  API-level addition relation, not the row-level `CompleteAdd.circuit` alone.

## Sinsemilla and Orchard wrapper conformance audit

The same custom-gate versus entry-point split appears in the Sinsemilla and Orchard
wrappers. These gaps are downstream of ECC complete addition and fixed-base scalar
multiplication, so they should be repaired after the ECC/scalar-mul entry-point circuits
exist.

| Rust source API | Rust semantics | Current Clean equivalent | Status |
| --- | --- | --- | --- |
| `SinsemillaInstructions::hash_to_point` / `hash_to_point_with_private_init`, implemented in `halo2_gadgets/src/sinsemilla/chip/hash_to_point.rs` | Initializes the accumulator from public/private `Q`, loops over all message pieces, performs generator-table lookups/range checks and merged double-and-add rows, assigns final `y_A`, rejects identity output, and returns a non-identity point plus running sums. | `Orchard.Sinsemilla.InitialYQ`, `InitWiring`, `Gate`, and explicit `computedHash`/point fields in later wrappers | Missing entry-point circuit. Clean has the local init/gate assertions, but no composed `hash_to_point` circuit whose surface is `(Q, message) -> (point, running sums)`. |
| `HashDomain::hash` in `halo2_gadgets/src/sinsemilla.rs` | Calls `hash_to_point` and extracts the x-coordinate. | `Orchard.Sinsemilla.Merkle.Wiring` with explicit `computedHash` | Missing entry-point circuit. Clean records the extraction/copy edge but does not compute the hash point from the message. |
| `CommitDomain::blinding_factor` and `CommitDomain::commit` in `halo2_gadgets/src/sinsemilla.rs` | Computes `[r] R`, computes `M = hash_to_point(message)`, then returns `M + [r] R` and running sums. | `Orchard.Sinsemilla.Commit.Entry.circuit` over explicit hash/blinding product points; row assertion remains `Commit.circuit` | Partial entry wrapper. The final addition now uses the complete-add entry relation, but Clean still does not compose fixed-base scalar multiplication or `hash_to_point`. |
| `CommitDomain::short_commit` in `halo2_gadgets/src/sinsemilla.rs` | Calls `commit`, then returns `ExtractP(commitment)`. | `Orchard.Sinsemilla.ShortCommit.Entry.circuit` over explicit hash/blinding product points | Partial entry wrapper. Clean composes the partial commit entry wrapper and extraction wiring, but the commit input still starts after hash/blinding products are explicit. |
| `MerkleInstructions::hash_layer` in `halo2_gadgets/src/sinsemilla/merkle/chip.rs` | Builds three Sinsemilla message pieces from `(layer, left, right)`, calls `hash_to_point`, extracts x, and wires decomposition/running-sum cells. | `Orchard.Sinsemilla.Merkle.circuit` and `Merkle.Wiring.circuit` | Partial wiring only. Clean ports the decomposition gate and final `computedHash = hash` edge, but the hash result is explicit rather than produced by a composed `hash_to_point` circuit. |
| `MerklePath::calculate_root` in `halo2_gadgets/src/sinsemilla/merkle.rs` | Iterates over all path layers, conditionally swaps `(node, sibling)`, calls `hash_layer`, and returns the final root. | `Orchard.Sinsemilla.Merkle.PathStep.circuit` and `Orchard.ActionMerkleWiring.circuit` | One-step wiring only. Clean models a single conditional swap plus explicit `hash_layer` row; it does not provide the full iterated path entry point. |
| `gadgets::note_commit` in `orchard/src/circuit/note_commit.rs` | Builds eight message pieces `a..h`, performs point-y and field canonicity checks using running-sum outputs from `CommitDomain::commit`, calls `CommitDomain::commit`, and returns the commitment point. | `Orchard.NoteCommit.Wiring.circuit` and `WiringWithCommit.circuit`; `Orchard.ActionNoteCommitWiring.circuit` composes two `WiringWithCommit` children | Partial entry wrapper. Clean composes the custom decomposition/canonicity assertions, uses `Sinsemilla.Commit.Entry.circuit` for the final addition/extraction over explicit hash and blinding product points, and records `[rcm] NoteCommitR` in `OrchardSpec`; it still does not prove the hash point comes from a full `hash_to_point` entry circuit or compose a real fixed-base scalar-mul circuit for the blinding product. |
| `gadgets::commit_ivk` in `orchard/src/circuit/commit_ivk.rs` | Builds four message pieces from `(ak, nk)`, calls `CommitDomain::short_commit`, uses returned running sums for canonicity, and returns `ivk`. | `Orchard.CommitIvk.Wiring.circuit` and `WiringWithShortCommit.circuit`; `Orchard.ActionAddressWiring.circuit` composes `WiringWithShortCommit` | Partial entry wrapper. Clean composes the canonicity gate, uses `Sinsemilla.ShortCommit.Entry.circuit` for the final short-commit extraction over explicit hash and blinding product points, and records `[rivk] CommitIvkR` in `OrchardSpec`; it still does not prove the hash point comes from a full `hash_to_point` entry circuit or compose a real fixed-base scalar-mul circuit for the blinding product. |

Immediate bottom-up implication:

- Fully repairing `Sinsemilla.Commit`, `ShortCommit`, `NoteCommit.WiringWithCommit`, and
  `CommitIvk.WiringWithShortCommit` semantically still depends on adding real fixed-base
  scalar-multiplication and `hash_to_point` entry-point circuits. The current wrappers
  already use the complete-add entry relation for the final addition and expose the
  relevant Orchard fixed-base blinding relations in their Orchard-level specs.
- Repairing Merkle path semantics additionally needs a composed `hash_to_point`/`hash_layer`
  entry point and then an iterated path circuit, not only the existing single `PathStep`.
