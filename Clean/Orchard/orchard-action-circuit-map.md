# Orchard Action Circuit Dependency Map

Source baseline:
- Orchard: `../audits/zcash-orchard/orchard-0.14.0`
- Halo2 gadgets: `../audits/zcash-orchard/halo2-halo2_gadgets-0.5.0`

## Action Circuit

- `Circuit::synthesize`
  - Source: `orchard-0.14.0/src/circuit.rs`
  - Clean: no full action entry circuit yet. Only the final action arithmetic gate is present in `Clean/Orchard/Action.lean` as `ActionChecks.circuit`.
  - Public inputs/wiring:
    - `ANCHOR`, `CV_NET_X`, `CV_NET_Y`, `NF_OLD`, `RK_X`, `RK_Y`, `CMX`, `ENABLE_SPEND`, `ENABLE_OUTPUT`
    - Clean: not implemented as a top-level public-input/action wiring circuit.
  - Witness helpers:
    - `assign_free_advice`
      - Source: `orchard-0.14.0/src/circuit/gadget.rs`
      - Clean: no dedicated wrapper; equivalent single-cell witnesses appear locally where needed.
    - `Point::new`, `NonIdentityPoint::new`
      - Source: `halo2_gadgets/src/ecc/chip.rs`, `halo2_gadgets/src/ecc/chip/witness_point.rs`
      - Clean: implemented in `Clean/Orchard/Ecc/WitnessPoint.lean` as `WitnessPoint.circuit` and `WitnessNonIdentityPoint.circuit`.

  - Merkle path validity
    - `MerklePath::calculate_root`
      - Source: `halo2_gadgets/src/sinsemilla/merkle.rs`
      - Clean: implemented in `Clean/Orchard/Sinsemilla/Merkle.lean` as
        `Sinsemilla.Merkle.CalculateRoot.circuit` (proven sound and complete): a
        `Circuit.foldl` over 32 `Merkle.Layer` sub-circuits (each composing
        `CondSwap.Swap.circuit` with `Merkle.HashLayer.circuit`).
      - For each tree layer:
        - `CondSwapInstructions::swap`
          - Source: `halo2_gadgets/src/utilities/cond_swap.rs`, called via `halo2_gadgets/src/sinsemilla/merkle/chip.rs`
          - Clean: implemented in `Clean/Orchard/Utilities.lean` as `CondSwap.Swap.circuit`; gate factored as `CondSwap.Gate.circuit`.
        - `MerkleInstructions::hash_layer`
          - Source: `halo2_gadgets/src/sinsemilla/merkle/chip.rs`
          - Clean: implemented in `Clean/Orchard/Sinsemilla/Merkle.lean` as
            `Sinsemilla.Merkle.HashLayer.circuit` (proven sound and complete);
            the local decomposition gate is `Sinsemilla.Merkle.circuit`.
          - `MessagePiece::from_subpieces`
            - Source: `halo2_gadgets/src/sinsemilla/message.rs`
            - Clean: partially modeled through Sinsemilla/message-piece gates; no complete source-level message-piece API.
          - `RangeConstrained::witness_short`
            - Source: `halo2_gadgets/src/utilities/lookup_range_check.rs`
            - Clean: `LookupRangeCheck.WitnessShort.circuit` and
              `LookupRangeCheck.WitnessShort.taggedCircuit` in
              `Clean/Orchard/Utilities.lean`; both call lookup-backed short checks.
          - `SinsemillaChip::hash_to_point`
            - Source: `halo2_gadgets/src/sinsemilla/chip.rs`, `halo2_gadgets/src/sinsemilla/chip/hash_to_point.rs`
            - Clean: implemented in `Clean/Orchard/Sinsemilla/HashToPoint.lean` as
              `Sinsemilla.Entry.circuit` (with `HashPiece`/`Chain`), proven sound and
              complete; lands at `Specs.Sinsemilla.hashToPoint`. NON-CONFORMANT output
              signature: Halo2 returns `(Point, Vec<Vec<AssignedCell>>)` (the per-piece
              running sums `zs`); Clean returns only the point + a one-off `z1`, not the
              full `zs`. This blocks `note_commit`/`commit_ivk` canonicity. See the
              conformance map's "Hash Output Signature: Running Sums" non-conformance.
              (Also still missing: `hash_to_point_with_private_init`.)
            - Generator lookup table
              - Source: `halo2_gadgets/src/sinsemilla/chip/generator_table.rs`
              - Clean: `generatorTable` in `Clean/Orchard/Sinsemilla/HashToPoint.lean`.
            - Sinsemilla double-and-add gate
              - Source: `halo2_gadgets/src/sinsemilla/chip/hash_to_point.rs`
              - Clean: `Sinsemilla.Gate.circuit` and `HashToPoint.HashPiece` work in `Clean/Orchard/Sinsemilla.lean` and `Clean/Orchard/Sinsemilla/HashToPoint.lean`.
            - ECC incomplete addition
              - Source: `halo2_gadgets/src/ecc/chip/add_incomplete.rs`
              - Clean: implemented in `Clean/Orchard/Ecc/AddIncomplete.lean`.

  - Value commitment integrity
    - `gadget::value_commit_orchard`
      - Source: `orchard-0.14.0/src/circuit/gadget.rs`
      - Clean: implemented in `Clean/Orchard/Gadget.lean` as `Gadget.ValueCommitOrchard.circuit`.
      - `[v] ValueCommitV`
        - Source: `FixedPointShort::mul`, `halo2_gadgets/src/ecc/chip/mul_fixed/short.rs`
        - Clean: implemented in `Clean/Orchard/Ecc/ScalarMul/MulFixed/Short.lean`.
      - `[rcv] ValueCommitR`
        - Source: `FixedPoint::mul`, `halo2_gadgets/src/ecc/chip/mul_fixed/full_width.rs`
        - Clean: implemented in `Clean/Orchard/Ecc/ScalarMul/MulFixed/FullWidth.lean`.
      - Complete addition of the two commitment points
        - Source: `halo2_gadgets/src/ecc/chip/add.rs`
        - Clean: implemented in `Clean/Orchard/Ecc/Add.lean`.

  - Nullifier integrity
    - `gadget::derive_nullifier`
      - Source: `orchard-0.14.0/src/circuit/gadget.rs`
      - Clean: `Gadget.DeriveNullifier.circuit` in `Clean/Orchard/Gadget.lean` — fully
        verified (soundness + completeness, no sorries); composes the Poseidon hash, the
        `BaseFieldElem` fixed-base mul by `NullifierK`, and the complete addition with
        `cm`, returning the extracted `x`-coordinate.
      - `PoseidonHash::init`
        - Source: `halo2_gadgets/src/poseidon`
        - Clean: implemented in `Clean/Orchard/Poseidon/Sponge.lean` as `InitialState.circuit`.
      - `PoseidonHash::hash(nk, rho)`
        - Source: `halo2_gadgets/src/poseidon`
        - Clean: implemented in `Clean/Orchard/Poseidon/Hash.lean` as `Hash.ConstantLength.circuit`; depends on:
          - Sponge absorb/add input
            - Clean: `Clean/Orchard/Poseidon/Sponge.lean`, `AddInput.circuit`.
          - Poseidon permutation
            - Clean: `Clean/Orchard/Poseidon/Pow5.lean`, `Permute.circuit`.
          - Gates `full round`, `partial rounds`, `pad-and-add`
            - Clean: `Clean/Orchard/Poseidon/Pow5.lean`.
      - Add Poseidon output to `psi`
        - Source: `orchard-0.14.0/src/circuit/gadget/add_chip.rs`
        - Clean: implemented in `Clean/Orchard/Utilities.lean` as `AddChip.circuit`; gate factored as `AddChip.Gate.circuit`.
      - `[poseidon_hash(nk, rho) + psi] NullifierK`
        - Source: `FixedPointBaseField::mul`, `halo2_gadgets/src/ecc/chip/mul_fixed/base_field_elem.rs`
        - Clean: source-level entry `BaseFieldElem.circuit` in `Clean/Orchard/Ecc/ScalarMul/MulFixed/BaseFieldElem.lean` — fully verified (soundness + completeness, no sorries); composes the `RunningSumMul` windowed mul with the canonicity gate.
      - Add result to `cm_old`
        - Source: `halo2_gadgets/src/ecc/chip/add.rs`
        - Clean: implemented in `Clean/Orchard/Ecc/Add.lean`.

  - Spend authority
    - Source block: `orchard-0.14.0/src/circuit.rs`, `Spend authority`
    - Clean: implemented in `Clean/Orchard/SpendAuthority.lean` as
      `SpendAuthority.circuit` (proven sound and complete): it witnesses `alpha` as a
      full-width fixed scalar via `MulFixed.FullWidth.circuit`, discards the returned
      scalar decomposition as the source does, and computes
      `rk = [alpha] SpendAuthG + ak_P` via complete addition. The public-input
      constraints on `RK_X` and `RK_Y` remain part of the missing top-level action
      wiring.
    - `[alpha] SpendAuthG`
      - Source: `FixedPoint::mul`, `halo2_gadgets/src/ecc/chip/mul_fixed/full_width.rs`
      - Clean: implemented in `Clean/Orchard/Ecc/ScalarMul/MulFixed/FullWidth.lean`.
    - Add `[alpha] SpendAuthG` to `ak_P`
      - Source: `halo2_gadgets/src/ecc/chip/add.rs`
      - Clean: implemented in `Clean/Orchard/Ecc/Add.lean`.

  - Diversified address integrity
    - Source block: `orchard-0.14.0/src/circuit.rs`, `Diversified address integrity`
    - Clean: implemented as the bundled mid-level circuit
      `Clean.Orchard.Action.AddressIntegrity.circuit`. It composes
      `Action.CommitIvk.circuit`, variable-base `Mul.circuit`, and an equality assertion
      tying the derived point to the witnessed `pk_d_old`.
    - `gadget::commit_ivk`
      - Source: `orchard-0.14.0/src/circuit/commit_ivk.rs`
      - Clean: implemented in `Clean/Orchard/Action/CommitIvk.lean` as
        `Orchard.Action.CommitIvk.circuit` (a `GeneralFormalCircuit.WithHint` returning the
        extracted `x`-coordinate `ivk`). Composes the four Sinsemilla pieces `a, b, c, d`
        over `CommitDomain.WithZs` (rounds `24 :: [0, 23, 0]`), the `ak`/`nk` canonicity
        decompositions (`CopyCheck 13`/`CopyCheck 14`), and the `CommitIvk.Gate` canonicity
        gate. Spec is `CommitIvk.Spec` (point-level Sinsemilla short-commit relation over
        `commitIvkChunks`). **Fully proven — `soundness` and `completeness` both closed**
        (no `sorry`). The entry is factored into a virtual `Commit` subcircuit (witnessing +
        `WithZs` hash) composed with a `Canonicity` subcircuit (the two `CopyCheck`
        decompositions + the gate), each proven sound and complete; the top-level composes
        them via the chunk bridge `pieceChunks_eq_commitIvkChunks_of_indexed_piece_values`
        (soundness) and `honestChunks_eq_commitIvkChunks` (completeness).
      - `CommitIvk canonicity check`
        - Source: `orchard-0.14.0/src/circuit/commit_ivk.rs`
        - Clean: implemented in `Clean/Orchard/Action/CommitIvkGate.lean` as
          `CommitIvk.Gate.circuit`, proved sound and complete with a **lifted
          canonical-decomposition `Spec`** (under the lookup `Assumptions`, `a`/`b0`/`b1` are
          the canonical bit slices of `ak` and `b2`/`c`/`d0`/`d1` of `nk`) — mirroring the
          `NoteCommit` `GdCanonicity`/`PkdCanonicity` gates and reusing the shared
          `CanonicityTheorems`.
      - `RangeConstrained::witness_short` for `b_0`, `b_2`, `d_0`
        - Source: `halo2_gadgets/src/utilities/lookup_range_check.rs`
        - Clean: `LookupRangeCheck.WitnessShort.circuit` and
          `LookupRangeCheck.WitnessShort.taggedCircuit` wrap the generic and optimized
          lookup-backed short checks.
      - `CommitDomain::short_commit`
        - Source: `halo2_gadgets/src/sinsemilla`
        - Clean: implemented in `Clean/Orchard/Sinsemilla/Domain.lean` as
          `Sinsemilla.CommitDomain.Short.circuit` (proven sound and complete); the
          underlying `commit` is `Sinsemilla.CommitDomain.circuit` and the blinding
          term `Sinsemilla.CommitDomain.blindingFactor`.
        - Depends on `SinsemillaChip::hash_to_point`
          - Clean: `Sinsemilla.Entry.circuit`, done (see Merkle path dependency above).
        - Depends on fixed-base blinding and incomplete/complete ECC additions
          - Clean: composed inside `CommitDomain.circuit` (full-width fixed-base mul +
            complete addition).
    - `ScalarVar::from_base`
      - Source: `halo2_gadgets/src/ecc`
      - Clean: no dedicated source-level conversion entry identified.
    - `[ivk] g_d_old`
      - Source: variable-base scalar multiplication, `halo2_gadgets/src/ecc/chip/mul.rs`
      - Clean: implemented as the variable-base entry `Mul.circuit`
        (`Clean/Orchard/Ecc/ScalarMul/Mul/Assign.lean`, `FormalCircuit`, proven sound
        and complete; `Spec` is `output = [alpha] base`).
      - Incomplete variable-base mul gates
        - Source: `halo2_gadgets/src/ecc/chip/mul/incomplete.rs`
        - Clean: `Clean/Orchard/Ecc/ScalarMul/Mul/Incomplete.lean`.
      - Complete variable-base mul gates
        - Source: `halo2_gadgets/src/ecc/chip/mul/complete.rs`
        - Clean: `Clean/Orchard/Ecc/ScalarMul/Mul/Complete.lean`.
      - Overflow checks
        - Source: `halo2_gadgets/src/ecc/chip/mul/overflow.rs`
        - Clean: `Clean/Orchard/Ecc/ScalarMul/Mul/Overflow.lean`; uses lookup range-check `CopyCheck`.

  - Old note commitment integrity
    - `gadget::note_commit`
      - Source: `orchard-0.14.0/src/circuit/note_commit.rs`
      - Clean: only row/custom gates are implemented in `Clean/Orchard/NoteCommit.lean`; full `gadgets::note_commit` entry is missing.
      - `DecomposeB`
        - Clean: `NoteCommit.DecomposeB.circuit`.
      - `DecomposeD`
        - Clean: `NoteCommit.DecomposeD.circuit`.
      - `DecomposeE`
        - Clean: `NoteCommit.DecomposeE.circuit`.
      - `DecomposeG`
        - Clean: `NoteCommit.DecomposeG.circuit`.
      - `DecomposeH`
        - Clean: `NoteCommit.DecomposeH.circuit`.
      - `GdCanonicity`
        - Clean: `NoteCommit.GdCanonicity.circuit`.
      - `PkdCanonicity`
        - Clean: `NoteCommit.PkdCanonicity.circuit`.
      - `ValueCanonicity`
        - Clean: `NoteCommit.ValueCanonicity.circuit`.
      - `RhoCanonicity`
        - Clean: `NoteCommit.RhoCanonicity.circuit`.
      - `PsiCanonicity`
        - Clean: `NoteCommit.PsiCanonicity.circuit`.
      - `YCanonicity`
        - Clean: `NoteCommit.YCanonicity.circuit`.
      - `RangeConstrained::witness_short`
        - Clean: `LookupRangeCheck.WitnessShort.circuit` and
          `LookupRangeCheck.WitnessShort.taggedCircuit` are source-shaped wrappers.
      - `CommitDomain::commit`
        - Source: `halo2_gadgets/src/sinsemilla`
        - Clean: `Sinsemilla.CommitDomain.circuit`
          (`Clean/Orchard/Sinsemilla/Domain.lean`), proven sound and complete.
      - `SinsemillaChip::hash_to_point`
        - Clean: `Sinsemilla.Entry.circuit`, done (see Merkle path dependency above).
      - `[rcm_old] NoteCommitR`
        - Source: full-width fixed-base mul
        - Clean: `Clean/Orchard/Ecc/ScalarMul/MulFixed/FullWidth.lean`.
      - Add Sinsemilla hash point to blinding point
        - Source: ECC addition
        - Clean: `Clean/Orchard/Ecc/Add.lean` / `AddIncomplete.lean` pieces exist; full note-commit wiring missing.

  - New note commitment integrity
    - Same dependency tree as old note commitment.
    - Difference in action wiring:
      - `rho_new = nf_old`
      - public output is `cm_new.extract_p()` constrained to `CMX`
    - Clean: not implemented as action wiring.

  - Final Orchard circuit checks
    - Source: `orchard-0.14.0/src/circuit.rs`, region `"Orchard circuit checks"`
    - Clean: implemented in `Clean/Orchard/Action.lean` as `ActionChecks.circuit`.
    - Constraints:
      - `v_old - v_new = magnitude * sign`
      - if `v_old != 0`, calculated root equals public anchor
      - if `v_old != 0`, spends are enabled
      - if `v_new != 0`, outputs are enabled

## Shared Low-Level Dependencies

- Lookup range checks
  - Source: `halo2_gadgets/src/utilities/lookup_range_check.rs`
  - Clean:
    - `tableIdx` and `CopyCheck.circuit` are lookup-backed in `Clean/Orchard/Utilities.lean`.
    - generic `shortRangeCircuit` is lookup-backed in `Clean/Orchard/Utilities.lean`.
    - tagged 4/5-bit lookup path is implemented as `taggedShortRangeCircuit`.

- Arithmetic running-sum range gate
  - Source: `halo2_gadgets/src/utilities/decompose_running_sum.rs`
  - Clean: implemented source-conformantly as polynomial gate `RunningSum.circuit` in `Clean/Orchard/Utilities.lean`.

- Boolean checks
  - Source: `halo2_gadgets/src/utilities.rs`, `bool_check`
  - Clean: locally modeled in the gate files that need it; also general boolean gadgets exist in `Clean/Gadgets/Boolean.lean`.

- Complete ECC addition
  - Source: `halo2_gadgets/src/ecc/chip/add.rs`
  - Clean: `Clean/Orchard/Ecc/Add.lean`.

- Incomplete ECC addition
  - Source: `halo2_gadgets/src/ecc/chip/add_incomplete.rs`
  - Clean: `Clean/Orchard/Ecc/AddIncomplete.lean`.

- Fixed-base scalar multiplication
  - Source: `halo2_gadgets/src/ecc/chip/mul_fixed*.rs`
  - Clean:
    - short signed fixed-base mul: `Clean/Orchard/Ecc/ScalarMul/MulFixed/Short.lean`
    - full-width fixed-base mul: `Clean/Orchard/Ecc/ScalarMul/MulFixed/FullWidth.lean`
    - base-field-element fixed-base mul (entry circuit `BaseFieldElem.circuit`, fully verified): `Clean/Orchard/Ecc/ScalarMul/MulFixed/BaseFieldElem.lean`

- Variable-base scalar multiplication
  - Source: `halo2_gadgets/src/ecc/chip/mul*.rs`
  - Clean: full source-level entry `Mul.circuit`
    (`Clean/Orchard/Ecc/ScalarMul/Mul/Assign.lean`, `FormalCircuit`, proven sound and
    complete), composing the incomplete `DoubleAndAdd`, complete bits, `ProcessLsb`,
    and `OverflowCheck` sub-circuits (all under `Clean/Orchard/Ecc/ScalarMul/Mul*.lean`).
