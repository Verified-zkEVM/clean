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
      - Clean: not implemented as a source-level Merkle path entry circuit. TODO in `Clean/Orchard/Sinsemilla.lean`.
      - For each tree layer:
        - `CondSwapInstructions::swap`
          - Source: `halo2_gadgets/src/utilities/cond_swap.rs`, called via `halo2_gadgets/src/sinsemilla/merkle/chip.rs`
          - Clean: implemented in `Clean/Orchard/Utilities.lean` as `CondSwap.Swap.circuit`; gate factored as `CondSwap.Gate.circuit`.
        - `MerkleInstructions::hash_layer`
          - Source: `halo2_gadgets/src/sinsemilla/merkle/chip.rs`
          - Clean: only the local decomposition gate is present in `Clean/Orchard/Sinsemilla.lean` as `Merkle.circuit`; no full hash-layer entry circuit.
          - `MessagePiece::from_subpieces`
            - Source: `halo2_gadgets/src/sinsemilla/message.rs`
            - Clean: partially modeled through Sinsemilla/message-piece gates; no complete source-level message-piece API.
          - `RangeConstrained::witness_short`
            - Source: `halo2_gadgets/src/utilities/lookup_range_check.rs`
            - Clean: generic `shortRangeCircuit` and tagged 4/5B `taggedShortRangeCircuit` are lookup-backed in `Clean/Orchard/Utilities.lean`.
          - `SinsemillaChip::hash_to_point`
            - Source: `halo2_gadgets/src/sinsemilla/chip.rs`, `halo2_gadgets/src/sinsemilla/chip/hash_to_point.rs`
            - Clean: partial work in `Clean/Orchard/Sinsemilla/HashToPoint.lean`; not wired as the full Orchard `hash_to_point` API.
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
      - Clean: not implemented as an entry circuit. TODO in `Clean/Orchard/Gadget.lean`.
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
        - Clean: only the row gate is present in `Clean/Orchard/Ecc/ScalarMul/MulFixed/BaseFieldElem.lean`; source-level entry is missing.
      - Add result to `cm_old`
        - Source: `halo2_gadgets/src/ecc/chip/add.rs`
        - Clean: implemented in `Clean/Orchard/Ecc/Add.lean`.

  - Spend authority
    - Source block: `orchard-0.14.0/src/circuit.rs`, `Spend authority`
    - Clean: not implemented as an action/source entry. TODO in `Clean/Orchard/Gadget.lean`.
    - `[alpha] SpendAuthG`
      - Source: `FixedPoint::mul`, `halo2_gadgets/src/ecc/chip/mul_fixed/full_width.rs`
      - Clean: implemented in `Clean/Orchard/Ecc/ScalarMul/MulFixed/FullWidth.lean`.
    - Add `[alpha] SpendAuthG` to `ak_P`
      - Source: `halo2_gadgets/src/ecc/chip/add.rs`
      - Clean: implemented in `Clean/Orchard/Ecc/Add.lean`.

  - Diversified address integrity
    - Source block: `orchard-0.14.0/src/circuit.rs`, `Diversified address integrity`
    - Clean: not implemented as action wiring. TODO in `Clean/Orchard/Action.lean`.
    - `gadget::commit_ivk`
      - Source: `orchard-0.14.0/src/circuit/commit_ivk.rs`
      - Clean: only the canonicity gate is implemented in `Clean/Orchard/CommitIvk.lean` as `CommitIvk.circuit`; full `gadgets::commit_ivk` entry is missing.
      - `CommitIvk canonicity check`
        - Source: `orchard-0.14.0/src/circuit/commit_ivk.rs`
        - Clean: implemented in `Clean/Orchard/CommitIvk.lean`.
      - `RangeConstrained::witness_short` for `b_0`, `b_2`, `d_0`
        - Source: `halo2_gadgets/src/utilities/lookup_range_check.rs`
        - Clean: generic short checks and optimized tagged 4/5B checks are lookup-backed.
      - `CommitDomain::short_commit`
        - Source: `halo2_gadgets/src/sinsemilla`
        - Clean: not implemented as a source-level commit/short-commit API. TODO in `Clean/Orchard/Sinsemilla.lean`.
        - Depends on `SinsemillaChip::hash_to_point`
          - Clean: partial, see Merkle path dependency above.
        - Depends on fixed-base blinding and incomplete/complete ECC additions
          - Clean: fixed-base mul and ECC add pieces exist; full short-commit wiring is missing.
    - `ScalarVar::from_base`
      - Source: `halo2_gadgets/src/ecc`
      - Clean: no dedicated source-level conversion entry identified.
    - `[ivk] g_d_old`
      - Source: variable-base scalar multiplication, `halo2_gadgets/src/ecc/chip/mul.rs`
      - Clean: row gates and entry work exist under `Clean/Orchard/Ecc/ScalarMul/Mul*.lean`; conformance map still marks source entry/API gaps.
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
        - Clean: generic short lookup path and optimized tagged 4/5B path are source-shaped.
      - `CommitDomain::commit`
        - Source: `halo2_gadgets/src/sinsemilla`
        - Clean: not implemented as a source-level commit API.
      - `SinsemillaChip::hash_to_point`
        - Clean: partial, see Merkle path dependency above.
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
    - base-field-element fixed-base mul gate only: `Clean/Orchard/Ecc/ScalarMul/MulFixed/BaseFieldElem.lean`

- Variable-base scalar multiplication
  - Source: `halo2_gadgets/src/ecc/chip/mul*.rs`
  - Clean: pieces under `Clean/Orchard/Ecc/ScalarMul/Mul*.lean`; source-level entry/API conformance still incomplete.
