# Orchard Action Circuit Dependency Map

Source → Clean lookup for the Orchard action circuit and its dependencies. Implementations
are assumed proven (soundness + completeness) unless a **GAP** note says otherwise; only
unfinished or non-conformant items are flagged.

Source baseline:
- Orchard: `../audits/zcash-orchard/orchard-0.14.0`
- Halo2 gadgets: `../audits/zcash-orchard/halo2-halo2_gadgets-0.5.0`

## Action Circuit

- `Circuit::synthesize`
  - Source: `orchard-0.14.0/src/circuit.rs`
  - Clean: `Orchard.Action.circuit` in `Clean/Orchard/Action.lean`. Composes the gadget
    blocks (Merkle/anchor, value commitment, nullifier, spend authority, address integrity,
    old + new note commitment) and ties their outputs to the public instance cells
    (`ANCHOR`, `CV_NET_X/Y`, `NF_OLD`, `RK_X/Y`, `CMX`, `ENABLE_SPEND`, `ENABLE_OUTPUT`) plus
    the `q_orchard` gate (`Action.Gate.circuit`).
  - Witness helpers:
    - `assign_free_advice` (`orchard-0.14.0/src/circuit/gadget.rs`)
      - **GAP:** no dedicated wrapper; single-cell witnesses appear locally where needed.
    - `Point::new`, `NonIdentityPoint::new` (`halo2_gadgets/src/ecc/chip/witness_point.rs`)
      - Clean: `WitnessPoint.circuit`, `WitnessNonIdentityPoint.circuit` in
        `Clean/Orchard/Ecc/WitnessPoint.lean`.

  - Merkle path validity
    - `MerklePath::calculate_root` (`halo2_gadgets/src/sinsemilla/merkle.rs`)
      - Clean: `Sinsemilla.Merkle.CalculateRoot.circuit` in `Clean/Orchard/Sinsemilla/Merkle.lean`.
    - `CondSwapInstructions::swap` (`halo2_gadgets/src/utilities/cond_swap.rs`)
      - Clean: `CondSwap.Swap.circuit` (gate `CondSwap.Gate.circuit`) in `Clean/Orchard/Utilities.lean`.
    - `MerkleInstructions::hash_layer` (`halo2_gadgets/src/sinsemilla/merkle/chip.rs`)
      - Clean: `Sinsemilla.Merkle.HashLayer.circuit` (gate `Sinsemilla.Merkle.circuit`) in
        `Clean/Orchard/Sinsemilla/Merkle.lean`.
    - `MessagePiece::from_subpieces` (`halo2_gadgets/src/sinsemilla/message.rs`)
      - **GAP:** partially modeled through message-piece gates; no complete source-level API.
    - `RangeConstrained::witness_short` (`halo2_gadgets/src/utilities/lookup_range_check.rs`)
      - Clean: `LookupRangeCheck.WitnessShort.circuit` / `.taggedCircuit` in `Clean/Orchard/Utilities.lean`.
    - `SinsemillaChip::hash_to_point` (`halo2_gadgets/src/sinsemilla/chip/hash_to_point.rs`)
      - Clean: `Sinsemilla.Entry.circuit` (with `HashPiece`/`Chain`) in `Clean/Orchard/Sinsemilla/HashToPoint.lean`.
      - **GAP:** output signature. Halo2 returns `(Point, zs)` (per-piece running sums); the
        base `Entry` returns only the point and the `z1` cells. Action circuits needing
        running sums use `CommitDomain.WithZs`. Also missing: `hash_to_point_with_private_init`.
      - Generator table (`halo2_gadgets/src/sinsemilla/chip/generator_table.rs`)
        - Clean: `generatorTable` in `Clean/Orchard/Sinsemilla/HashToPoint.lean`.
      - Double-and-add gate (`halo2_gadgets/src/sinsemilla/chip/hash_to_point.rs`)
        - Clean: `Sinsemilla.Gate.circuit`, `HashToPoint.HashPiece`.
      - Incomplete addition (`halo2_gadgets/src/ecc/chip/add_incomplete.rs`)
        - Clean: `Clean/Orchard/Ecc/AddIncomplete.lean`.

  - Value commitment integrity
    - `gadget::value_commit_orchard` (`orchard-0.14.0/src/circuit/gadget.rs`)
      - Clean: `Gadget.ValueCommitOrchard.circuit` in `Clean/Orchard/Gadget.lean`.
    - `[v] ValueCommitV` (`FixedPointShort::mul`, `halo2_gadgets/src/ecc/chip/mul_fixed/short.rs`)
      - Clean: `Clean/Orchard/Ecc/ScalarMul/MulFixed/Short.lean`.
    - `[rcv] ValueCommitR` (`FixedPoint::mul`, `halo2_gadgets/src/ecc/chip/mul_fixed/full_width.rs`)
      - Clean: `Clean/Orchard/Ecc/ScalarMul/MulFixed/FullWidth.lean`.
    - Complete addition (`halo2_gadgets/src/ecc/chip/add.rs`)
      - Clean: `Clean/Orchard/Ecc/Add.lean`.

  - Nullifier integrity
    - `gadget::derive_nullifier` (`orchard-0.14.0/src/circuit/gadget.rs`)
      - Clean: `Gadget.DeriveNullifier.circuit` in `Clean/Orchard/Gadget.lean`.
    - `PoseidonHash::init` (`halo2_gadgets/src/poseidon`)
      - Clean: `InitialState.circuit` in `Clean/Orchard/Poseidon/Sponge.lean`.
    - `PoseidonHash::hash(nk, rho)` (`halo2_gadgets/src/poseidon`)
      - Clean: `Hash.ConstantLength.circuit` in `Clean/Orchard/Poseidon/Hash.lean`; depends on
        sponge `AddInput.circuit` (`Sponge.lean`), `Permute.circuit` (`Pow5.lean`), and the
        `full round` / `partial rounds` / `pad-and-add` gates (`Pow5.lean`).
    - Add Poseidon output to `psi` (`orchard-0.14.0/src/circuit/gadget/add_chip.rs`)
      - Clean: `AddChip.circuit` (gate `AddChip.Gate.circuit`) in `Clean/Orchard/Utilities.lean`.
    - `[poseidon_hash(nk, rho) + psi] NullifierK`
      (`FixedPointBaseField::mul`, `halo2_gadgets/src/ecc/chip/mul_fixed/base_field_elem.rs`)
      - Clean: `BaseFieldElem.circuit` in `Clean/Orchard/Ecc/ScalarMul/MulFixed/BaseFieldElem.lean`.
    - Add result to `cm_old` (`halo2_gadgets/src/ecc/chip/add.rs`)
      - Clean: `Clean/Orchard/Ecc/Add.lean`.

  - Spend authority
    - Source: `orchard-0.14.0/src/circuit.rs`, `Spend authority`
    - Clean: `SpendAuthority.circuit` in `Clean/Orchard/SpendAuthority.lean`
      (the `RK_X`/`RK_Y` public constraints are wired in `Orchard.Action.circuit`).
    - `[alpha] SpendAuthG` (`FixedPoint::mul`, `halo2_gadgets/src/ecc/chip/mul_fixed/full_width.rs`)
      - Clean: `Clean/Orchard/Ecc/ScalarMul/MulFixed/FullWidth.lean`.
    - Add to `ak_P` (`halo2_gadgets/src/ecc/chip/add.rs`)
      - Clean: `Clean/Orchard/Ecc/Add.lean`.

  - Diversified address integrity
    - Source: `orchard-0.14.0/src/circuit.rs`, `Diversified address integrity`
    - Clean: `Action.AddressIntegrity.circuit`.
    - `gadget::commit_ivk` (`orchard-0.14.0/src/circuit/commit_ivk.rs`)
      - Clean: `Orchard.Action.CommitIvk.circuit` in `Clean/Orchard/Action/CommitIvk.lean`.
    - `CommitIvk canonicity check` (`orchard-0.14.0/src/circuit/commit_ivk.rs`)
      - Clean: `CommitIvk.Gate.circuit` in `Clean/Orchard/Action/CommitIvkGate.lean`.
    - `RangeConstrained::witness_short` (`halo2_gadgets/src/utilities/lookup_range_check.rs`)
      - Clean: `LookupRangeCheck.WitnessShort.circuit` / `.taggedCircuit`.
    - `CommitDomain::short_commit` (`halo2_gadgets/src/sinsemilla`)
      - Clean: `Sinsemilla.CommitDomain.Short.circuit` in `Clean/Orchard/Sinsemilla/Domain.lean`
        (over `CommitDomain.circuit` + `CommitDomain.blindingFactor`).
    - `ScalarVar::from_base` (`halo2_gadgets/src/ecc`)
      - **GAP:** no dedicated source-level conversion entry identified.
    - `[ivk] g_d_old` (variable-base mul, `halo2_gadgets/src/ecc/chip/mul.rs`)
      - Clean: `Mul.circuit` in `Clean/Orchard/Ecc/ScalarMul/Mul/Assign.lean`.
      - Incomplete gates: `Clean/Orchard/Ecc/ScalarMul/Mul/Incomplete.lean`.
      - Complete gates: `Clean/Orchard/Ecc/ScalarMul/Mul/Complete.lean`.
      - Overflow checks: `Clean/Orchard/Ecc/ScalarMul/Mul/Overflow.lean`.

  - Old note commitment integrity
    - `gadget::note_commit` (`orchard-0.14.0/src/circuit/note_commit.rs`)
      - Clean: `Action.NoteCommit.circuit` in `Clean/Orchard/Action/NoteCommit.lean`.
    - `DecomposeB`/`D`/`E`/`G`/`H`
      - Clean: `Action.NoteCommit.DecomposeB`/`D`/`E`/`G`/`H.circuit`.
    - `GdCanonicity`/`PkdCanonicity`/`ValueCanonicity`/`RhoCanonicity`/`PsiCanonicity`/`YCanonicity`
      - Clean: `Action.NoteCommit.{Gd,Pkd,Value,Rho,Psi,Y}Canonicity.circuit`.
    - `RangeConstrained::witness_short`
      - Clean: `LookupRangeCheck.WitnessShort.circuit` / `.taggedCircuit`.
    - `CommitDomain::commit` (`halo2_gadgets/src/sinsemilla`)
      - Clean: `Sinsemilla.CommitDomain.circuit` in `Clean/Orchard/Sinsemilla/Domain.lean`.
    - `SinsemillaChip::hash_to_point`
      - Clean: `Sinsemilla.Entry.circuit` (see Merkle path above).
    - `[rcm_old] NoteCommitR` (full-width fixed-base mul)
      - Clean: `Clean/Orchard/Ecc/ScalarMul/MulFixed/FullWidth.lean`.
    - Add hash point to blinding point (ECC addition)
      - Clean: composed inside `Action.NoteCommit.circuit` via `Sinsemilla.CommitDomain.WithZs.circuit`.

  - New note commitment integrity
    - Same dependency tree as old note commitment; action wiring differs (`rho_new = nf_old`,
      output `cm_new.extract_p()` constrained to `CMX`). Wired in `Orchard.Action.circuit`.

  - Final Orchard circuit checks
    - Source: `orchard-0.14.0/src/circuit.rs`, region `"Orchard circuit checks"`
    - Clean: `Action.Gate.circuit` (the `q_orchard` gate), composed in `Orchard.Action.circuit`.

## Shared Low-Level Dependencies

- Lookup range checks (`halo2_gadgets/src/utilities/lookup_range_check.rs`)
  - Clean: `tableIdx`, `CopyCheck.circuit`, `shortRangeCircuit`, `taggedShortRangeCircuit`
    in `Clean/Orchard/Utilities.lean`.
- Running-sum range gate (`halo2_gadgets/src/utilities/decompose_running_sum.rs`)
  - Clean: `RunningSum.circuit` in `Clean/Orchard/Utilities.lean`.
- Boolean checks (`halo2_gadgets/src/utilities.rs`, `bool_check`)
  - Clean: modeled locally in gate files; general gadgets in `Clean/Gadgets/Boolean.lean`.
- Complete ECC addition (`halo2_gadgets/src/ecc/chip/add.rs`)
  - Clean: `Clean/Orchard/Ecc/Add.lean`.
- Incomplete ECC addition (`halo2_gadgets/src/ecc/chip/add_incomplete.rs`)
  - Clean: `Clean/Orchard/Ecc/AddIncomplete.lean`.
- Fixed-base scalar multiplication (`halo2_gadgets/src/ecc/chip/mul_fixed*.rs`)
  - Clean: `MulFixed/Short.lean`, `MulFixed/FullWidth.lean`, `MulFixed/BaseFieldElem.lean`
    (all under `Clean/Orchard/Ecc/ScalarMul/`).
- Variable-base scalar multiplication (`halo2_gadgets/src/ecc/chip/mul*.rs`)
  - Clean: `Mul.circuit` (`Clean/Orchard/Ecc/ScalarMul/Mul/Assign.lean`).
