import Clean.Ironwood.CommitIvk.Gate
import Clean.Ironwood.CommitIvk.GateTheorems

/-!
Reference (ported from actual Rust, not memory):
`orchard@0.14.0/src/circuit/commit_ivk.rs` — the `"CommitIvk canonicity check"` region
(`assign`, lines 519-660): `q_commit_ivk` at row 0; row 0 copies
`ak/a/b/b_0/b_2/z13_a/a_prime/z13_a_prime` and witnesses `b_1`; row 1 copies
`nk/c/d/d_0/z13_c/b2_c_prime/z14_b2_c_prime` and witnesses `d_1`.

The semantic contract is the phase-1 `CommitIvk.Gate` spec verbatim; the canonicity
value arguments are the donor row-level lemmas (`soundness_ak`/`soundness_nk` and the
extracted `eqs_of_spec`).
-/

namespace Zcash.Circuits.CommitIvk

open Halo2

private abbrev DRow := Gate.Input
private abbrev DSpec := Gate.Spec
private abbrev DAssumptions := Gate.Assumptions

/-- `v·(1−v) = 0` pins a boolean. -/
private theorem isBool_of_boolCheck {v : Fp} (h : v * (1 - v) = 0) : IsBool v := by
  rcases mul_eq_zero.mp h with h0 | h1
  · exact Or.inl h0
  · exact Or.inr (by linear_combination -h1)

/-- The copied-in cells (the `b_1`/`d_1` sign bits are witnessed in-region). -/
structure Inputs (F : Type) where
  ak : F
  a : F
  bWhole : F
  b0 : F
  b2 : F
  z13A : F
  aPrime : F
  z13APrime : F
  nk : F
  c : F
  dWhole : F
  d0 : F
  z13C : F
  b2CPrime : F
  z14B2CPrime : F
deriving ProvableStruct

/-- The donor-side row at the witnessed `(b1, d1)` pair. -/
def toDonor (row : Inputs Fp) (b1 d1 : Fp) : DRow Fp :=
  ⟨row.ak, row.nk, row.a, row.bWhole, row.c, row.dWhole, row.b0, b1, row.b2,
    row.d0, d1, row.z13A, row.z13C, row.aPrime, row.b2CPrime, row.z13APrime,
    row.z14B2CPrime⟩

/-- Advice columns into which the bundle copies its inputs. -/
@[keygen_norm]
def permutationColumns (cfg : Config) : List AnyColumn :=
  [cfg.advices 0, cfg.advices 1, cfg.advices 2, cfg.advices 3,
    cfg.advices 5, cfg.advices 6, cfg.advices 7, cfg.advices 8]

def synthesisSummary (cfg : Config) (offset : ℕ) :
    FloorPlanner.RegionSynthesisSummary :=
  .ofColumns
    [.selector cfg.qCommitIvk.index,
      .column .advice (cfg.advices 0).index,
      .column .advice (cfg.advices 1).index,
      .column .advice (cfg.advices 2).index,
      .column .advice (cfg.advices 3).index,
      .column .advice (cfg.advices 4).index,
      .column .advice (cfg.advices 5).index,
      .column .advice (cfg.advices 6).index,
      .column .advice (cfg.advices 7).index,
      .column .advice (cfg.advices 8).index,
      .column .advice (cfg.advices 0).index,
      .column .advice (cfg.advices 1).index,
      .column .advice (cfg.advices 2).index,
      .column .advice (cfg.advices 3).index,
      .column .advice (cfg.advices 4).index,
      .column .advice (cfg.advices 6).index,
      .column .advice (cfg.advices 7).index,
      .column .advice (cfg.advices 8).index]
    (offset + 2) 0

@[synthesis_summary_norm]
theorem synthesisSummary_hasNoFixedColumns (cfg : Config) (offset : ℕ) :
    (synthesisSummary cfg offset).HasNoFixedColumns := by
  unfold synthesisSummary
  rw [FloorPlanner.RegionSynthesisSummary.hasNoFixedColumns_ofColumns]
  simp

@[circuit_norm]
def bundleSynthesize (wb1 wd1 : WitgenIR Fp 1) (cfg : Config)
    (offset : ℕ) (input : Var Inputs Fp) : RegionCircuit Fp Unit := do
  (gate cfg).enable offset
  let _ak ← copyAdvice input.ak (cfg.advices 0) offset
  let _a ← copyAdvice input.a (cfg.advices 1) offset
  let _b ← copyAdvice input.bWhole (cfg.advices 2) offset
  let _b0 ← copyAdvice input.b0 (cfg.advices 3) offset
  let _b1 ← assignAdvice (cfg.advices 4) offset wb1
  let _b2 ← copyAdvice input.b2 (cfg.advices 5) offset
  let _z13a ← copyAdvice input.z13A (cfg.advices 6) offset
  let _ap ← copyAdvice input.aPrime (cfg.advices 7) offset
  let _z13ap ← copyAdvice input.z13APrime (cfg.advices 8) offset
  let _nk ← copyAdvice input.nk (cfg.advices 0) (offset + 1)
  let _c ← copyAdvice input.c (cfg.advices 1) (offset + 1)
  let _d ← copyAdvice input.dWhole (cfg.advices 2) (offset + 1)
  let _d0 ← copyAdvice input.d0 (cfg.advices 3) (offset + 1)
  let _d1 ← assignAdvice (cfg.advices 4) (offset + 1) wd1
  let _z13c ← copyAdvice input.z13C (cfg.advices 6) (offset + 1)
  let _b2cp ← copyAdvice input.b2CPrime (cfg.advices 7) (offset + 1)
  let _z14 ← copyAdvice input.z14B2CPrime (cfg.advices 8) (offset + 1)
  pure ()

@[reducible]
def bundleElaborated (wb1 wd1 : WitgenIR Fp 1) :
    ElaboratedRegionCircuit Fp Config Config Inputs unit pure
      (bundleSynthesize wb1 wd1) :=
  { keygenRequirements :=
      { gates cfg _ := [gate cfg]
        permutationColumns cfg _ := permutationColumns cfg
        inputCells _ _ input :=
          [input.ak.cell, input.a.cell, input.bWhole.cell, input.b0.cell,
            input.b2.cell, input.z13A.cell, input.aPrime.cell,
            input.z13APrime.cell, input.nk.cell, input.c.cell,
            input.dWhole.cell, input.d0.cell, input.z13C.cell,
            input.b2CPrime.cell, input.z14B2CPrime.cell] }
    synthesisSummary cfg offset _ _ := synthesisSummary cfg offset
    synthesisSummary_eq := by
      intro _ _ _ _
      apply FloorPlanner.RegionSynthesisSummary.ext
      · simp only [synthesisSummary, bundleSynthesize, circuit_norm,
          synthesis_summary_norm, configure_selector_norm]
      · simp only [synthesisSummary, bundleSynthesize, circuit_norm,
          synthesis_summary_norm]
        omega
      · simp only [synthesisSummary, bundleSynthesize, circuit_norm,
          synthesis_summary_norm]
      · simp only [synthesisSummary, bundleSynthesize, circuit_norm,
          synthesis_summary_norm]
    copyCellsAssigned := by keygen_registration [bundleSynthesize] }

/-- Rust `CommitIvkChip` canonicity `assign` (`commit_ivk.rs:519-660`), parameterized by
the `b_1`/`d_1` witness programs. The `(b1, d1)` readings are the extraction data;
`Spec` is the donor `CommitIvk.Gate.Spec` at them, `Assumptions` the input-only donor
rely-conditions (the two witnessed-bit implications move to `ProverAssumptions`). -/
def bundle (wb1 wd1 : WitgenIR Fp 1) :
    FormalRegionCircuit Fp Config Config Inputs unit where
  configure := pure
  synthesize := bundleSynthesize wb1 wd1
  elaborated := bundleElaborated wb1 wd1

  Witness := fieldPair
  extract cfg offset _ self env :=
    (eval env (AssignedCell.of self offset (cfg.advices 4) : Var field Fp),
     eval env (AssignedCell.of self (offset + 1) (cfg.advices 4) : Var field Fp))

  -- the input-only rely-conditions (donor `Assumptions` minus the witnessed-bit
  -- implications)
  -- input-only rely-conditions: the gate itself enforces both shifts (constraints 9/13)
  Assumptions input :=
    input.a.val < 2 ^ 250 ∧ input.b0.val < 2 ^ 4 ∧ input.b2.val < 2 ^ 5 ∧
    input.c.val < 2 ^ 240 ∧ input.d0.val < 2 ^ 9 ∧
    input.z13A = ((input.a.val / 2 ^ 130 : ℕ) : Fp) ∧
    (∃ lo : ℕ, lo < 2 ^ 130 ∧
      input.aPrime = ((lo : ℕ) : Fp) + ((2 ^ 130 : ℕ) : Fp) * input.z13APrime) ∧
    input.z13C = ((input.c.val / 2 ^ 130 : ℕ) : Fp) ∧
    (∃ lo : ℕ, lo < 2 ^ 140 ∧
      input.b2CPrime = ((lo : ℕ) : Fp) + ((2 ^ 140 : ℕ) : Fp) * input.z14B2CPrime)

  Spec := fun input _ (wit : Fp × Fp) => DSpec (toDonor input wit.1 wit.2)

  ProverAssumptions := fun input (wit : Fp × Fp) _ =>
    (wit.1 = 1 → input.z13APrime = 0) ∧ (wit.2 = 1 → input.z14B2CPrime = 0) ∧
    input.aPrime = input.a + ((2 ^ 130 : ℕ) : Fp) - tP ∧
    input.b2CPrime = input.b2 + input.c * ((2 ^ 5 : ℕ) : Fp)
      + ((2 ^ 140 : ℕ) : Fp) - tP ∧
    DSpec (toDonor input wit.1 wit.2)

  soundness := by
    circuit_proof_start [gate, boolCheck]
    obtain ⟨⟨hb1c, hd1c, hbW, hdW, hak, hnk, hb1b0, hb1z13A, hapC, hb1z13ap,
      hd1d0, hd1z13C, hb2cpC, hd1z14⟩,
      hcak, hca, hcb, hcb0, hcb2, hcz13a, hcap, hcz13ap,
      hcnk, hcc, hcd, hcd0, hcz13c, hcb2cp, hcz14⟩ := hc
    rw [hca, hcb0, hcak] at hak
    rw [hcb2, hcc, hcd0, hcnk] at hnk
    rw [hcb0] at hb1b0
    rw [hcz13a] at hb1z13A
    rw [hcz13ap] at hb1z13ap
    rw [hcd0] at hd1d0
    rw [hcz13c] at hd1z13C
    rw [hcb, hcb0, hcb2] at hbW
    rw [hcd, hcd0] at hdW
    rw [hcz14] at hd1z14
    have hidx1 : (((place self : ℕ) : ℤ) + (((offset : ℕ) : ℤ) + 1))
        = ((place self : ℕ) : ℤ) + ((offset : ℕ) : ℤ) + 1 := by ring
    rw [hca, hcap] at hapC
    rw [hcb2, hcc, hcb2cp] at hb2cpC
    have hapS : input_aPrime = input_a + ((2 ^ 130 : ℕ) : Fp) - tP := by
      push_cast at hapC ⊢; linear_combination -hapC
    have hb2cS : input_b2CPrime = input_b2 + input_c * ((2 ^ 5 : ℕ) : Fp)
        + ((2 ^ 140 : ℕ) : Fp) - tP := by
      push_cast at hb2cpC ⊢; linear_combination -hb2cpC
    have hakEq : input_a + input_b0 * ((2 ^ 250 : ℕ) : Fp)
        + env.advice (cfg.advices 4)
            (((place self : ℕ) : ℤ) + ((offset : ℕ) : ℤ))
          * ((2 ^ 254 : ℕ) : Fp) - input_ak = 0 := by
      push_cast at hak ⊢; linear_combination hak
    have hnkEq : input_b2 + input_c * ((2 ^ 5 : ℕ) : Fp)
        + input_d0 * ((2 ^ 245 : ℕ) : Fp)
        + env.advice (cfg.advices 4)
            (((place self : ℕ) : ℤ) + ((offset : ℕ) : ℤ) + 1)
          * ((2 ^ 254 : ℕ) : Fp) - input_nk = 0 := by
      push_cast at hnk ⊢
      rw [hidx1] at hnk
      linear_combination hnk
    obtain ⟨hakE1, hakE2, hakE3⟩ :=
      Gate.soundness_ak hA.1 hA.2.1
        (isBool_of_boolCheck hb1c) hapS hA.2.2.2.2.2.1
        hA.2.2.2.2.2.2.1 hakEq hb1b0 hb1z13A hb1z13ap
    obtain ⟨hnkE1, hnkE2, hnkE3, hnkE4⟩ :=
      Gate.soundness_nk hA.2.2.1 hA.2.2.2.1 hA.2.2.2.2.1
        (isBool_of_boolCheck hd1c) hb2cS
        hA.2.2.2.2.2.2.2.2 hnkEq hd1d0 hd1z14
    exact ⟨hakE1, hakE2, hakE3, hnkE1, hnkE2, hnkE3, hnkE4,
      by simp only [toDonor]; push_cast at hbW ⊢; linear_combination hbW,
      by simp only [toDonor]; push_cast at hdW ⊢
         rw [hidx1] at hdW
         ring_nf at hdW ⊢
         linear_combination hdW⟩

  completeness := by
    intro cfg offset
    rw [FormalRegionCircuit.completeness_iff]
    intro self env input_var input output h_input h_output hwit _hE hA hPA
    simp only [circuit_norm, gate, boolCheck] at hwit h_input h_output hA hPA ⊢
    obtain ⟨hwak, hwa, hwb, hwb0, hwb1, hwb2, hwz13a, hwap, hwz13ap,
      hwnk, hwc, hwd, hwd0, hwd1, hwz13c, hwb2cp, hwz14⟩ := hwit
    rw [show (ProvableStruct.Halo2.eval env.place env.env.toEnvironment input_var
        : Inputs Fp)
      = { ak := AssignedCell.eval env.place env.env.toEnvironment input_var.ak,
          a := AssignedCell.eval env.place env.env.toEnvironment input_var.a,
          bWhole := AssignedCell.eval env.place env.env.toEnvironment input_var.bWhole,
          b0 := AssignedCell.eval env.place env.env.toEnvironment input_var.b0,
          b2 := AssignedCell.eval env.place env.env.toEnvironment input_var.b2,
          z13A := AssignedCell.eval env.place env.env.toEnvironment input_var.z13A,
          aPrime := AssignedCell.eval env.place env.env.toEnvironment input_var.aPrime,
          z13APrime := AssignedCell.eval env.place env.env.toEnvironment input_var.z13APrime,
          nk := AssignedCell.eval env.place env.env.toEnvironment input_var.nk,
          c := AssignedCell.eval env.place env.env.toEnvironment input_var.c,
          dWhole := AssignedCell.eval env.place env.env.toEnvironment input_var.dWhole,
          d0 := AssignedCell.eval env.place env.env.toEnvironment input_var.d0,
          z13C := AssignedCell.eval env.place env.env.toEnvironment input_var.z13C,
          b2CPrime := AssignedCell.eval env.place env.env.toEnvironment input_var.b2CPrime,
          z14B2CPrime := AssignedCell.eval env.place env.env.toEnvironment input_var.z14B2CPrime } from by
        provable_type_simp] at h_input hA
    rw [h_input] at hA
    have hiak : AssignedCell.eval env.place env.env.toEnvironment input_var.ak = input.ak := congrArg Inputs.ak h_input
    have hia : AssignedCell.eval env.place env.env.toEnvironment input_var.a = input.a := congrArg Inputs.a h_input
    have hibWhole : AssignedCell.eval env.place env.env.toEnvironment input_var.bWhole = input.bWhole := congrArg Inputs.bWhole h_input
    have hib0 : AssignedCell.eval env.place env.env.toEnvironment input_var.b0 = input.b0 := congrArg Inputs.b0 h_input
    have hib2 : AssignedCell.eval env.place env.env.toEnvironment input_var.b2 = input.b2 := congrArg Inputs.b2 h_input
    have hiz13A : AssignedCell.eval env.place env.env.toEnvironment input_var.z13A = input.z13A := congrArg Inputs.z13A h_input
    have hiaPrime : AssignedCell.eval env.place env.env.toEnvironment input_var.aPrime = input.aPrime := congrArg Inputs.aPrime h_input
    have hiz13APrime : AssignedCell.eval env.place env.env.toEnvironment input_var.z13APrime = input.z13APrime := congrArg Inputs.z13APrime h_input
    have hInputNk : AssignedCell.eval env.place env.env.toEnvironment input_var.nk = input.nk :=
      congrArg Inputs.nk h_input
    have hic : AssignedCell.eval env.place env.env.toEnvironment input_var.c = input.c := congrArg Inputs.c h_input
    have hidWhole : AssignedCell.eval env.place env.env.toEnvironment input_var.dWhole = input.dWhole := congrArg Inputs.dWhole h_input
    have hid0 : AssignedCell.eval env.place env.env.toEnvironment input_var.d0 = input.d0 := congrArg Inputs.d0 h_input
    have hiz13C : AssignedCell.eval env.place env.env.toEnvironment input_var.z13C = input.z13C := congrArg Inputs.z13C h_input
    have hib2CPrime : AssignedCell.eval env.place env.env.toEnvironment input_var.b2CPrime = input.b2CPrime := congrArg Inputs.b2CPrime h_input
    have hiz14B2CPrime : AssignedCell.eval env.place env.env.toEnvironment input_var.z14B2CPrime = input.z14B2CPrime := congrArg Inputs.z14B2CPrime h_input
    have heqs := Gate.eqs_of_spec
      (toDonor input
        (env.env.advice (cfg.advices 4) ((env.place self + offset : ℕ) : ℤ))
        (env.env.advice (cfg.advices 4) ((env.place self + (offset + 1) : ℕ) : ℤ)))
      ⟨hA.1, hA.2.1, hA.2.2.1, hA.2.2.2.1, hA.2.2.2.2.1, hPA.2.2.1,
        hA.2.2.2.2.2.1, hA.2.2.2.2.2.2.1, hPA.1, hPA.2.2.2.1,
        hA.2.2.2.2.2.2.2.1, hA.2.2.2.2.2.2.2.2, hPA.2.1⟩
      hPA.2.2.2.2
    obtain ⟨hbb1, hbd1, he3, he4, he5, he6, he7, he8, he9, he10, he11, he12,
      he13, he14⟩ := heqs
    simp only [toDonor] at hbb1 hbd1 he3 he4 he5 he6 he7 he8 he9 he10 he11 he12 he13 he14
    rw [← hibWhole, ← hib0, ← hib2, ← hwb, ← hwb0, ← hwb2] at he3
    rw [← hidWhole, ← hid0, ← hwd, ← hwd0] at he4
    rw [← hia, ← hib0, ← hiak, ← hwa, ← hwb0, ← hwak] at he5
    rw [← hib2, ← hic, ← hid0, ← hInputNk, ← hwb2, ← hwc, ← hwd0, ← hwnk] at he6
    rw [← hib0, ← hwb0] at he7
    rw [← hiz13A, ← hwz13a] at he8
    rw [← hia, ← hiaPrime, ← hwa, ← hwap] at he9
    rw [← hiz13APrime, ← hwz13ap] at he10
    rw [← hid0, ← hwd0] at he11
    rw [← hiz13C, ← hwz13c] at he12
    rw [← hib2, ← hic, ← hib2CPrime, ← hwb2, ← hwc, ← hwb2cp] at he13
    rw [← hiz14B2CPrime, ← hwz14] at he14
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
      hwak, hwa, hwb, hwb0, hwb2, hwz13a, hwap, hwz13ap,
      hwnk, hwc, hwd, hwd0, hwz13c, hwb2cp, hwz14⟩
    · rcases hbb1 with h | h <;> rw [h] <;> ring
    · rcases hbd1 with h | h <;> rw [h] <;> ring
    · push_cast at he3 ⊢; linear_combination he3
    · push_cast at he4 ⊢; linear_combination he4
    · push_cast at he5 ⊢; linear_combination he5
    · push_cast at he6 ⊢; linear_combination he6
    · push_cast at he7 ⊢; linear_combination he7
    · push_cast at he8 ⊢; linear_combination he8
    · push_cast at he9 ⊢; linear_combination he9
    · push_cast at he10 ⊢; linear_combination he10
    · push_cast at he11 ⊢; linear_combination he11
    · push_cast at he12 ⊢; linear_combination he12
    · push_cast at he13 ⊢; linear_combination he13
    · push_cast at he14 ⊢; linear_combination he14

end Zcash.Circuits.CommitIvk
