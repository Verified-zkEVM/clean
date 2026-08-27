import Clean.Ironwood.NoteCommit.Gates
import Clean.Ironwood.NoteCommit.CanonicityTheorems

/-!
Reference (ported from actual Rust, not memory):
`orchard@0.14.0/src/circuit/note_commit.rs` — the input-canonicity `assign` regions
(`"NoteCommit input value"` 994-1035: pure copies of `value`/`d_2`/`d_3 = z1_d`/`e_0`).

The semantic contracts are the phase-1 gate specs (`Clean/Orchard/Action/Canonicity.lean`)
verbatim; the heavyweight canonicity value arguments are REUSED wholesale via the
donor-replay bridge: the donor `Gate.circuit` is a main-Clean `FormalAssertion` over the
same field equations, so applying its `soundness` at offset 0, a trivial environment and
const-lifted inputs turns the Ironwood-landed equations into the donor `Spec`.
-/

namespace Zcash.Circuits.NoteCommit

open Halo2

/-- `v·(1−v) = 0` pins a boolean. -/
private theorem isBool_of_boolCheck' {v : Fp} (h : v * (1 - v) = 0) : IsBool v := by
  rcases mul_eq_zero.mp h with h0 | h1
  · exact Or.inl h0
  · exact Or.inr (by linear_combination -h1)

namespace ValueCanonicity

private abbrev DRow := NoteCommit.ValueCanonicity.Gate.Row
private abbrev DSpec := NoteCommit.ValueCanonicity.Gate.Spec
private abbrev DAssumptions := NoteCommit.ValueCanonicity.Gate.Assumptions

structure Row (F : Type) where
  value : F
  d2 : F
  d3 : F
  e0 : F
deriving ProvableStruct

/-- The donor-side row record. -/
def toDonor (row : Row Fp) : DRow Fp :=
  { value := row.value, d2 := row.d2, d3 := row.d3, e0 := row.e0 }

def synthesisSummary (cfg : Config) (offset : ℕ) :
    FloorPlanner.RegionSynthesisSummary :=
  .ofColumns
    [.selector cfg.qNotecommitValue.index,
      .column .advice cfg.colL.index,
      .column .advice cfg.colM.index,
      .column .advice cfg.colR.index,
      .column .advice cfg.colZ.index]
    (offset + 1) 0

@[synthesis_summary_norm]
theorem synthesisSummary_hasNoFixedColumns (cfg : Config) (offset : ℕ) :
    (synthesisSummary cfg offset).HasNoFixedColumns := by
  unfold synthesisSummary
  rw [FloorPlanner.RegionSynthesisSummary.hasNoFixedColumns_ofColumns]
  simp

def bundleSynthesize (cfg : Config) (offset : ℕ)
    (input : Var Row Fp) : RegionCircuit Fp Unit := do
  (gate cfg).enable offset
  let _v ← copyAdvice input.value cfg.colL offset
  let _d2 ← copyAdvice input.d2 cfg.colM offset
  let _d3 ← copyAdvice input.d3 cfg.colR offset
  let _e0 ← copyAdvice input.e0 cfg.colZ offset
  pure ()

/-- Rust `ValueCanonicity::assign` (`note_commit.rs:994-1035`): pure copies. `Spec` is
the donor `ValueCanonicity.Gate.Spec` (canonical 64-bit value with its slices);
`Assumptions` the donor rely-conditions (the slices are range-checked). -/
def bundle : FormalRegionCircuit Fp Config Config Row unit where
  configure := pure
  synthesize := bundleSynthesize
  elaborated :=
    { keygenRequirements :=
        { gates cfg _ := [gate cfg]
          permutationColumns cfg _ :=
            [cfg.colL, cfg.colM, cfg.colR, cfg.colZ]
          inputCells _ _ input :=
            [input.value.cell, input.d2.cell, input.d3.cell, input.e0.cell] }
      copyCellsAssigned := by keygen_registration [bundleSynthesize]
      synthesisSummary cfg offset _ _ := ValueCanonicity.synthesisSummary cfg offset
      synthesisSummary_eq := by
        intro _ _ _ _
        apply FloorPlanner.RegionSynthesisSummary.ext
        · simp only [ValueCanonicity.synthesisSummary, bundleSynthesize, circuit_norm,
            synthesis_summary_norm]
        · simp only [ValueCanonicity.synthesisSummary, bundleSynthesize, circuit_norm,
            synthesis_summary_norm]
        · simp only [ValueCanonicity.synthesisSummary, bundleSynthesize, circuit_norm,
            synthesis_summary_norm]
        · simp only [ValueCanonicity.synthesisSummary, bundleSynthesize, circuit_norm,
            synthesis_summary_norm]
        · simp only [ValueCanonicity.synthesisSummary, bundleSynthesize, circuit_norm,
            synthesis_summary_norm] }
  Assumptions input := DAssumptions (toDonor input)

  Spec input _ _ := DSpec (toDonor input)

  ProverAssumptions input _ _ :=
    input.value = input.d2 + input.d3 * (2 ^ 8 : Fp) + input.e0 * (2 ^ 58 : Fp)

  soundness := by
    circuit_proof_start [gate]
    obtain ⟨heq, hcv, hcd2, hcd3, hce0⟩ := hc
    rw [hcv, hcd2, hcd3, hce0] at heq
    exact NoteCommit.ValueCanonicity.Gate.spec_of_eq
      ⟨input_value, input_d2, input_d3, input_e0⟩ hA
      (by push_cast; linear_combination heq)

  completeness := by
    circuit_proof_start [gate]
    linear_combination -hPA

@[synthesis_summary_norm]
theorem bundle_synthesisSummary_eq (cfg : Config) (offset : ℕ)
    (input : Var Row Fp) (region : RegionIndex) :
    bundle.elaborated.synthesisSummary cfg offset input region =
      synthesisSummary cfg offset := rfl

derive_contract_bridges bundle := bundle

end ValueCanonicity

namespace GdCanonicity

private abbrev DRow := NoteCommit.GdCanonicity.Gate.Row
private abbrev DSpec := NoteCommit.GdCanonicity.Gate.Spec
private abbrev DAssumptions := NoteCommit.GdCanonicity.Gate.Assumptions

structure Row (F : Type) where
  gdX : F
  b0 : F
  b1 : F
  a : F
  aPrime : F
  z13A : F
  z13APrime : F
deriving ProvableStruct

/-- The donor-side row record. -/
def toDonor (row : Row Fp) : DRow Fp :=
  ⟨row.gdX, row.b0, row.b1, row.a, row.aPrime, row.z13A, row.z13APrime⟩

def synthesisSummary (cfg : Config) (offset : ℕ) :
    FloorPlanner.RegionSynthesisSummary :=
  .ofColumns
    [.column .advice cfg.colL.index,
      .column .advice cfg.colM.index,
      .column .advice cfg.colM.index,
      .column .advice cfg.colR.index,
      .column .advice cfg.colR.index,
      .column .advice cfg.colZ.index,
      .column .advice cfg.colZ.index,
      .selector cfg.qNotecommitGd.index]
    (offset + 2) 0

@[synthesis_summary_norm]
theorem synthesisSummary_hasNoFixedColumns (cfg : Config) (offset : ℕ) :
    (synthesisSummary cfg offset).HasNoFixedColumns := by
  unfold synthesisSummary
  rw [FloorPlanner.RegionSynthesisSummary.hasNoFixedColumns_ofColumns]
  simp

def bundleSynthesize (cfg : Config) (offset : ℕ)
    (input : Var Row Fp) : RegionCircuit Fp Unit := do
  let _x ← copyAdvice input.gdX cfg.colL offset
  let _b0 ← copyAdvice input.b0 cfg.colM offset
  let _b1 ← copyAdvice input.b1 cfg.colM (offset + 1)
  let _a ← copyAdvice input.a cfg.colR offset
  let _ap ← copyAdvice input.aPrime cfg.colR (offset + 1)
  let _z ← copyAdvice input.z13A cfg.colZ offset
  let _zp ← copyAdvice input.z13APrime cfg.colZ (offset + 1)
  (gate cfg).enable offset
  pure ()

@[reducible]
def bundleElaborated :
    ElaboratedRegionCircuit Fp Config Config Row unit pure bundleSynthesize :=
  { keygenRequirements :=
      { gates cfg _ := [gate cfg]
        permutationColumns cfg _ :=
          [cfg.colL, cfg.colM, cfg.colR, cfg.colZ]
        inputCells _ _ input :=
          [input.gdX.cell, input.b0.cell, input.b1.cell, input.a.cell,
            input.aPrime.cell, input.z13A.cell, input.z13APrime.cell] }
    copyCellsAssigned := by keygen_registration [bundleSynthesize]
    synthesisSummary cfg offset _ _ := synthesisSummary cfg offset
    synthesisSummary_eq := by
      intro _ _ _ _
      apply FloorPlanner.RegionSynthesisSummary.ext
      · simp only [synthesisSummary, bundleSynthesize, circuit_norm,
          synthesis_summary_norm]
      · simp only [synthesisSummary, bundleSynthesize, circuit_norm,
          synthesis_summary_norm]
        omega
      · simp only [synthesisSummary, bundleSynthesize, circuit_norm,
          synthesis_summary_norm]
      · simp only [synthesisSummary, bundleSynthesize, circuit_norm,
          synthesis_summary_norm]
      · simp only [synthesisSummary, bundleSynthesize, circuit_norm,
          synthesis_summary_norm] }

/-- Rust `GdCanonicity::assign` (`note_commit.rs:789-841`): pure copies (rows 0/1 of
`col_l/m/r/z`), gate enabled at row 0. `Spec`/`Assumptions` are the donor
`GdCanonicity.Gate` contract; the canonicity value argument is the donor `spec_of_eqs`. -/
def bundle : FormalRegionCircuit Fp Config Config Row unit where
  configure := pure
  synthesize := bundleSynthesize
  elaborated := bundleElaborated

  -- input-only rely-conditions: the gate itself enforces the `a'` shift (constraint 2)
  Assumptions input := IsBool input.b1 ∧ input.a.val < 2 ^ 250 ∧
    input.b0.val < 2 ^ 4 ∧
    input.z13A = ((input.a.val / 2 ^ 130 : ℕ) : Fp) ∧
    ∃ lo : ℕ, lo < 2 ^ 130 ∧
      input.aPrime = ((lo : ℕ) : Fp) + ((2 ^ 130 : ℕ) : Fp) * input.z13APrime

  Spec input _ _ := DSpec (toDonor input)

  ProverAssumptions input _ _ := DSpec (toDonor input) ∧
    input.aPrime = input.a + ((2 ^ 130 : ℕ) : Fp) - tP

  soundness := by
    circuit_proof_start [gate]
    obtain ⟨hc1, hc2, hc3, hc4, hc5, hc6, hc7, hg1, hg2, hg3, hg4, hg5⟩ := hc
    rw [hc4, hc2, hc3, hc1] at hg1
    rw [hc4, hc5] at hg2
    rw [hc3, hc2] at hg3
    rw [hc3, hc6] at hg4
    rw [hc3, hc7] at hg5
    have haPrime : input_aPrime = input_a + ((2 ^ 130 : ℕ) : Fp) - tP := by
      push_cast at hg2 ⊢; linear_combination -hg2
    exact NoteCommit.GdCanonicity.Gate.spec_of_eqs
      ⟨input_gdX, input_b0, input_b1, input_a, input_aPrime, input_z13A,
        input_z13APrime⟩
      ⟨hA.1, hA.2.1, hA.2.2.1, haPrime, hA.2.2.2.1, hA.2.2.2.2⟩
      (by push_cast; linear_combination hg1) hg3 hg4 hg5

  completeness := by
    circuit_proof_start [gate]
    have heqs := NoteCommit.GdCanonicity.Gate.eqs_of_spec
      (toDonor { gdX := input_gdX, b0 := input_b0, b1 := input_b1, a := input_a,
                 aPrime := input_aPrime, z13A := input_z13A, z13APrime := input_z13APrime })
      ⟨hA.1, hA.2.1, hA.2.2.1, hPA.2, hA.2.2.2.1, hA.2.2.2.2⟩ hPA.1
    obtain ⟨he1, he2, he3, he4, he5⟩ := heqs
    simp only [toDonor] at he1 he2 he3 he4 he5
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · push_cast at he1 ⊢
      linear_combination he1
    · push_cast at he2 ⊢
      linear_combination he2
    · linear_combination he3
    · linear_combination he4
    · linear_combination he5

@[synthesis_summary_norm]
theorem bundle_synthesisSummary_eq (cfg : Config) (offset : ℕ)
    (input : Var Row Fp) (region : RegionIndex) :
    bundle.elaborated.synthesisSummary cfg offset input region =
      synthesisSummary cfg offset := rfl

derive_contract_bridges bundle := bundle

end GdCanonicity

namespace PkdCanonicity

private abbrev DRow := NoteCommit.PkdCanonicity.Gate.Row
private abbrev DSpec := NoteCommit.PkdCanonicity.Gate.Spec
private abbrev DAssumptions := NoteCommit.PkdCanonicity.Gate.Assumptions

structure Row (F : Type) where
  pkdX : F
  b3 : F
  d0 : F
  c : F
  b3CPrime : F
  z13C : F
  z14B3CPrime : F
deriving ProvableStruct

/-- The donor-side row record. -/
def toDonor (row : Row Fp) : DRow Fp :=
  ⟨row.pkdX, row.b3, row.d0, row.c, row.b3CPrime, row.z13C, row.z14B3CPrime⟩

def synthesisSummary (cfg : Config) (offset : ℕ) :
    FloorPlanner.RegionSynthesisSummary :=
  .ofColumns
    [.column .advice cfg.colL.index,
      .column .advice cfg.colM.index,
      .column .advice cfg.colM.index,
      .column .advice cfg.colR.index,
      .column .advice cfg.colR.index,
      .column .advice cfg.colZ.index,
      .column .advice cfg.colZ.index,
      .selector cfg.qNotecommitPkd.index]
    (offset + 2) 0

@[synthesis_summary_norm]
theorem synthesisSummary_hasNoFixedColumns (cfg : Config) (offset : ℕ) :
    (synthesisSummary cfg offset).HasNoFixedColumns := by
  unfold synthesisSummary
  rw [FloorPlanner.RegionSynthesisSummary.hasNoFixedColumns_ofColumns]
  simp

def bundleSynthesize (cfg : Config) (offset : ℕ)
    (input : Var Row Fp) : RegionCircuit Fp Unit := do
  let _x ← copyAdvice input.pkdX cfg.colL offset
  let _b3 ← copyAdvice input.b3 cfg.colM offset
  let _d0 ← copyAdvice input.d0 cfg.colM (offset + 1)
  let _c ← copyAdvice input.c cfg.colR offset
  let _ap ← copyAdvice input.b3CPrime cfg.colR (offset + 1)
  let _z ← copyAdvice input.z13C cfg.colZ offset
  let _zp ← copyAdvice input.z14B3CPrime cfg.colZ (offset + 1)
  (gate cfg).enable offset
  pure ()

theorem bundleSynthesisSummary_eq (cfg : Config) (offset : ℕ)
    (input : Var Row Fp) (self : RegionIndex) :
    synthesisSummary cfg offset =
      FloorPlanner.regionSynthesisSummary
        ((bundleSynthesize cfg offset input).operations self) := by
  apply FloorPlanner.RegionSynthesisSummary.ext
  · simp only [synthesisSummary, bundleSynthesize, circuit_norm,
      synthesis_summary_norm]
  · simp only [synthesisSummary, bundleSynthesize, circuit_norm,
      synthesis_summary_norm]
    omega
  · simp only [synthesisSummary, bundleSynthesize, circuit_norm,
      synthesis_summary_norm]
  · simp only [synthesisSummary, bundleSynthesize, circuit_norm,
      synthesis_summary_norm]
  · simp only [synthesisSummary, bundleSynthesize, circuit_norm,
      synthesis_summary_norm]

/-- Rust `PkdCanonicity::assign` (`note_commit.rs:789-841`): pure copies (rows 0/1 of
`col_l/m/r/z`), gate enabled at row 0. `Spec`/`Assumptions` are the donor
`PkdCanonicity.Gate` contract; the canonicity value argument is the donor `spec_of_eqs`. -/
def bundle : FormalRegionCircuit Fp Config Config Row unit where
  configure := pure
  synthesize := bundleSynthesize
  elaborated :=
    { keygenRequirements :=
        { gates cfg _ := [gate cfg]
          permutationColumns cfg _ :=
            [cfg.colL, cfg.colM, cfg.colR, cfg.colZ]
          inputCells _ _ input :=
            [input.pkdX.cell, input.b3.cell, input.d0.cell, input.c.cell,
              input.b3CPrime.cell, input.z13C.cell, input.z14B3CPrime.cell] }
      copyCellsAssigned := by keygen_registration [bundleSynthesize]
      synthesisSummary cfg offset _ _ := PkdCanonicity.synthesisSummary cfg offset
      synthesisSummary_eq := bundleSynthesisSummary_eq }
  -- input-only rely-conditions: the gate itself enforces the shift (constraint 2)
  Assumptions input := IsBool input.d0 ∧ input.c.val < 2 ^ 250 ∧
    input.b3.val < 2 ^ 4 ∧
    input.z13C = ((input.c.val / 2 ^ 130 : ℕ) : Fp) ∧
    ∃ lo : ℕ, lo < 2 ^ 140 ∧
      input.b3CPrime = ((lo : ℕ) : Fp) + ((2 ^ 140 : ℕ) : Fp) * input.z14B3CPrime

  Spec input _ _ := DSpec (toDonor input)

  ProverAssumptions input _ _ := DSpec (toDonor input) ∧
    input.b3CPrime = input.b3 + input.c * ((2 ^ 4 : ℕ) : Fp) + ((2 ^ 140 : ℕ) : Fp) - tP

  soundness := by
    circuit_proof_start [gate]
    obtain ⟨hc1, hc2, hc3, hc4, hc5, hc6, hc7, hg1, hg2, hg3, hg4⟩ := hc
    rw [hc4, hc2, hc3, hc1] at hg1
    rw [hc2, hc4, hc5] at hg2
    rw [hc3, hc6] at hg3
    rw [hc3, hc7] at hg4
    have hshift : input_b3CPrime = input_b3 + input_c * ((2 ^ 4 : ℕ) : Fp)
        + ((2 ^ 140 : ℕ) : Fp) - tP := by
      push_cast at hg2 ⊢; linear_combination -hg2
    exact NoteCommit.PkdCanonicity.Gate.spec_of_eqs
      ⟨input_pkdX, input_b3, input_d0, input_c, input_b3CPrime, input_z13C,
        input_z14B3CPrime⟩
      ⟨hA.1, hA.2.1, hA.2.2.1, hshift, hA.2.2.2.1, hA.2.2.2.2⟩
      (by push_cast; linear_combination hg1) hg3 hg4

  completeness := by
    circuit_proof_start [gate]
    have heqs := NoteCommit.PkdCanonicity.Gate.eqs_of_spec
      (toDonor { pkdX := input_pkdX, b3 := input_b3, d0 := input_d0, c := input_c,
                 b3CPrime := input_b3CPrime, z13C := input_z13C,
                 z14B3CPrime := input_z14B3CPrime })
      ⟨hA.1, hA.2.1, hA.2.2.1, hPA.2, hA.2.2.2.1, hA.2.2.2.2⟩ hPA.1
    obtain ⟨he1, he2, he3, he4⟩ := heqs
    simp only [toDonor] at he1 he2 he3 he4
    refine ⟨?_, ?_, ?_, ?_⟩
    · push_cast at he1 ⊢
      linear_combination he1
    · push_cast at he2 ⊢
      linear_combination he2
    · linear_combination he3
    · linear_combination he4

@[synthesis_summary_norm]
theorem bundle_synthesisSummary_eq (cfg : Config) (offset : ℕ)
    (input : Var Row Fp) (region : RegionIndex) :
    bundle.elaborated.synthesisSummary cfg offset input region =
      synthesisSummary cfg offset := rfl

derive_contract_bridges bundle := bundle

end PkdCanonicity

namespace RhoCanonicity

private abbrev DRow := NoteCommit.RhoCanonicity.Gate.Row
private abbrev DSpec := NoteCommit.RhoCanonicity.Gate.Spec
private abbrev DAssumptions := NoteCommit.RhoCanonicity.Gate.Assumptions

structure Row (F : Type) where
  rho : F
  e1 : F
  g0 : F
  f : F
  e1FPrime : F
  z13F : F
  z14E1FPrime : F
deriving ProvableStruct

/-- The donor-side row record. -/
def toDonor (row : Row Fp) : DRow Fp :=
  ⟨row.rho, row.e1, row.g0, row.f, row.e1FPrime, row.z13F, row.z14E1FPrime⟩

def synthesisSummary (cfg : Config) (offset : ℕ) :
    FloorPlanner.RegionSynthesisSummary :=
  .ofColumns
    [.column .advice cfg.colL.index,
      .column .advice cfg.colM.index,
      .column .advice cfg.colM.index,
      .column .advice cfg.colR.index,
      .column .advice cfg.colR.index,
      .column .advice cfg.colZ.index,
      .column .advice cfg.colZ.index,
      .selector cfg.qNotecommitRho.index]
    (offset + 2) 0

@[synthesis_summary_norm]
theorem synthesisSummary_hasNoFixedColumns (cfg : Config) (offset : ℕ) :
    (synthesisSummary cfg offset).HasNoFixedColumns := by
  unfold synthesisSummary
  rw [FloorPlanner.RegionSynthesisSummary.hasNoFixedColumns_ofColumns]
  simp

def bundleSynthesize (cfg : Config) (offset : ℕ)
    (input : Var Row Fp) : RegionCircuit Fp Unit := do
  let _x ← copyAdvice input.rho cfg.colL offset
  let _e1 ← copyAdvice input.e1 cfg.colM offset
  let _g0 ← copyAdvice input.g0 cfg.colM (offset + 1)
  let _f ← copyAdvice input.f cfg.colR offset
  let _ap ← copyAdvice input.e1FPrime cfg.colR (offset + 1)
  let _z ← copyAdvice input.z13F cfg.colZ offset
  let _zp ← copyAdvice input.z14E1FPrime cfg.colZ (offset + 1)
  (gate cfg).enable offset
  pure ()

theorem bundleSynthesisSummary_eq (cfg : Config) (offset : ℕ)
    (input : Var Row Fp) (self : RegionIndex) :
    synthesisSummary cfg offset =
      FloorPlanner.regionSynthesisSummary
        ((bundleSynthesize cfg offset input).operations self) := by
  apply FloorPlanner.RegionSynthesisSummary.ext
  · simp only [synthesisSummary, bundleSynthesize, circuit_norm,
      synthesis_summary_norm]
  · simp only [synthesisSummary, bundleSynthesize, circuit_norm,
      synthesis_summary_norm]
    omega
  · simp only [synthesisSummary, bundleSynthesize, circuit_norm,
      synthesis_summary_norm]
  · simp only [synthesisSummary, bundleSynthesize, circuit_norm,
      synthesis_summary_norm]
  · simp only [synthesisSummary, bundleSynthesize, circuit_norm,
      synthesis_summary_norm]

/-- Rust `RhoCanonicity::assign` (`note_commit.rs:789-841`): pure copies (rows 0/1 of
`col_l/m/r/z`), gate enabled at row 0. `Spec`/`Assumptions` are the donor
`RhoCanonicity.Gate` contract; the canonicity value argument is the donor `spec_of_eqs`. -/
def bundle : FormalRegionCircuit Fp Config Config Row unit where
  configure := pure
  synthesize := bundleSynthesize
  elaborated :=
    { keygenRequirements :=
        { gates cfg _ := [gate cfg]
          permutationColumns cfg _ :=
            [cfg.colL, cfg.colM, cfg.colR, cfg.colZ]
          inputCells _ _ input :=
            [input.rho.cell, input.e1.cell, input.g0.cell, input.f.cell,
              input.e1FPrime.cell, input.z13F.cell, input.z14E1FPrime.cell] }
      copyCellsAssigned := by keygen_registration [bundleSynthesize]
      synthesisSummary cfg offset _ _ := RhoCanonicity.synthesisSummary cfg offset
      synthesisSummary_eq := bundleSynthesisSummary_eq }
  -- input-only rely-conditions: the gate itself enforces the shift (constraint 2)
  Assumptions input := IsBool input.g0 ∧ input.f.val < 2 ^ 250 ∧
    input.e1.val < 2 ^ 4 ∧
    input.z13F = ((input.f.val / 2 ^ 130 : ℕ) : Fp) ∧
    ∃ lo : ℕ, lo < 2 ^ 140 ∧
      input.e1FPrime = ((lo : ℕ) : Fp) + ((2 ^ 140 : ℕ) : Fp) * input.z14E1FPrime

  Spec input _ _ := DSpec (toDonor input)

  ProverAssumptions input _ _ := DSpec (toDonor input) ∧
    input.e1FPrime = input.e1 + input.f * ((2 ^ 4 : ℕ) : Fp) + ((2 ^ 140 : ℕ) : Fp) - tP

  soundness := by
    circuit_proof_start [gate]
    obtain ⟨hc1, hc2, hc3, hc4, hc5, hc6, hc7, hg1, hg2, hg3, hg4⟩ := hc
    rw [hc4, hc2, hc3, hc1] at hg1
    rw [hc2, hc4, hc5] at hg2
    rw [hc3, hc6] at hg3
    rw [hc3, hc7] at hg4
    have hshift : input_e1FPrime = input_e1 + input_f * ((2 ^ 4 : ℕ) : Fp)
        + ((2 ^ 140 : ℕ) : Fp) - tP := by
      push_cast at hg2 ⊢; linear_combination -hg2
    exact NoteCommit.RhoCanonicity.Gate.spec_of_eqs
      ⟨input_rho, input_e1, input_g0, input_f, input_e1FPrime, input_z13F,
        input_z14E1FPrime⟩
      ⟨hA.1, hA.2.1, hA.2.2.1, hshift, hA.2.2.2.1, hA.2.2.2.2⟩
      (by push_cast; linear_combination hg1) hg3 hg4

  completeness := by
    circuit_proof_start [gate]
    have heqs := NoteCommit.RhoCanonicity.Gate.eqs_of_spec
      (toDonor { rho := input_rho, e1 := input_e1, g0 := input_g0, f := input_f,
                 e1FPrime := input_e1FPrime, z13F := input_z13F,
                 z14E1FPrime := input_z14E1FPrime })
      ⟨hA.1, hA.2.1, hA.2.2.1, hPA.2, hA.2.2.2.1, hA.2.2.2.2⟩ hPA.1
    obtain ⟨he1, he2, he3, he4⟩ := heqs
    simp only [toDonor] at he1 he2 he3 he4
    refine ⟨?_, ?_, ?_, ?_⟩
    · push_cast at he1 ⊢
      linear_combination he1
    · push_cast at he2 ⊢
      linear_combination he2
    · linear_combination he3
    · linear_combination he4

@[synthesis_summary_norm]
theorem bundle_synthesisSummary_eq (cfg : Config) (offset : ℕ)
    (input : Var Row Fp) (region : RegionIndex) :
    bundle.elaborated.synthesisSummary cfg offset input region =
      synthesisSummary cfg offset := rfl

derive_contract_bridges bundle := bundle

end RhoCanonicity

namespace PsiCanonicity

private abbrev DRow := NoteCommit.PsiCanonicity.Gate.Row
private abbrev DSpec := NoteCommit.PsiCanonicity.Gate.Spec
private abbrev DAssumptions := NoteCommit.PsiCanonicity.Gate.Assumptions

structure Row (F : Type) where
  psi : F
  h0 : F
  g1 : F
  h1 : F
  g2 : F
  g1G2Prime : F
  z13G : F
  z13G1G2Prime : F
deriving ProvableStruct

/-- The donor-side row record. -/
def toDonor (row : Row Fp) : DRow Fp :=
  ⟨row.psi, row.h0, row.g1, row.h1, row.g2, row.g1G2Prime, row.z13G, row.z13G1G2Prime⟩

def synthesisSummary (cfg : Config) (offset : ℕ) :
    FloorPlanner.RegionSynthesisSummary :=
  .ofColumns
    [.column .advice cfg.colL.index,
      .column .advice cfg.colL.index,
      .column .advice cfg.colM.index,
      .column .advice cfg.colM.index,
      .column .advice cfg.colR.index,
      .column .advice cfg.colR.index,
      .column .advice cfg.colZ.index,
      .column .advice cfg.colZ.index,
      .selector cfg.qNotecommitPsi.index]
    (offset + 2) 0

@[synthesis_summary_norm]
theorem synthesisSummary_hasNoFixedColumns (cfg : Config) (offset : ℕ) :
    (synthesisSummary cfg offset).HasNoFixedColumns := by
  unfold synthesisSummary
  rw [FloorPlanner.RegionSynthesisSummary.hasNoFixedColumns_ofColumns]
  simp

def bundleSynthesize (cfg : Config) (offset : ℕ)
    (input : Var Row Fp) : RegionCircuit Fp Unit := do
  let _p ← copyAdvice input.psi cfg.colL offset
  let _h0 ← copyAdvice input.h0 cfg.colL (offset + 1)
  let _g1 ← copyAdvice input.g1 cfg.colM offset
  let _h1 ← copyAdvice input.h1 cfg.colM (offset + 1)
  let _g2 ← copyAdvice input.g2 cfg.colR offset
  let _gp ← copyAdvice input.g1G2Prime cfg.colR (offset + 1)
  let _z ← copyAdvice input.z13G cfg.colZ offset
  let _zp ← copyAdvice input.z13G1G2Prime cfg.colZ (offset + 1)
  (gate cfg).enable offset
  pure ()

theorem bundleSynthesisSummary_eq (cfg : Config) (offset : ℕ)
    (input : Var Row Fp) (self : RegionIndex) :
    synthesisSummary cfg offset =
      FloorPlanner.regionSynthesisSummary
        ((bundleSynthesize cfg offset input).operations self) := by
  apply FloorPlanner.RegionSynthesisSummary.ext
  · simp only [synthesisSummary, bundleSynthesize, circuit_norm,
      synthesis_summary_norm]
  · simp only [synthesisSummary, bundleSynthesize, circuit_norm,
      synthesis_summary_norm]
    omega
  · simp only [synthesisSummary, bundleSynthesize, circuit_norm,
      synthesis_summary_norm]
  · simp only [synthesisSummary, bundleSynthesize, circuit_norm,
      synthesis_summary_norm]
  · simp only [synthesisSummary, bundleSynthesize, circuit_norm,
      synthesis_summary_norm]

/-- Rust `PsiCanonicity::assign` (`note_commit.rs:1240-1274`): pure copies (rows 0/1 of
`col_l/m/r/z`), gate enabled at row 0. `Spec`/`Assumptions` are the donor
`PsiCanonicity.Gate` contract. -/
def bundle : FormalRegionCircuit Fp Config Config Row unit where
  configure := pure
  synthesize := bundleSynthesize
  elaborated :=
    { keygenRequirements :=
        { gates cfg _ := [gate cfg]
          permutationColumns cfg _ :=
            [cfg.colL, cfg.colM, cfg.colR, cfg.colZ]
          inputCells _ _ input :=
            [input.psi.cell, input.h0.cell, input.g1.cell, input.h1.cell,
              input.g2.cell, input.g1G2Prime.cell, input.z13G.cell,
              input.z13G1G2Prime.cell] }
      copyCellsAssigned := by keygen_registration [bundleSynthesize]
      synthesisSummary cfg offset _ _ := PsiCanonicity.synthesisSummary cfg offset
      synthesisSummary_eq := bundleSynthesisSummary_eq }
  -- input-only rely-conditions: the gate itself enforces the shift (constraint 2)
  Assumptions input := IsBool input.h1 ∧ input.g1.val < 2 ^ 9 ∧
    input.g2.val < 2 ^ 240 ∧ input.h0.val < 2 ^ 5 ∧
    input.z13G = (((input.g1.val + input.g2.val * 2 ^ 9) / 2 ^ 129 : ℕ) : Fp) ∧
    ∃ lo : ℕ, lo < 2 ^ 130 ∧
      input.g1G2Prime = ((lo : ℕ) : Fp) + ((2 ^ 130 : ℕ) : Fp) * input.z13G1G2Prime

  Spec input _ _ := DSpec (toDonor input)

  ProverAssumptions input _ _ := DSpec (toDonor input) ∧
    input.g1G2Prime = input.g1 + input.g2 * ((2 ^ 9 : ℕ) : Fp)
      + ((2 ^ 130 : ℕ) : Fp) - tP

  soundness := by
    circuit_proof_start [gate]
    obtain ⟨hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hg1, hg2, hg3, hg4, hg5⟩ := hc
    rw [hc3, hc5, hc2, hc4, hc1] at hg1
    rw [hc3, hc5, hc6] at hg2
    rw [hc4, hc2] at hg3
    rw [hc4, hc7] at hg4
    rw [hc4, hc8] at hg5
    have hshift : input_g1G2Prime = input_g1 + input_g2 * ((2 ^ 9 : ℕ) : Fp)
        + ((2 ^ 130 : ℕ) : Fp) - tP := by
      push_cast at hg2 ⊢; linear_combination -hg2
    exact NoteCommit.PsiCanonicity.Gate.spec_of_eqs
      ⟨input_psi, input_h0, input_g1, input_h1, input_g2, input_g1G2Prime, input_z13G,
        input_z13G1G2Prime⟩
      ⟨hA.1, hA.2.1, hA.2.2.1, hA.2.2.2.1, hshift, hA.2.2.2.2.1, hA.2.2.2.2.2⟩
      (by push_cast; linear_combination hg1) hg3 hg4 hg5

  completeness := by
    circuit_proof_start [gate]
    have heqs := NoteCommit.PsiCanonicity.Gate.eqs_of_spec
      (toDonor { psi := input_psi, h0 := input_h0, g1 := input_g1, h1 := input_h1,
                 g2 := input_g2, g1G2Prime := input_g1G2Prime, z13G := input_z13G,
                 z13G1G2Prime := input_z13G1G2Prime })
      ⟨hA.1, hA.2.1, hA.2.2.1, hA.2.2.2.1, hPA.2, hA.2.2.2.2.1, hA.2.2.2.2.2⟩ hPA.1
    obtain ⟨he1, he2, he3, he4, he5⟩ := heqs
    simp only [toDonor] at he1 he2 he3 he4 he5
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · push_cast at he1 ⊢
      linear_combination he1
    · push_cast at he2 ⊢
      linear_combination he2
    · linear_combination he3
    · linear_combination he4
    · linear_combination he5

@[synthesis_summary_norm]
theorem bundle_synthesisSummary_eq (cfg : Config) (offset : ℕ)
    (input : Var Row Fp) (region : RegionIndex) :
    bundle.elaborated.synthesisSummary cfg offset input region =
      synthesisSummary cfg offset := rfl

derive_contract_bridges bundle := bundle

end PsiCanonicity

namespace YCanonicity

private abbrev DRow := NoteCommit.YCanonicity.Gate.Row
private abbrev DSpec := NoteCommit.YCanonicity.Gate.Spec
private abbrev DAssumptions := NoteCommit.YCanonicity.Gate.Assumptions

/-- The copied-in cells (the `lsb`/`k_3` sign bits are witnessed in-region). -/
structure Row (F : Type) where
  y : F
  k0 : F
  k2 : F
  j : F
  z1J : F
  z13J : F
  jPrime : F
  z13JPrime : F
deriving ProvableStruct

/-- The donor-side row at the witnessed `(lsb, k3)` pair. -/
def toDonor (row : Row Fp) (lsb k3 : Fp) : DRow Fp :=
  ⟨row.y, lsb, row.k0, row.k2, k3, row.j, row.z1J, row.z13J, row.jPrime,
    row.z13JPrime⟩

def synthesisSummary (cfg : Config) (offset : ℕ) :
    FloorPlanner.RegionSynthesisSummary :=
  .ofColumns
    [.selector cfg.qYCanon.index,
      .column .advice (cfg.advices 5).index,
      .column .advice (cfg.advices 6).index,
      .column .advice (cfg.advices 7).index,
      .column .advice (cfg.advices 8).index,
      .column .advice (cfg.advices 9).index,
      .column .advice (cfg.advices 5).index,
      .column .advice (cfg.advices 6).index,
      .column .advice (cfg.advices 7).index,
      .column .advice (cfg.advices 8).index,
      .column .advice (cfg.advices 9).index]
    (offset + 2) 0

@[synthesis_summary_norm]
theorem synthesisSummary_hasNoFixedColumns (cfg : Config) (offset : ℕ) :
    (synthesisSummary cfg offset).HasNoFixedColumns := by
  unfold synthesisSummary
  rw [FloorPlanner.RegionSynthesisSummary.hasNoFixedColumns_ofColumns]
  simp

def bundleSynthesize (wlsb wk3 : WitgenIR Fp 1) (cfg : Config) (offset : ℕ)
    (input : Var Row Fp) : RegionCircuit Fp (Var field Fp) := do
  (gate cfg).enable offset
  let _y ← copyAdvice input.y (cfg.advices 5) offset
  let lsb ← assignAdvice (cfg.advices 6) offset wlsb
  let _k0 ← copyAdvice input.k0 (cfg.advices 7) offset
  let _k2 ← copyAdvice input.k2 (cfg.advices 8) offset
  let _k3 ← assignAdvice (cfg.advices 9) offset wk3
  let _j ← copyAdvice input.j (cfg.advices 5) (offset + 1)
  let _z1 ← copyAdvice input.z1J (cfg.advices 6) (offset + 1)
  let _z13 ← copyAdvice input.z13J (cfg.advices 7) (offset + 1)
  let _jp ← copyAdvice input.jPrime (cfg.advices 8) (offset + 1)
  let _z13p ← copyAdvice input.z13JPrime (cfg.advices 9) (offset + 1)
  pure lsb

@[circuit_norm]
theorem bundleSynthesize_output (wlsb wk3 : WitgenIR Fp 1)
    (cfg : Config) (offset : ℕ) (input : Var Row Fp) (self : RegionIndex) :
    (bundleSynthesize wlsb wk3 cfg offset input).output self =
      AssignedCell.of self offset (cfg.advices 6) := by
  simp only [bundleSynthesize, circuit_norm]

theorem bundleSynthesisSummary_eq (wlsb wk3 : WitgenIR Fp 1)
    (cfg : Config) (offset : ℕ) (input : Var Row Fp) (self : RegionIndex) :
    synthesisSummary cfg offset =
      FloorPlanner.regionSynthesisSummary
        ((bundleSynthesize wlsb wk3 cfg offset input).operations self) := by
  apply FloorPlanner.RegionSynthesisSummary.ext
  · simp only [synthesisSummary, bundleSynthesize, circuit_norm,
      synthesis_summary_norm]
  · simp only [synthesisSummary, bundleSynthesize, circuit_norm,
      synthesis_summary_norm]
    omega
  · simp only [synthesisSummary, bundleSynthesize, circuit_norm,
      synthesis_summary_norm]
  · simp only [synthesisSummary, bundleSynthesize, circuit_norm,
      synthesis_summary_norm]
  · simp only [synthesisSummary, bundleSynthesize, circuit_norm,
      synthesis_summary_norm]

/-- Rust `YCanonicity::assign` (`note_commit.rs:1345-1409`): `q_y_canon` at row 0; row 0
copies `y`/`k_0`/`k_2` and witnesses `LSB`/`k_3` (the `wlsb`/`wk3` programs); row 1 copies
`j`/`z1_j`/`z13_j`/`j_prime`/`z13_j_prime`. Output is the witnessed `lsb` cell; the
`(lsb, k3)` readings are the extraction data. `Spec` is the donor `YCanonicity.Gate.Spec`
CONDITIONED on the output's booleanity — as in Rust, the lsb cell is boolean-constrained
*outside* this gate (the decompose gates' `bool_check` on the copied cell), so the
composite threads it back as a rely. -/
def bundle (wlsb wk3 : WitgenIR Fp 1) :
    FormalRegionCircuit Fp Config Config Row field where
  configure := pure
  synthesize := bundleSynthesize wlsb wk3
  elaborated :=
    { keygenRequirements :=
        { gates cfg _ := [gate cfg]
          permutationColumns cfg _ :=
            [cfg.advices 5, cfg.advices 6, cfg.advices 7,
              cfg.advices 8, cfg.advices 9]
          inputCells _ _ input :=
            [input.y.cell, input.k0.cell, input.k2.cell, input.j.cell,
              input.z1J.cell, input.z13J.cell, input.jPrime.cell,
              input.z13JPrime.cell] }
      copyCellsAssigned := by keygen_registration [bundleSynthesize]
      synthesisSummary cfg offset _ _ := YCanonicity.synthesisSummary cfg offset
      synthesisSummary_eq := bundleSynthesisSummary_eq wlsb wk3 }
  Witness := fieldPair
  extract cfg offset _ self env :=
    (eval env (AssignedCell.of self offset (cfg.advices 6) : Var field Fp),
     eval env (AssignedCell.of self offset (cfg.advices 9) : Var field Fp))

  -- the input-only rely-conditions (donor `Assumptions` minus `IsBool lsb`)
  -- input-only rely-conditions: the gate itself enforces the `j'` shift (constraint 4)
  Assumptions input :=
    input.j.val < 2 ^ 250 ∧ input.k0.val < 2 ^ 9 ∧ input.k2.val < 2 ^ 4 ∧
    input.z1J.val = input.j.val / 2 ^ 10 ∧
    input.z13J.val = input.j.val / 2 ^ 130 ∧
    ∃ lo : ℕ, lo < 2 ^ 130 ∧
      input.jPrime = ((lo : ℕ) : Fp) + ((2 ^ 130 : ℕ) : Fp) * input.z13JPrime

  Spec := fun input (out : Fp) (wit : Fp × Fp) =>
    out = wit.1 ∧ (IsBool out → DSpec (toDonor input out wit.2))

  ProverAssumptions := fun input (wit : Fp × Fp) _ =>
    IsBool wit.1 ∧ DSpec (toDonor input wit.1 wit.2) ∧
    input.jPrime = input.j + ((2 ^ 130 : ℕ) : Fp) - tP

  ProverSpec := fun _ (out : Fp) (wit : Fp × Fp) _ => out = wit.1

  soundness := by
    circuit_proof_start [gate, boolCheck]
    obtain ⟨⟨hk3c, hjdec, hyc, hjpc, hg1, hg2, hg3⟩,
      hcy, hck0, hck2, hcj, hcz1, hcz13, hcjp, hcz13p⟩ := hc
    rw [hcj, hck0, hcz1] at hjdec
    rw [hcy, hcj, hck2] at hyc
    rw [hck2] at hg1
    rw [hcj, hcjp] at hjpc
    rw [hcz13p] at hg3
    have hjP : input_jPrime = input_j + ((2 ^ 130 : ℕ) : Fp) - tP := by
      push_cast at hjpc ⊢; linear_combination -hjpc
    have hidx : ((place self + offset : ℕ) : ℤ)
        = ((place self : ℕ) : ℤ) + ((offset : ℕ) : ℤ) := by push_cast; ring
    rw [hidx] at hk3c hyc hg1 hg3
    exact ⟨trivial, fun hbool =>
      NoteCommit.YCanonicity.Gate.spec_of_eqs
        (toDonor ⟨input_y, input_k0, input_k2, input_j, input_z1J, input_z13J,
          input_jPrime, input_z13JPrime⟩ _ _)
        ⟨hbool, hA.1, hA.2.1, hA.2.2.1, hjP, hA.2.2.2.1,
          hA.2.2.2.2.1, hA.2.2.2.2.2⟩
        (isBool_of_boolCheck' hk3c)
        (by simp only [toDonor]; linear_combination hjdec)
        (by simp only [toDonor]; push_cast at hyc ⊢; linear_combination hyc)
        (by simp only [toDonor]; push_cast at hg1 ⊢; linear_combination hg1)
        (by simp only [toDonor]; push_cast at hg3 ⊢; linear_combination hg3)⟩

  completeness := by
    circuit_proof_start [gate, boolCheck]
    have heqs := NoteCommit.YCanonicity.Gate.eqs_of_spec
      (toDonor { y := input_y, k0 := input_k0, k2 := input_k2, j := input_j,
                 z1J := input_z1J, z13J := input_z13J, jPrime := input_jPrime,
                 z13JPrime := input_z13JPrime }
        (Witgen.WitgenIROver.eval wlsb ⟨place, env⟩)[0]
        (Witgen.WitgenIROver.eval wk3 ⟨place, env⟩)[0])
      ⟨hPA.1, hA.1, hA.2.1, hA.2.2.1, hPA.2.2, hA.2.2.2.1,
        hA.2.2.2.2.1, hA.2.2.2.2.2⟩ hPA.2.1
    obtain ⟨hb, he2, he3, he4, he5, he6, he7⟩ := heqs
    simp only [toDonor] at hb he2 he3 he4 he5 he6 he7
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, h_output.symm⟩
    · rcases hb with h | h <;> rw [h] <;> ring
    · linear_combination he2
    · push_cast at he3 ⊢
      linear_combination he3
    · push_cast at he4 ⊢
      linear_combination he4
    · linear_combination he5
    · linear_combination he6
    · linear_combination he7

@[synthesis_summary_norm]
theorem bundle_synthesisSummary_eq (wlsb wk3 : WitgenIR Fp 1)
    (cfg : Config) (offset : ℕ) (input : Var Row Fp)
    (region : RegionIndex) :
    (bundle wlsb wk3).elaborated.synthesisSummary cfg offset input region =
      synthesisSummary cfg offset := rfl

derive_contract_bridges bundle (wlsb wk3 : WitgenIR Fp 1) := bundle wlsb wk3

end YCanonicity

@[synthesis_summary_norm]
theorem ValueCanonicity.synthesisSummary_lookupActivationCount
    (cfg : ValueCanonicity.Config) (offset : ℕ) :
    (ValueCanonicity.synthesisSummary cfg offset).lookupActivationCount = 0 := by
  simp only [ValueCanonicity.synthesisSummary, synthesis_summary_norm]

@[synthesis_summary_norm]
theorem GdCanonicity.synthesisSummary_lookupActivationCount
    (cfg : GdCanonicity.Config) (offset : ℕ) :
    (GdCanonicity.synthesisSummary cfg offset).lookupActivationCount = 0 := by
  simp only [GdCanonicity.synthesisSummary, synthesis_summary_norm]

@[synthesis_summary_norm]
theorem PkdCanonicity.synthesisSummary_lookupActivationCount
    (cfg : PkdCanonicity.Config) (offset : ℕ) :
    (PkdCanonicity.synthesisSummary cfg offset).lookupActivationCount = 0 := by
  simp only [PkdCanonicity.synthesisSummary, synthesis_summary_norm]

@[synthesis_summary_norm]
theorem RhoCanonicity.synthesisSummary_lookupActivationCount
    (cfg : RhoCanonicity.Config) (offset : ℕ) :
    (RhoCanonicity.synthesisSummary cfg offset).lookupActivationCount = 0 := by
  simp only [RhoCanonicity.synthesisSummary, synthesis_summary_norm]

@[synthesis_summary_norm]
theorem PsiCanonicity.synthesisSummary_lookupActivationCount
    (cfg : PsiCanonicity.Config) (offset : ℕ) :
    (PsiCanonicity.synthesisSummary cfg offset).lookupActivationCount = 0 := by
  simp only [PsiCanonicity.synthesisSummary, synthesis_summary_norm]

@[synthesis_summary_norm]
theorem YCanonicity.synthesisSummary_lookupActivationCount
    (cfg : YCanonicity.Config) (offset : ℕ) :
    (YCanonicity.synthesisSummary cfg offset).lookupActivationCount = 0 := by
  simp only [YCanonicity.synthesisSummary, synthesis_summary_norm]

end Zcash.Circuits.NoteCommit
