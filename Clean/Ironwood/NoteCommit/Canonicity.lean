import Clean.Ironwood.NoteCommit.Gates
import Clean.Orchard.Action.Canonicity

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

namespace Halo2.Ironwood.NoteCommit

open Halo2.Ironwood (Fp)

/-- `v·(1−v) = 0` pins a boolean. -/
private theorem isBool_of_boolCheck' {v : Fp} (h : v * (1 - v) = 0) : IsBool v := by
  rcases mul_eq_zero.mp h with h0 | h1
  · exact Or.inl h0
  · exact Or.inr (by linear_combination -h1)

namespace ValueCanonicity

private abbrev DRow := Orchard.Action.NoteCommit.ValueCanonicity.Gate.Row
private abbrev DSpec := Orchard.Action.NoteCommit.ValueCanonicity.Gate.Spec
private abbrev DAssumptions := Orchard.Action.NoteCommit.ValueCanonicity.Gate.Assumptions
private abbrev DCircuit := Orchard.Action.NoteCommit.ValueCanonicity.Gate.circuit

structure Row (F : Type) where
  value : F
  d2 : F
  d3 : F
  e0 : F
deriving ProvableStruct

/-- The donor-side row record. -/
def toDonor (row : Row Fp) : DRow Fp :=
  { value := row.value, d2 := row.d2, d3 := row.d3, e0 := row.e0 }

/-- Rust `ValueCanonicity::assign` (`note_commit.rs:994-1035`): pure copies. `Spec` is
the donor `ValueCanonicity.Gate.Spec` (canonical 64-bit value with its slices);
`Assumptions` the donor rely-conditions (the slices are range-checked). -/
def bundle : FormalRegionCircuit Fp Config Config Row unit where
  configure := pure

  synthesize cfg offset (input : Row (AssignedCell Fp)) := do
    (gate cfg).enable offset
    let _v ← copyAdvice input.value cfg.colL offset
    let _d2 ← copyAdvice input.d2 cfg.colM offset
    let _d3 ← copyAdvice input.d3 cfg.colR offset
    let _e0 ← copyAdvice input.e0 cfg.colZ offset
    pure ()

  Assumptions input := DAssumptions (toDonor input)

  Spec input _ _ := DSpec (toDonor input)

  ProverAssumptions input _ _ :=
    input.value = input.d2 + input.d3 * (2 ^ 8 : Fp) + input.e0 * (2 ^ 58 : Fp)

  soundness := by
    circuit_proof_start [gate]
    obtain ⟨heq, hcv, hcd2, hcd3, hce0⟩ := hc
    rw [hcv, hcd2, hcd3, hce0] at heq
    exact Orchard.Action.NoteCommit.ValueCanonicity.Gate.spec_of_eq
      ⟨input_value, input_d2, input_d3, input_e0⟩ hA
      (by push_cast; linear_combination heq)

  completeness := by
    intro cfg offset
    rw [FormalRegionCircuit.completeness_iff]
    intro self env input_var input output h_input h_output hwit _hE hA hPA
    simp only [circuit_norm, gate] at hwit h_input h_output hPA ⊢
    obtain ⟨hwv, hwd2, hwd3, hwe0⟩ := hwit
    rw [show (ProvableStruct.eval env.place env.env.toEnvironment input_var
        : Row Fp)
      = { value := env.env.get input_var.value.cell.column
            ((env.place input_var.value.cell.regionIndex
              + input_var.value.cell.rowOffset : ℕ) : ℤ),
          d2 := env.env.get input_var.d2.cell.column
            ((env.place input_var.d2.cell.regionIndex
              + input_var.d2.cell.rowOffset : ℕ) : ℤ),
          d3 := env.env.get input_var.d3.cell.column
            ((env.place input_var.d3.cell.regionIndex
              + input_var.d3.cell.rowOffset : ℕ) : ℤ),
          e0 := env.env.get input_var.e0.cell.column
            ((env.place input_var.e0.cell.regionIndex
              + input_var.e0.cell.rowOffset : ℕ) : ℤ) } from by
        with_unfolding_all rfl] at h_input
    have hiv : env.env.get input_var.value.cell.column
        ((env.place input_var.value.cell.regionIndex
          + input_var.value.cell.rowOffset : ℕ) : ℤ) = input.value :=
      congrArg Row.value h_input
    have hid2 : env.env.get input_var.d2.cell.column
        ((env.place input_var.d2.cell.regionIndex
          + input_var.d2.cell.rowOffset : ℕ) : ℤ) = input.d2 :=
      congrArg Row.d2 h_input
    have hid3 : env.env.get input_var.d3.cell.column
        ((env.place input_var.d3.cell.regionIndex
          + input_var.d3.cell.rowOffset : ℕ) : ℤ) = input.d3 :=
      congrArg Row.d3 h_input
    have hie0 : env.env.get input_var.e0.cell.column
        ((env.place input_var.e0.cell.regionIndex
          + input_var.e0.cell.rowOffset : ℕ) : ℤ) = input.e0 :=
      congrArg Row.e0 h_input
    rw [← hiv, ← hid2, ← hid3, ← hie0, ← hwv, ← hwd2, ← hwd3, ← hwe0] at hPA
    exact ⟨by linear_combination -hPA, hwv, hwd2, hwd3, hwe0⟩

end ValueCanonicity

namespace GdCanonicity

private abbrev DRow := Orchard.Action.NoteCommit.GdCanonicity.Gate.Row
private abbrev DSpec := Orchard.Action.NoteCommit.GdCanonicity.Gate.Spec
private abbrev DAssumptions := Orchard.Action.NoteCommit.GdCanonicity.Gate.Assumptions

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

/-- Rust `GdCanonicity::assign` (`note_commit.rs:789-841`): pure copies (rows 0/1 of
`col_l/m/r/z`), gate enabled at row 0. `Spec`/`Assumptions` are the donor
`GdCanonicity.Gate` contract; the canonicity value argument is the donor `spec_of_eqs`. -/
def bundle : FormalRegionCircuit Fp Config Config Row unit where
  configure := pure

  synthesize cfg offset (input : Row (AssignedCell Fp)) := do
    let _x ← copyAdvice input.gdX cfg.colL offset
    let _b0 ← copyAdvice input.b0 cfg.colM offset
    let _b1 ← copyAdvice input.b1 cfg.colM (offset + 1)
    let _a ← copyAdvice input.a cfg.colR offset
    let _ap ← copyAdvice input.aPrime cfg.colR (offset + 1)
    let _z ← copyAdvice input.z13A cfg.colZ offset
    let _zp ← copyAdvice input.z13APrime cfg.colZ (offset + 1)
    (gate cfg).enable offset
    pure ()

  -- input-only rely-conditions: the gate itself enforces the `a'` shift (constraint 2)
  Assumptions input := IsBool input.b1 ∧ input.a.val < 2 ^ 250 ∧
    input.b0.val < 2 ^ 4 ∧
    input.z13A = ((input.a.val / 2 ^ 130 : ℕ) : Fp) ∧
    ∃ lo : ℕ, lo < 2 ^ 130 ∧
      input.aPrime = ((lo : ℕ) : Fp) + ((2 ^ 130 : ℕ) : Fp) * input.z13APrime

  Spec input _ _ := DSpec (toDonor input)

  ProverAssumptions input _ _ := DSpec (toDonor input) ∧
    input.aPrime = input.a + ((2 ^ 130 : ℕ) : Fp) - Orchard.tP

  soundness := by
    circuit_proof_start [gate]
    obtain ⟨hc1, hc2, hc3, hc4, hc5, hc6, hc7, hg1, hg2, hg3, hg4, hg5⟩ := hc
    rw [hc4, hc2, hc3, hc1] at hg1
    rw [hc4, hc5] at hg2
    rw [hc3, hc2] at hg3
    rw [hc3, hc6] at hg4
    rw [hc3, hc7] at hg5
    have haPrime : input_aPrime = input_a + ((2 ^ 130 : ℕ) : Fp) - Orchard.tP := by
      push_cast at hg2 ⊢; linear_combination -hg2
    exact Orchard.Action.NoteCommit.GdCanonicity.Gate.spec_of_eqs
      ⟨input_gdX, input_b0, input_b1, input_a, input_aPrime, input_z13A,
        input_z13APrime⟩
      ⟨hA.1, hA.2.1, hA.2.2.1, haPrime, hA.2.2.2.1, hA.2.2.2.2⟩
      (by push_cast; linear_combination hg1) hg3 hg4 hg5

  completeness := by
    intro cfg offset
    rw [FormalRegionCircuit.completeness_iff]
    intro self env input_var input output h_input h_output hwit _hE hA hPA
    simp only [circuit_norm, gate] at hwit h_input h_output hA hPA ⊢
    obtain ⟨hw1, hw2, hw3, hw4, hw5, hw6, hw7⟩ := hwit
    rw [show (ProvableStruct.eval env.place env.env.toEnvironment input_var
        : Row Fp)
      = { gdX := env.env.get input_var.gdX.cell.column
            ((env.place input_var.gdX.cell.regionIndex
              + input_var.gdX.cell.rowOffset : ℕ) : ℤ),
          b0 := env.env.get input_var.b0.cell.column
            ((env.place input_var.b0.cell.regionIndex
              + input_var.b0.cell.rowOffset : ℕ) : ℤ),
          b1 := env.env.get input_var.b1.cell.column
            ((env.place input_var.b1.cell.regionIndex
              + input_var.b1.cell.rowOffset : ℕ) : ℤ),
          a := env.env.get input_var.a.cell.column
            ((env.place input_var.a.cell.regionIndex
              + input_var.a.cell.rowOffset : ℕ) : ℤ),
          aPrime := env.env.get input_var.aPrime.cell.column
            ((env.place input_var.aPrime.cell.regionIndex
              + input_var.aPrime.cell.rowOffset : ℕ) : ℤ),
          z13A := env.env.get input_var.z13A.cell.column
            ((env.place input_var.z13A.cell.regionIndex
              + input_var.z13A.cell.rowOffset : ℕ) : ℤ),
          z13APrime := env.env.get input_var.z13APrime.cell.column
            ((env.place input_var.z13APrime.cell.regionIndex
              + input_var.z13APrime.cell.rowOffset : ℕ) : ℤ) } from by
        with_unfolding_all rfl] at h_input hA
    rw [h_input] at hA
    have higdX : env.env.get input_var.gdX.cell.column
        ((env.place input_var.gdX.cell.regionIndex
          + input_var.gdX.cell.rowOffset : ℕ) : ℤ) = input.gdX := congrArg Row.gdX h_input
    have hib0 : env.env.get input_var.b0.cell.column
        ((env.place input_var.b0.cell.regionIndex
          + input_var.b0.cell.rowOffset : ℕ) : ℤ) = input.b0 := congrArg Row.b0 h_input
    have hib1 : env.env.get input_var.b1.cell.column
        ((env.place input_var.b1.cell.regionIndex
          + input_var.b1.cell.rowOffset : ℕ) : ℤ) = input.b1 := congrArg Row.b1 h_input
    have hia : env.env.get input_var.a.cell.column
        ((env.place input_var.a.cell.regionIndex
          + input_var.a.cell.rowOffset : ℕ) : ℤ) = input.a := congrArg Row.a h_input
    have hiaPrime : env.env.get input_var.aPrime.cell.column
        ((env.place input_var.aPrime.cell.regionIndex
          + input_var.aPrime.cell.rowOffset : ℕ) : ℤ) = input.aPrime := congrArg Row.aPrime h_input
    have hiz13A : env.env.get input_var.z13A.cell.column
        ((env.place input_var.z13A.cell.regionIndex
          + input_var.z13A.cell.rowOffset : ℕ) : ℤ) = input.z13A := congrArg Row.z13A h_input
    have hiz13APrime : env.env.get input_var.z13APrime.cell.column
        ((env.place input_var.z13APrime.cell.regionIndex
          + input_var.z13APrime.cell.rowOffset : ℕ) : ℤ) = input.z13APrime := congrArg Row.z13APrime h_input
    have heqs := Orchard.Action.NoteCommit.GdCanonicity.Gate.eqs_of_spec
      (toDonor input) ⟨hA.1, hA.2.1, hA.2.2.1, hPA.2, hA.2.2.2.1, hA.2.2.2.2⟩ hPA.1
    obtain ⟨he1, he2, he3, he4, he5⟩ := heqs
    simp only [toDonor] at he1 he2 he3 he4 he5
    rw [← higdX, ← hib0, ← hib1, ← hia, ← hw1, ← hw2, ← hw3, ← hw4] at he1
    rw [← hia, ← hiaPrime, ← hw4, ← hw5] at he2
    rw [← hib1, ← hib0, ← hw3, ← hw2] at he3
    rw [← hib1, ← hiz13A, ← hw3, ← hw6] at he4
    rw [← hib1, ← hiz13APrime, ← hw3, ← hw7] at he5
    refine ⟨hw1, hw2, hw3, hw4, hw5, hw6, hw7, ?_, ?_, ?_, ?_, ?_⟩
    · push_cast at he1 ⊢
      linear_combination he1
    · push_cast at he2 ⊢
      linear_combination he2
    · linear_combination he3
    · linear_combination he4
    · linear_combination he5

end GdCanonicity

namespace PkdCanonicity

private abbrev DRow := Orchard.Action.NoteCommit.PkdCanonicity.Gate.Row
private abbrev DSpec := Orchard.Action.NoteCommit.PkdCanonicity.Gate.Spec
private abbrev DAssumptions := Orchard.Action.NoteCommit.PkdCanonicity.Gate.Assumptions

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

/-- Rust `PkdCanonicity::assign` (`note_commit.rs:789-841`): pure copies (rows 0/1 of
`col_l/m/r/z`), gate enabled at row 0. `Spec`/`Assumptions` are the donor
`PkdCanonicity.Gate` contract; the canonicity value argument is the donor `spec_of_eqs`. -/
def bundle : FormalRegionCircuit Fp Config Config Row unit where
  configure := pure

  synthesize cfg offset (input : Row (AssignedCell Fp)) := do
    let _x ← copyAdvice input.pkdX cfg.colL offset
    let _b3 ← copyAdvice input.b3 cfg.colM offset
    let _d0 ← copyAdvice input.d0 cfg.colM (offset + 1)
    let _c ← copyAdvice input.c cfg.colR offset
    let _ap ← copyAdvice input.b3CPrime cfg.colR (offset + 1)
    let _z ← copyAdvice input.z13C cfg.colZ offset
    let _zp ← copyAdvice input.z14B3CPrime cfg.colZ (offset + 1)
    (gate cfg).enable offset
    pure ()

  -- input-only rely-conditions: the gate itself enforces the shift (constraint 2)
  Assumptions input := IsBool input.d0 ∧ input.c.val < 2 ^ 250 ∧
    input.b3.val < 2 ^ 4 ∧
    input.z13C = ((input.c.val / 2 ^ 130 : ℕ) : Fp) ∧
    ∃ lo : ℕ, lo < 2 ^ 140 ∧
      input.b3CPrime = ((lo : ℕ) : Fp) + ((2 ^ 140 : ℕ) : Fp) * input.z14B3CPrime

  Spec input _ _ := DSpec (toDonor input)

  ProverAssumptions input _ _ := DSpec (toDonor input) ∧
    input.b3CPrime = input.b3 + input.c * ((2 ^ 4 : ℕ) : Fp) + ((2 ^ 140 : ℕ) : Fp) - Orchard.tP

  soundness := by
    circuit_proof_start [gate]
    obtain ⟨hc1, hc2, hc3, hc4, hc5, hc6, hc7, hg1, hg2, hg3, hg4⟩ := hc
    rw [hc4, hc2, hc3, hc1] at hg1
    rw [hc2, hc4, hc5] at hg2
    rw [hc3, hc6] at hg3
    rw [hc3, hc7] at hg4
    have hshift : input_b3CPrime = input_b3 + input_c * ((2 ^ 4 : ℕ) : Fp)
        + ((2 ^ 140 : ℕ) : Fp) - Orchard.tP := by
      push_cast at hg2 ⊢; linear_combination -hg2
    exact Orchard.Action.NoteCommit.PkdCanonicity.Gate.spec_of_eqs
      ⟨input_pkdX, input_b3, input_d0, input_c, input_b3CPrime, input_z13C,
        input_z14B3CPrime⟩
      ⟨hA.1, hA.2.1, hA.2.2.1, hshift, hA.2.2.2.1, hA.2.2.2.2⟩
      (by push_cast; linear_combination hg1) hg3 hg4

  completeness := by
    intro cfg offset
    rw [FormalRegionCircuit.completeness_iff]
    intro self env input_var input output h_input h_output hwit _hE hA hPA
    simp only [circuit_norm, gate] at hwit h_input h_output hA hPA ⊢
    obtain ⟨hw1, hw2, hw3, hw4, hw5, hw6, hw7⟩ := hwit
    rw [show (ProvableStruct.eval env.place env.env.toEnvironment input_var
        : Row Fp)
      = { pkdX := env.env.get input_var.pkdX.cell.column
            ((env.place input_var.pkdX.cell.regionIndex
              + input_var.pkdX.cell.rowOffset : ℕ) : ℤ),
          b3 := env.env.get input_var.b3.cell.column
            ((env.place input_var.b3.cell.regionIndex
              + input_var.b3.cell.rowOffset : ℕ) : ℤ),
          d0 := env.env.get input_var.d0.cell.column
            ((env.place input_var.d0.cell.regionIndex
              + input_var.d0.cell.rowOffset : ℕ) : ℤ),
          c := env.env.get input_var.c.cell.column
            ((env.place input_var.c.cell.regionIndex
              + input_var.c.cell.rowOffset : ℕ) : ℤ),
          b3CPrime := env.env.get input_var.b3CPrime.cell.column
            ((env.place input_var.b3CPrime.cell.regionIndex
              + input_var.b3CPrime.cell.rowOffset : ℕ) : ℤ),
          z13C := env.env.get input_var.z13C.cell.column
            ((env.place input_var.z13C.cell.regionIndex
              + input_var.z13C.cell.rowOffset : ℕ) : ℤ),
          z14B3CPrime := env.env.get input_var.z14B3CPrime.cell.column
            ((env.place input_var.z14B3CPrime.cell.regionIndex
              + input_var.z14B3CPrime.cell.rowOffset : ℕ) : ℤ) } from by
        with_unfolding_all rfl] at h_input hA
    rw [h_input] at hA
    have hipkdX : env.env.get input_var.pkdX.cell.column
        ((env.place input_var.pkdX.cell.regionIndex
          + input_var.pkdX.cell.rowOffset : ℕ) : ℤ) = input.pkdX := congrArg Row.pkdX h_input
    have hib3 : env.env.get input_var.b3.cell.column
        ((env.place input_var.b3.cell.regionIndex
          + input_var.b3.cell.rowOffset : ℕ) : ℤ) = input.b3 := congrArg Row.b3 h_input
    have hid0 : env.env.get input_var.d0.cell.column
        ((env.place input_var.d0.cell.regionIndex
          + input_var.d0.cell.rowOffset : ℕ) : ℤ) = input.d0 := congrArg Row.d0 h_input
    have hic : env.env.get input_var.c.cell.column
        ((env.place input_var.c.cell.regionIndex
          + input_var.c.cell.rowOffset : ℕ) : ℤ) = input.c := congrArg Row.c h_input
    have hib3CPrime : env.env.get input_var.b3CPrime.cell.column
        ((env.place input_var.b3CPrime.cell.regionIndex
          + input_var.b3CPrime.cell.rowOffset : ℕ) : ℤ) = input.b3CPrime := congrArg Row.b3CPrime h_input
    have hiz13C : env.env.get input_var.z13C.cell.column
        ((env.place input_var.z13C.cell.regionIndex
          + input_var.z13C.cell.rowOffset : ℕ) : ℤ) = input.z13C := congrArg Row.z13C h_input
    have hiz14B3CPrime : env.env.get input_var.z14B3CPrime.cell.column
        ((env.place input_var.z14B3CPrime.cell.regionIndex
          + input_var.z14B3CPrime.cell.rowOffset : ℕ) : ℤ) = input.z14B3CPrime := congrArg Row.z14B3CPrime h_input
    have heqs := Orchard.Action.NoteCommit.PkdCanonicity.Gate.eqs_of_spec
      (toDonor input) ⟨hA.1, hA.2.1, hA.2.2.1, hPA.2, hA.2.2.2.1, hA.2.2.2.2⟩ hPA.1
    obtain ⟨he1, he2, he3, he4⟩ := heqs
    simp only [toDonor] at he1 he2 he3 he4
    rw [← hipkdX, ← hib3, ← hid0, ← hic, ← hw1, ← hw2, ← hw3, ← hw4] at he1
    rw [← hib3, ← hic, ← hib3CPrime, ← hw2, ← hw4, ← hw5] at he2
    rw [← hid0, ← hiz13C, ← hw3, ← hw6] at he3
    rw [← hid0, ← hiz14B3CPrime, ← hw3, ← hw7] at he4
    refine ⟨hw1, hw2, hw3, hw4, hw5, hw6, hw7, ?_, ?_, ?_, ?_⟩
    · push_cast at he1 ⊢
      linear_combination he1
    · push_cast at he2 ⊢
      linear_combination he2
    · linear_combination he3
    · linear_combination he4

end PkdCanonicity

namespace RhoCanonicity

private abbrev DRow := Orchard.Action.NoteCommit.RhoCanonicity.Gate.Row
private abbrev DSpec := Orchard.Action.NoteCommit.RhoCanonicity.Gate.Spec
private abbrev DAssumptions := Orchard.Action.NoteCommit.RhoCanonicity.Gate.Assumptions

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

/-- Rust `RhoCanonicity::assign` (`note_commit.rs:789-841`): pure copies (rows 0/1 of
`col_l/m/r/z`), gate enabled at row 0. `Spec`/`Assumptions` are the donor
`RhoCanonicity.Gate` contract; the canonicity value argument is the donor `spec_of_eqs`. -/
def bundle : FormalRegionCircuit Fp Config Config Row unit where
  configure := pure

  synthesize cfg offset (input : Row (AssignedCell Fp)) := do
    let _x ← copyAdvice input.rho cfg.colL offset
    let _e1 ← copyAdvice input.e1 cfg.colM offset
    let _g0 ← copyAdvice input.g0 cfg.colM (offset + 1)
    let _f ← copyAdvice input.f cfg.colR offset
    let _ap ← copyAdvice input.e1FPrime cfg.colR (offset + 1)
    let _z ← copyAdvice input.z13F cfg.colZ offset
    let _zp ← copyAdvice input.z14E1FPrime cfg.colZ (offset + 1)
    (gate cfg).enable offset
    pure ()

  -- input-only rely-conditions: the gate itself enforces the shift (constraint 2)
  Assumptions input := IsBool input.g0 ∧ input.f.val < 2 ^ 250 ∧
    input.e1.val < 2 ^ 4 ∧
    input.z13F = ((input.f.val / 2 ^ 130 : ℕ) : Fp) ∧
    ∃ lo : ℕ, lo < 2 ^ 140 ∧
      input.e1FPrime = ((lo : ℕ) : Fp) + ((2 ^ 140 : ℕ) : Fp) * input.z14E1FPrime

  Spec input _ _ := DSpec (toDonor input)

  ProverAssumptions input _ _ := DSpec (toDonor input) ∧
    input.e1FPrime = input.e1 + input.f * ((2 ^ 4 : ℕ) : Fp) + ((2 ^ 140 : ℕ) : Fp) - Orchard.tP

  soundness := by
    circuit_proof_start [gate]
    obtain ⟨hc1, hc2, hc3, hc4, hc5, hc6, hc7, hg1, hg2, hg3, hg4⟩ := hc
    rw [hc4, hc2, hc3, hc1] at hg1
    rw [hc2, hc4, hc5] at hg2
    rw [hc3, hc6] at hg3
    rw [hc3, hc7] at hg4
    have hshift : input_e1FPrime = input_e1 + input_f * ((2 ^ 4 : ℕ) : Fp)
        + ((2 ^ 140 : ℕ) : Fp) - Orchard.tP := by
      push_cast at hg2 ⊢; linear_combination -hg2
    exact Orchard.Action.NoteCommit.RhoCanonicity.Gate.spec_of_eqs
      ⟨input_rho, input_e1, input_g0, input_f, input_e1FPrime, input_z13F,
        input_z14E1FPrime⟩
      ⟨hA.1, hA.2.1, hA.2.2.1, hshift, hA.2.2.2.1, hA.2.2.2.2⟩
      (by push_cast; linear_combination hg1) hg3 hg4

  completeness := by
    intro cfg offset
    rw [FormalRegionCircuit.completeness_iff]
    intro self env input_var input output h_input h_output hwit _hE hA hPA
    simp only [circuit_norm, gate] at hwit h_input h_output hA hPA ⊢
    obtain ⟨hw1, hw2, hw3, hw4, hw5, hw6, hw7⟩ := hwit
    rw [show (ProvableStruct.eval env.place env.env.toEnvironment input_var
        : Row Fp)
      = { rho := env.env.get input_var.rho.cell.column
            ((env.place input_var.rho.cell.regionIndex
              + input_var.rho.cell.rowOffset : ℕ) : ℤ),
          e1 := env.env.get input_var.e1.cell.column
            ((env.place input_var.e1.cell.regionIndex
              + input_var.e1.cell.rowOffset : ℕ) : ℤ),
          g0 := env.env.get input_var.g0.cell.column
            ((env.place input_var.g0.cell.regionIndex
              + input_var.g0.cell.rowOffset : ℕ) : ℤ),
          f := env.env.get input_var.f.cell.column
            ((env.place input_var.f.cell.regionIndex
              + input_var.f.cell.rowOffset : ℕ) : ℤ),
          e1FPrime := env.env.get input_var.e1FPrime.cell.column
            ((env.place input_var.e1FPrime.cell.regionIndex
              + input_var.e1FPrime.cell.rowOffset : ℕ) : ℤ),
          z13F := env.env.get input_var.z13F.cell.column
            ((env.place input_var.z13F.cell.regionIndex
              + input_var.z13F.cell.rowOffset : ℕ) : ℤ),
          z14E1FPrime := env.env.get input_var.z14E1FPrime.cell.column
            ((env.place input_var.z14E1FPrime.cell.regionIndex
              + input_var.z14E1FPrime.cell.rowOffset : ℕ) : ℤ) } from by
        with_unfolding_all rfl] at h_input hA
    rw [h_input] at hA
    have hirho : env.env.get input_var.rho.cell.column
        ((env.place input_var.rho.cell.regionIndex
          + input_var.rho.cell.rowOffset : ℕ) : ℤ) = input.rho := congrArg Row.rho h_input
    have hie1 : env.env.get input_var.e1.cell.column
        ((env.place input_var.e1.cell.regionIndex
          + input_var.e1.cell.rowOffset : ℕ) : ℤ) = input.e1 := congrArg Row.e1 h_input
    have hig0 : env.env.get input_var.g0.cell.column
        ((env.place input_var.g0.cell.regionIndex
          + input_var.g0.cell.rowOffset : ℕ) : ℤ) = input.g0 := congrArg Row.g0 h_input
    have hif : env.env.get input_var.f.cell.column
        ((env.place input_var.f.cell.regionIndex
          + input_var.f.cell.rowOffset : ℕ) : ℤ) = input.f := congrArg Row.f h_input
    have hie1FPrime : env.env.get input_var.e1FPrime.cell.column
        ((env.place input_var.e1FPrime.cell.regionIndex
          + input_var.e1FPrime.cell.rowOffset : ℕ) : ℤ) = input.e1FPrime := congrArg Row.e1FPrime h_input
    have hiz13F : env.env.get input_var.z13F.cell.column
        ((env.place input_var.z13F.cell.regionIndex
          + input_var.z13F.cell.rowOffset : ℕ) : ℤ) = input.z13F := congrArg Row.z13F h_input
    have hiz14E1FPrime : env.env.get input_var.z14E1FPrime.cell.column
        ((env.place input_var.z14E1FPrime.cell.regionIndex
          + input_var.z14E1FPrime.cell.rowOffset : ℕ) : ℤ) = input.z14E1FPrime := congrArg Row.z14E1FPrime h_input
    have heqs := Orchard.Action.NoteCommit.RhoCanonicity.Gate.eqs_of_spec
      (toDonor input) ⟨hA.1, hA.2.1, hA.2.2.1, hPA.2, hA.2.2.2.1, hA.2.2.2.2⟩ hPA.1
    obtain ⟨he1, he2, he3, he4⟩ := heqs
    simp only [toDonor] at he1 he2 he3 he4
    rw [← hirho, ← hie1, ← hig0, ← hif, ← hw1, ← hw2, ← hw3, ← hw4] at he1
    rw [← hie1, ← hif, ← hie1FPrime, ← hw2, ← hw4, ← hw5] at he2
    rw [← hig0, ← hiz13F, ← hw3, ← hw6] at he3
    rw [← hig0, ← hiz14E1FPrime, ← hw3, ← hw7] at he4
    refine ⟨hw1, hw2, hw3, hw4, hw5, hw6, hw7, ?_, ?_, ?_, ?_⟩
    · push_cast at he1 ⊢
      linear_combination he1
    · push_cast at he2 ⊢
      linear_combination he2
    · linear_combination he3
    · linear_combination he4

end RhoCanonicity

namespace PsiCanonicity

private abbrev DRow := Orchard.Action.NoteCommit.PsiCanonicity.Gate.Row
private abbrev DSpec := Orchard.Action.NoteCommit.PsiCanonicity.Gate.Spec
private abbrev DAssumptions := Orchard.Action.NoteCommit.PsiCanonicity.Gate.Assumptions

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

/-- Rust `PsiCanonicity::assign` (`note_commit.rs:1240-1274`): pure copies (rows 0/1 of
`col_l/m/r/z`), gate enabled at row 0. `Spec`/`Assumptions` are the donor
`PsiCanonicity.Gate` contract. -/
def bundle : FormalRegionCircuit Fp Config Config Row unit where
  configure := pure

  synthesize cfg offset (input : Row (AssignedCell Fp)) := do
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

  -- input-only rely-conditions: the gate itself enforces the shift (constraint 2)
  Assumptions input := IsBool input.h1 ∧ input.g1.val < 2 ^ 9 ∧
    input.g2.val < 2 ^ 240 ∧ input.h0.val < 2 ^ 5 ∧
    input.z13G = (((input.g1.val + input.g2.val * 2 ^ 9) / 2 ^ 129 : ℕ) : Fp) ∧
    ∃ lo : ℕ, lo < 2 ^ 130 ∧
      input.g1G2Prime = ((lo : ℕ) : Fp) + ((2 ^ 130 : ℕ) : Fp) * input.z13G1G2Prime

  Spec input _ _ := DSpec (toDonor input)

  ProverAssumptions input _ _ := DSpec (toDonor input) ∧
    input.g1G2Prime = input.g1 + input.g2 * ((2 ^ 9 : ℕ) : Fp)
      + ((2 ^ 130 : ℕ) : Fp) - Orchard.tP

  soundness := by
    circuit_proof_start [gate]
    obtain ⟨hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hg1, hg2, hg3, hg4, hg5⟩ := hc
    rw [hc3, hc5, hc2, hc4, hc1] at hg1
    rw [hc3, hc5, hc6] at hg2
    rw [hc4, hc2] at hg3
    rw [hc4, hc7] at hg4
    rw [hc4, hc8] at hg5
    have hshift : input_g1G2Prime = input_g1 + input_g2 * ((2 ^ 9 : ℕ) : Fp)
        + ((2 ^ 130 : ℕ) : Fp) - Orchard.tP := by
      push_cast at hg2 ⊢; linear_combination -hg2
    exact Orchard.Action.NoteCommit.PsiCanonicity.Gate.spec_of_eqs
      ⟨input_psi, input_h0, input_g1, input_h1, input_g2, input_g1G2Prime, input_z13G,
        input_z13G1G2Prime⟩
      ⟨hA.1, hA.2.1, hA.2.2.1, hA.2.2.2.1, hshift, hA.2.2.2.2.1, hA.2.2.2.2.2⟩
      (by push_cast; linear_combination hg1) hg3 hg4 hg5

  completeness := by
    intro cfg offset
    rw [FormalRegionCircuit.completeness_iff]
    intro self env input_var input output h_input h_output hwit _hE hA hPA
    simp only [circuit_norm, gate] at hwit h_input h_output hA hPA ⊢
    obtain ⟨hw1, hw2, hw3, hw4, hw5, hw6, hw7, hw8⟩ := hwit
    rw [show (ProvableStruct.eval env.place env.env.toEnvironment input_var
        : Row Fp)
      = { psi := env.env.get input_var.psi.cell.column
            ((env.place input_var.psi.cell.regionIndex
              + input_var.psi.cell.rowOffset : ℕ) : ℤ),
          h0 := env.env.get input_var.h0.cell.column
            ((env.place input_var.h0.cell.regionIndex
              + input_var.h0.cell.rowOffset : ℕ) : ℤ),
          g1 := env.env.get input_var.g1.cell.column
            ((env.place input_var.g1.cell.regionIndex
              + input_var.g1.cell.rowOffset : ℕ) : ℤ),
          h1 := env.env.get input_var.h1.cell.column
            ((env.place input_var.h1.cell.regionIndex
              + input_var.h1.cell.rowOffset : ℕ) : ℤ),
          g2 := env.env.get input_var.g2.cell.column
            ((env.place input_var.g2.cell.regionIndex
              + input_var.g2.cell.rowOffset : ℕ) : ℤ),
          g1G2Prime := env.env.get input_var.g1G2Prime.cell.column
            ((env.place input_var.g1G2Prime.cell.regionIndex
              + input_var.g1G2Prime.cell.rowOffset : ℕ) : ℤ),
          z13G := env.env.get input_var.z13G.cell.column
            ((env.place input_var.z13G.cell.regionIndex
              + input_var.z13G.cell.rowOffset : ℕ) : ℤ),
          z13G1G2Prime := env.env.get input_var.z13G1G2Prime.cell.column
            ((env.place input_var.z13G1G2Prime.cell.regionIndex
              + input_var.z13G1G2Prime.cell.rowOffset : ℕ) : ℤ) } from by
        with_unfolding_all rfl] at h_input hA
    rw [h_input] at hA
    have hipsi : env.env.get input_var.psi.cell.column
        ((env.place input_var.psi.cell.regionIndex
          + input_var.psi.cell.rowOffset : ℕ) : ℤ) = input.psi := congrArg Row.psi h_input
    have hih0 : env.env.get input_var.h0.cell.column
        ((env.place input_var.h0.cell.regionIndex
          + input_var.h0.cell.rowOffset : ℕ) : ℤ) = input.h0 := congrArg Row.h0 h_input
    have hig1 : env.env.get input_var.g1.cell.column
        ((env.place input_var.g1.cell.regionIndex
          + input_var.g1.cell.rowOffset : ℕ) : ℤ) = input.g1 := congrArg Row.g1 h_input
    have hih1 : env.env.get input_var.h1.cell.column
        ((env.place input_var.h1.cell.regionIndex
          + input_var.h1.cell.rowOffset : ℕ) : ℤ) = input.h1 := congrArg Row.h1 h_input
    have hig2 : env.env.get input_var.g2.cell.column
        ((env.place input_var.g2.cell.regionIndex
          + input_var.g2.cell.rowOffset : ℕ) : ℤ) = input.g2 := congrArg Row.g2 h_input
    have hig1G2Prime : env.env.get input_var.g1G2Prime.cell.column
        ((env.place input_var.g1G2Prime.cell.regionIndex
          + input_var.g1G2Prime.cell.rowOffset : ℕ) : ℤ) = input.g1G2Prime := congrArg Row.g1G2Prime h_input
    have hiz13G : env.env.get input_var.z13G.cell.column
        ((env.place input_var.z13G.cell.regionIndex
          + input_var.z13G.cell.rowOffset : ℕ) : ℤ) = input.z13G := congrArg Row.z13G h_input
    have hiz13G1G2Prime : env.env.get input_var.z13G1G2Prime.cell.column
        ((env.place input_var.z13G1G2Prime.cell.regionIndex
          + input_var.z13G1G2Prime.cell.rowOffset : ℕ) : ℤ) = input.z13G1G2Prime := congrArg Row.z13G1G2Prime h_input
    have heqs := Orchard.Action.NoteCommit.PsiCanonicity.Gate.eqs_of_spec
      (toDonor input)
      ⟨hA.1, hA.2.1, hA.2.2.1, hA.2.2.2.1, hPA.2, hA.2.2.2.2.1, hA.2.2.2.2.2⟩ hPA.1
    obtain ⟨he1, he2, he3, he4, he5⟩ := heqs
    simp only [toDonor] at he1 he2 he3 he4 he5
    rw [← hig1, ← hig2, ← hih0, ← hih1, ← hipsi,
      ← hw3, ← hw5, ← hw2, ← hw4, ← hw1] at he1
    rw [← hig1, ← hig2, ← hig1G2Prime, ← hw3, ← hw5, ← hw6] at he2
    rw [← hih1, ← hih0, ← hw4, ← hw2] at he3
    rw [← hih1, ← hiz13G, ← hw4, ← hw7] at he4
    rw [← hih1, ← hiz13G1G2Prime, ← hw4, ← hw8] at he5
    refine ⟨hw1, hw2, hw3, hw4, hw5, hw6, hw7, hw8, ?_, ?_, ?_, ?_, ?_⟩
    · push_cast at he1 ⊢
      linear_combination he1
    · push_cast at he2 ⊢
      linear_combination he2
    · linear_combination he3
    · linear_combination he4
    · linear_combination he5

end PsiCanonicity

namespace YCanonicity

private abbrev DRow := Orchard.Action.NoteCommit.YCanonicity.Gate.Row
private abbrev DSpec := Orchard.Action.NoteCommit.YCanonicity.Gate.Spec
private abbrev DAssumptions := Orchard.Action.NoteCommit.YCanonicity.Gate.Assumptions

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

  synthesize cfg offset (input : Row (AssignedCell Fp)) := do
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
    input.jPrime = input.j + ((2 ^ 130 : ℕ) : Fp) - Orchard.tP

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
    have hjP : input_jPrime = input_j + ((2 ^ 130 : ℕ) : Fp) - Orchard.tP := by
      push_cast at hjpc ⊢; linear_combination -hjpc
    have hidx : ((place self + offset : ℕ) : ℤ)
        = ((place self : ℕ) : ℤ) + ((offset : ℕ) : ℤ) := by push_cast; ring
    rw [hidx] at hk3c hyc hg1 hg3
    exact ⟨trivial, fun hbool =>
      Orchard.Action.NoteCommit.YCanonicity.Gate.spec_of_eqs
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
    intro cfg offset
    rw [FormalRegionCircuit.completeness_iff]
    intro self env input_var input output h_input h_output hwit _hE hA hPA
    simp only [circuit_norm, gate, boolCheck] at hwit h_input h_output hA hPA ⊢
    obtain ⟨hwy, hwlsb, hwk0, hwk2, hwk3, hwj, hwz1, hwz13, hwjp, hwz13p⟩ := hwit
    rw [show (ProvableStruct.eval env.place env.env.toEnvironment input_var
        : Row Fp)
      = { y := env.env.get input_var.y.cell.column
            ((env.place input_var.y.cell.regionIndex
              + input_var.y.cell.rowOffset : ℕ) : ℤ),
          k0 := env.env.get input_var.k0.cell.column
            ((env.place input_var.k0.cell.regionIndex
              + input_var.k0.cell.rowOffset : ℕ) : ℤ),
          k2 := env.env.get input_var.k2.cell.column
            ((env.place input_var.k2.cell.regionIndex
              + input_var.k2.cell.rowOffset : ℕ) : ℤ),
          j := env.env.get input_var.j.cell.column
            ((env.place input_var.j.cell.regionIndex
              + input_var.j.cell.rowOffset : ℕ) : ℤ),
          z1J := env.env.get input_var.z1J.cell.column
            ((env.place input_var.z1J.cell.regionIndex
              + input_var.z1J.cell.rowOffset : ℕ) : ℤ),
          z13J := env.env.get input_var.z13J.cell.column
            ((env.place input_var.z13J.cell.regionIndex
              + input_var.z13J.cell.rowOffset : ℕ) : ℤ),
          jPrime := env.env.get input_var.jPrime.cell.column
            ((env.place input_var.jPrime.cell.regionIndex
              + input_var.jPrime.cell.rowOffset : ℕ) : ℤ),
          z13JPrime := env.env.get input_var.z13JPrime.cell.column
            ((env.place input_var.z13JPrime.cell.regionIndex
              + input_var.z13JPrime.cell.rowOffset : ℕ) : ℤ) } from by
        with_unfolding_all rfl] at h_input hA
    rw [h_input] at hA
    have hiy : env.env.get input_var.y.cell.column
        ((env.place input_var.y.cell.regionIndex
          + input_var.y.cell.rowOffset : ℕ) : ℤ) = input.y := congrArg Row.y h_input
    have hik0 : env.env.get input_var.k0.cell.column
        ((env.place input_var.k0.cell.regionIndex
          + input_var.k0.cell.rowOffset : ℕ) : ℤ) = input.k0 := congrArg Row.k0 h_input
    have hik2 : env.env.get input_var.k2.cell.column
        ((env.place input_var.k2.cell.regionIndex
          + input_var.k2.cell.rowOffset : ℕ) : ℤ) = input.k2 := congrArg Row.k2 h_input
    have hij : env.env.get input_var.j.cell.column
        ((env.place input_var.j.cell.regionIndex
          + input_var.j.cell.rowOffset : ℕ) : ℤ) = input.j := congrArg Row.j h_input
    have hiz1J : env.env.get input_var.z1J.cell.column
        ((env.place input_var.z1J.cell.regionIndex
          + input_var.z1J.cell.rowOffset : ℕ) : ℤ) = input.z1J := congrArg Row.z1J h_input
    have hiz13J : env.env.get input_var.z13J.cell.column
        ((env.place input_var.z13J.cell.regionIndex
          + input_var.z13J.cell.rowOffset : ℕ) : ℤ) = input.z13J := congrArg Row.z13J h_input
    have hijPrime : env.env.get input_var.jPrime.cell.column
        ((env.place input_var.jPrime.cell.regionIndex
          + input_var.jPrime.cell.rowOffset : ℕ) : ℤ) = input.jPrime := congrArg Row.jPrime h_input
    have hiz13JPrime : env.env.get input_var.z13JPrime.cell.column
        ((env.place input_var.z13JPrime.cell.regionIndex
          + input_var.z13JPrime.cell.rowOffset : ℕ) : ℤ) = input.z13JPrime := congrArg Row.z13JPrime h_input
    have heqs := Orchard.Action.NoteCommit.YCanonicity.Gate.eqs_of_spec
      (toDonor input
        (env.env.advice (cfg.advices 6) ((env.place self + offset : ℕ) : ℤ))
        (env.env.advice (cfg.advices 9) ((env.place self + offset : ℕ) : ℤ)))
      ⟨hPA.1, hA.1, hA.2.1, hA.2.2.1, hPA.2.2, hA.2.2.2.1,
        hA.2.2.2.2.1, hA.2.2.2.2.2⟩ hPA.2.1
    obtain ⟨hb, he2, he3, he4, he5, he6, he7⟩ := heqs
    simp only [toDonor] at hb he2 he3 he4 he5 he6 he7
    rw [← hij, ← hik0, ← hiz1J, ← hwj, ← hwk0, ← hwz1] at he2
    rw [← hiy, ← hij, ← hik2, ← hwy, ← hwj, ← hwk2] at he3
    rw [← hij, ← hijPrime, ← hwj, ← hwjp] at he4
    rw [← hik2, ← hwk2] at he5
    rw [← hiz13J, ← hwz13] at he6
    rw [← hiz13JPrime, ← hwz13p] at he7
    refine ⟨⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
      hwy, hwk0, hwk2, hwj, hwz1, hwz13, hwjp, hwz13p⟩, h_output.symm⟩
    · rcases hb with h | h <;> rw [h] <;> ring
    · push_cast at he2 ⊢
      linear_combination he2
    · push_cast at he3 ⊢
      linear_combination he3
    · push_cast at he4 ⊢
      linear_combination he4
    · linear_combination he5
    · linear_combination he6
    · linear_combination he7

end YCanonicity

end Halo2.Ironwood.NoteCommit
