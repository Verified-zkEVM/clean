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

  Assumptions input := DAssumptions (toDonor input)

  Spec input _ _ := DSpec (toDonor input)

  ProverAssumptions input _ _ := DSpec (toDonor input)

  soundness := by
    circuit_proof_start [gate]
    obtain ⟨hc1, hc2, hc3, hc4, hc5, hc6, hc7, hg1, hg2, hg3, hg4, hg5⟩ := hc
    rw [hc4, hc2, hc3, hc1] at hg1
    rw [hc3, hc2] at hg3
    rw [hc3, hc6] at hg4
    rw [hc3, hc7] at hg5
    exact Orchard.Action.NoteCommit.GdCanonicity.Gate.spec_of_eqs
      ⟨input_gdX, input_b0, input_b1, input_a, input_aPrime, input_z13A,
        input_z13APrime⟩ hA
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
      (toDonor input) hA hPA
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

end Halo2.Ironwood.NoteCommit
