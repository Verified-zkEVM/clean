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

end Halo2.Ironwood.NoteCommit
