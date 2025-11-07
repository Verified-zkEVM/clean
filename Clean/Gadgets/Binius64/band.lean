import Mathlib.Data.ZMod.Basic
import Clean.Circuit.Basic
import Clean.Circuit.Theorems
import Clean.Circuit.Provable
import Clean.Circuit.Expression
import Clean.Gadgets.Binius64.SVI

namespace Gadgets.Binius64

open Circuit

variable {p : ℕ} [Fact p.Prime]

/-- Inputs to the Binius 64-bit bitwise-and gadget. -/
structure BandInputs (F : Type) where
  lhs : SVIData F
  rhs : SVIData F

instance : ProvableStruct BandInputs where
  components := [SVI, SVI]
  toComponents := fun { lhs, rhs } => .cons lhs (.cons rhs .nil)
  fromComponents := fun
    | .cons lhs (.cons rhs .nil) => { lhs, rhs }

namespace Band

private def elementwiseAndExpr
    (lhs rhs : Vector (Expression (F p)) 64) : Vector (Expression (F p)) 64 :=
  Vector.ofFn fun i => lhs[i] * rhs[i]

private def elementwiseAndVals
    (lhs rhs : Vector (F p) 64) : Vector (F p) 64 :=
  Vector.ofFn fun i => lhs[i] * rhs[i]

/-- we do not constrain the shifts yet   --/
def main (input : Var BandInputs (F p)) : Circuit (F p) (Var SVI (F p)) := do
  let ⟨lhs, rhs⟩ := input
  let lhsShifted ← applyShiftExpr lhs
  let rhsShifted ← applyShiftExpr rhs
  let wire := elementwiseAndExpr lhsShifted rhsShifted
  return {
    wire
    shiftType := Expression.const (F:=F p) 0
    shiftAmount := Expression.const (F:=F p) 0
  }

def Assumptions (_ : BandInputs (F p)) : Prop := True

def Spec (input : BandInputs (F p)) (output : SVIData (F p)) : Prop :=
  let lhsShift := applyShift input.lhs
  let rhsShift := applyShift input.rhs
  output.shiftType = 0 ∧
  output.shiftAmount = 0 ∧
  output.wire = elementwiseAndVals lhsShift rhsShift

instance elaborated : ElaboratedCircuit (F p) BandInputs SVI where
  main := main
  localLength input :=
    shiftLocalLength input.lhs + shiftLocalLength input.rhs

  localLength_eq := by
    intro input offset
    rcases input with ⟨lhs, rhs⟩
    simp [main, shiftLocalLength, Circuit.bind_localLength_eq,
      Circuit.map_localLength_eq]
  subcircuitsConsistent := by sorry

theorem soundness : Soundness (F p) elaborated Assumptions Spec := by
  intro offset env inputVar input h_input _ h_constraints
  sorry

theorem completeness : Completeness (F p) elaborated Assumptions := by
  intro offset env inputVar h_env input h_eval _
  sorry

def circuit : FormalCircuit (F p) BandInputs SVI where
  elaborated := elaborated
  Assumptions := Assumptions
  Spec := Spec
  soundness := soundness
  completeness := completeness

end Band

end Gadgets.Binius64
