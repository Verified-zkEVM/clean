import Mathlib.Data.ZMod.Basic
import Clean.Circuit
import Clean.Gadgets.Binius64.SVI
import Clean.Utils.Tactics.CircuitProofStart

namespace Gadgets.Binius64

open Circuit

variable {p : ℕ} [Fact p.Prime]
variable {k m : ShiftKind} {a b : Fin 64}

/-- Inputs to the Binius 64-bit bitwise-and gadget. -/
structure BandInputs (k m : ShiftKind) (a b : Fin 64) (F : Type) where
  lhs : SVI k a F
  rhs : SVI m b F

instance : ProvableStruct (BandInputs k m a b) where
  components := [SVI k a, SVI m b]
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

private lemma elementwiseAndExpr_eval
    (env : Environment (F p))
    (lhs rhs : Vector (Expression (F p)) 64) :
    Vector.map (Expression.eval env) (elementwiseAndExpr lhs rhs) =
      elementwiseAndVals (Vector.map (Expression.eval env) lhs)
        (Vector.map (Expression.eval env) rhs) := by
  classical
  ext i
  simp [elementwiseAndExpr, elementwiseAndVals, Expression.eval]

def main (k m : ShiftKind) (a b : Fin 64)
    (input : Var (BandInputs k m a b) (F p)) :
    Circuit (F p) (Var (SVI .sll 0) (F p)) := do
  let ⟨lhs, rhs⟩ := input
  let lhsShifted ← applyShiftExpr lhs
  let rhsShifted ← applyShiftExpr rhs
  let wire := elementwiseAndExpr lhsShifted rhsShifted
  return { wire := wire }

def Assumptions (_ : BandInputs k m a b (F p)) : Prop := True

def Spec (input : BandInputs k m a b (F p))
    (output : SVI (.sll) 0 (F p)) : Prop :=
  let lhsShift := applyShift input.lhs
  let rhsShift := applyShift input.rhs
  output.wire = elementwiseAndVals lhsShift rhsShift

instance elaborated (k m : ShiftKind) (a b : Fin 64) :
    ElaboratedCircuit (F p) (BandInputs k m a b) (SVI .sll 0) where
  main := main k m a b
  localLength _ := 0


theorem soundness (k m : ShiftKind) (a b : Fin 64) :
    Soundness (F p) (elaborated (k:=k) (m:=m) (a:=a) (b:=b))
      (Assumptions (k:=k) (m:=m) (a:=a) (b:=b))
      (Spec (k:=k) (m:=m) (a:=a) (b:=b)) := by
  circuit_proof_start
  classical
  have h_eval :=
    elementwiseAndExpr_eval (env := env)
      (lhs := (applyShiftExpr input_var.lhs i₀).1)
      (rhs :=
        (applyShiftExpr input_var.rhs
          (i₀ + Operations.localLength (applyShiftExpr input_var.lhs i₀).2)).1)
  have hl :
      Vector.map (Expression.eval env) (applyShiftExpr input_var.lhs i₀).1 =
        applyShift
          ({ wire := Vector.map (Expression.eval env) input_var.lhs.wire } :
            SVI k a (F p)) := by
    simp [applyShiftExpr, applyShift, map_eval_applyShiftVec, Circuit.pure_def]
  have hr :
      Vector.map (Expression.eval env)
          (applyShiftExpr input_var.rhs
            (i₀ + Operations.localLength (applyShiftExpr input_var.lhs i₀).2)).1 =
        applyShift
          ({ wire := Vector.map (Expression.eval env) input_var.rhs.wire } :
            SVI m b (F p)) := by
    simp [applyShiftExpr, applyShift, map_eval_applyShiftVec, Circuit.pure_def]
  cases h_input
  have h_rhs₁ :=
    congrArg (fun lhs =>
      elementwiseAndVals
        (lhs:=lhs)
        (rhs :=
          Vector.map (Expression.eval env)
            (applyShiftExpr input_var.rhs
              (i₀ + Operations.localLength (applyShiftExpr input_var.lhs i₀).2)).1)) hl
  have h_rhs₂ :=
    congrArg (fun rhs =>
      elementwiseAndVals
        (lhs :=
          applyShift
            ({ wire := Vector.map (Expression.eval env) input_var.lhs.wire } :
              SVI k a (F p)))
        (rhs:=rhs)) hr
  exact h_eval.trans (h_rhs₁.trans h_rhs₂)

theorem completeness (k m : ShiftKind) (a b : Fin 64) :
    Completeness (F p) (elaborated (k:=k) (m:=m) (a:=a) (b:=b))
      (Assumptions) := by
  circuit_proof_start
  simp [applyShiftExpr, circuit_norm]

def circuit (k m : ShiftKind) (a b : Fin 64) :
    FormalCircuit (F p) (BandInputs k m a b) (SVI .sll 0) where
  elaborated := elaborated (k:=k) (m:=m) (a:=a) (b:=b)
  Assumptions := Assumptions
  Spec := Spec
  soundness := soundness (k:=k) (m:=m) (a:=a) (b:=b)
  completeness := completeness (k:=k) (m:=m) (a:=a) (b:=b)

end Band

end Gadgets.Binius64
