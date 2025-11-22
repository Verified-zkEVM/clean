import Mathlib.Data.ZMod.Basic
import Clean.Circuit
import Clean.Gadgets.Binius64.SVI
import Clean.Utils.Tactics.CircuitProofStart

namespace Gadgets.Binius64

open Circuit

variable {p : ℕ} [Fact p.Prime]
variable {k m : ShiftKind} {a b : Fin 64}

/-- Inputs to the Binius 64-bit multiplication gadget. -/
structure IMulInputs (k m : ShiftKind) (a b : Fin 64) (F : Type) where
  lhs : SVI k a F
  rhs : SVI m b F

/-- Outputs of the multiplication gadget: low and high parts. -/
structure IMulOutputs (F : Type) where
  low : SVI .sll 0 F
  high : SVI .sll 0 F

instance : ProvableStruct (IMulInputs k m a b) where
  components := [SVI k a, SVI m b]
  toComponents := fun { lhs, rhs } => .cons lhs (.cons rhs .nil)
  fromComponents := fun
    | .cons lhs (.cons rhs .nil) => { lhs, rhs }

instance : ProvableStruct (IMulOutputs) where
  components := [SVI .sll 0, SVI .sll 0]
  toComponents := fun { low, high } => .cons low (.cons high .nil)
  fromComponents := fun
    | .cons low (.cons high .nil) => { low, high }

namespace IMul

variable {α : Type}

private def convolutionCoeff [Zero α] [Add α] [Mul α]
    (lhs rhs : Vector α 64) (n : ℕ) : α :=
  (List.range 64).foldl
    (fun acc i =>
      if hi : i < 64 then
        if hle : i ≤ n then
          let j := n - i
          if hj : j < 64 then
            let lhsIdx : Fin 64 := ⟨i, hi⟩
            let rhsIdx : Fin 64 := ⟨j, hj⟩
            acc + lhs[lhsIdx] * rhs[rhsIdx]
          else
            acc
        else
          acc
      else
        acc)
    0

private def unsignedMulVec [Zero α] [Add α] [Mul α]
    (lhs rhs : Vector α 64) :
    Vector α 64 × Vector α 64 :=
  let lo :=
    Vector.ofFn fun i => convolutionCoeff lhs rhs i.val
  let hi :=
    Vector.ofFn fun i => convolutionCoeff lhs rhs (i.val + 64)
  (hi, lo)

private def unsignedMulExpr
    (lhs rhs : Vector (Expression (F p)) 64) :
    Vector (Expression (F p)) 64 × Vector (Expression (F p)) 64 :=
  unsignedMulVec lhs rhs

private def unsignedMulVals
    (lhs rhs : Vector (F p) 64) :
    Vector (F p) 64 × Vector (F p) 64 :=
  unsignedMulVec lhs rhs

private lemma convolutionCoeff_eval
    (env : Environment (F p))
    (lhs rhs : Vector (Expression (F p)) 64) (n : ℕ) :
    Expression.eval env (convolutionCoeff lhs rhs n) =
      convolutionCoeff (Vector.map (Expression.eval env) lhs)
        (Vector.map (Expression.eval env) rhs) n := by
  classical
  set lhsVals := Vector.map (Expression.eval env) lhs
  set rhsVals := Vector.map (Expression.eval env) rhs
  let f :=
    fun (acc : Expression (F p)) i =>
      if hi : i < 64 then
        if hle : i ≤ n then
          let j := n - i
          if hj : j < 64 then
            let lhsIdx : Fin 64 := ⟨i, hi⟩
            let rhsIdx : Fin 64 := ⟨j, hj⟩
            acc + lhs[lhsIdx] * rhs[rhsIdx]
          else
            acc
        else
          acc
      else
        acc
  let g :=
    fun (acc : F p) i =>
      if hi : i < 64 then
        if hle : i ≤ n then
          let j := n - i
          if hj : j < 64 then
            let lhsIdx : Fin 64 := ⟨i, hi⟩
            let rhsIdx : Fin 64 := ⟨j, hj⟩
            acc + lhsVals[lhsIdx] * rhsVals[rhsIdx]
          else
            acc
        else
          acc
      else
        acc
  have hstep :
      ∀ acc i, Expression.eval env (f acc i) =
        g (Expression.eval env acc) i := by
    intro acc i
    by_cases hi : i < 64
    · by_cases hle : i ≤ n
      · by_cases hj : n - i < 64
        · simp [f, g, hi, hle, hj, lhsVals, rhsVals, eval_add, eval_mul']
        · simp [f, g, hi, hle, hj]
      · simp [f, g, hi, hle]
    · simp [f, g, hi]
  have hfold :
      ∀ (l : List ℕ) (acc : Expression (F p)),
        Expression.eval env (l.foldl f acc) =
          l.foldl g (Expression.eval env acc) := by
    intro l
    induction l with
    | nil =>
        intro acc
        rfl
    | cons a l ih =>
        intro acc
        have := hstep acc a
        simpa [List.foldl, this] using ih (f acc a)
  simpa [convolutionCoeff, lhsVals, rhsVals, f, g] using
    hfold (List.range 64) 0

private lemma unsignedMulExpr_eval
    (env : Environment (F p))
    (lhs rhs : Vector (Expression (F p)) 64) :
    let (highExpr, lowExpr) := unsignedMulExpr lhs rhs
    let lhsVals := Vector.map (Expression.eval env) lhs
    let rhsVals := Vector.map (Expression.eval env) rhs
    let (highVals, lowVals) := unsignedMulVals lhsVals rhsVals
    Vector.map (Expression.eval env) highExpr = highVals ∧
      Vector.map (Expression.eval env) lowExpr = lowVals := by
  classical
  dsimp [unsignedMulExpr, unsignedMulVals, unsignedMulVec]
  refine And.intro ?_ ?_
  · ext i
    simp [Vector.getElem_map, Vector.getElem_ofFn, convolutionCoeff_eval]
  · ext i
    simp [Vector.getElem_map, Vector.getElem_ofFn, convolutionCoeff_eval]

def main (k m : ShiftKind) (a b : Fin 64)
    (input : Var (IMulInputs k m a b) (F p)) :
    Circuit (F p) (Var IMulOutputs (F p)) := do
  let ⟨lhs, rhs⟩ := input
  let lhsShifted ← applyShiftExpr lhs
  let rhsShifted ← applyShiftExpr rhs
  let (highWire, lowWire) := unsignedMulExpr lhsShifted rhsShifted
  return { high := { wire := highWire }, low := { wire := lowWire } }

def Assumptions (_ : IMulInputs k m a b (F p)) : Prop := True

def Spec (input : IMulInputs k m a b (F p))
    (output : IMulOutputs (F p)) : Prop :=
  let lhsShift := applyShift input.lhs
  let rhsShift := applyShift input.rhs
  let (highVals, lowVals) := unsignedMulVals lhsShift rhsShift
  output.high.wire = highVals ∧ output.low.wire = lowVals

instance elaborated (k m : ShiftKind) (a b : Fin 64) :
    ElaboratedCircuit (F p) (IMulInputs k m a b) IMulOutputs where
  main := main k m a b
  localLength _ := 0

theorem soundness (k m : ShiftKind) (a b : Fin 64) :
    Soundness (F p) (elaborated (k:=k) (m:=m) (a:=a) (b:=b))
      (Assumptions (k:=k) (m:=m) (a:=a) (b:=b))
      (Spec (k:=k) (m:=m) (a:=a) (b:=b)) := by
  circuit_proof_start
  classical
  have h_eval :=
    unsignedMulExpr_eval (env := env)
      (lhs := (applyShiftExpr input_var.lhs i₀).1)
      (rhs :=
        (applyShiftExpr input_var.rhs
          (i₀ + Operations.localLength (applyShiftExpr input_var.lhs i₀).2)).1)
  obtain ⟨h_high, h_low⟩ := h_eval
  have hl :
      Vector.map (Expression.eval env) (applyShiftExpr input_var.lhs i₀).1 =
        applyShift
          ({ wire := Vector.map (Expression.eval env) input_var.lhs.wire } :
            SVI k a (F p)) := by
    simp [applyShiftExpr, applyShift, map_eval_applyShiftVec, circuit_norm]
  have hr :
      Vector.map (Expression.eval env)
          (applyShiftExpr input_var.rhs
            (i₀ + Operations.localLength (applyShiftExpr input_var.lhs i₀).2)).1 =
        applyShift
          ({ wire := Vector.map (Expression.eval env) input_var.rhs.wire } :
            SVI m b (F p)) := by
    simp [applyShiftExpr, applyShift, map_eval_applyShiftVec, circuit_norm]
  have h_congr_high :
      (unsignedMulVals
          (Vector.map (Expression.eval env) (applyShiftExpr input_var.lhs i₀).1)
          (Vector.map (Expression.eval env)
            (applyShiftExpr input_var.rhs
              (i₀ + Operations.localLength (applyShiftExpr input_var.lhs i₀).2)).1)).1 =
        (unsignedMulVals
          (applyShift
            ({ wire := Vector.map (Expression.eval env) input_var.lhs.wire } :
              SVI k a (F p)))
          (applyShift
            ({ wire := Vector.map (Expression.eval env) input_var.rhs.wire } :
              SVI m b (F p)))).1 := by
    have h₁ :=
      congrArg (fun lhs =>
        (unsignedMulVals lhs
          (Vector.map (Expression.eval env)
            (applyShiftExpr input_var.rhs
              (i₀ + Operations.localLength (applyShiftExpr input_var.lhs i₀).2)).1)).1) hl
    have h₂ :=
      congrArg (fun rhs =>
        (unsignedMulVals
          (applyShift
            ({ wire := Vector.map (Expression.eval env) input_var.lhs.wire } :
              SVI k a (F p))) rhs).1) hr
    simpa [applyShift] using h₁.trans h₂
  have h_congr_low :
      (unsignedMulVals
          (Vector.map (Expression.eval env) (applyShiftExpr input_var.lhs i₀).1)
          (Vector.map (Expression.eval env)
            (applyShiftExpr input_var.rhs
              (i₀ + Operations.localLength (applyShiftExpr input_var.lhs i₀).2)).1)).2 =
        (unsignedMulVals
          (applyShift
            ({ wire := Vector.map (Expression.eval env) input_var.lhs.wire } :
              SVI k a (F p)))
          (applyShift
            ({ wire := Vector.map (Expression.eval env) input_var.rhs.wire } :
              SVI m b (F p)))).2 := by
    have h₁ :=
      congrArg (fun lhs =>
        (unsignedMulVals lhs
          (Vector.map (Expression.eval env)
            (applyShiftExpr input_var.rhs
              (i₀ + Operations.localLength (applyShiftExpr input_var.lhs i₀).2)).1)).2) hl
    have h₂ :=
      congrArg (fun rhs =>
        (unsignedMulVals
          (applyShift
            ({ wire := Vector.map (Expression.eval env) input_var.lhs.wire } :
              SVI k a (F p))) rhs).2) hr
    simpa [applyShift] using h₁.trans h₂
  have h_high' := h_high.trans h_congr_high
  have h_low' := h_low.trans h_congr_low
  cases h_input
  simpa [Spec] using And.intro h_high' h_low'

theorem completeness (k m : ShiftKind) (a b : Fin 64) :
    Completeness (F p) (elaborated (k:=k) (m:=m) (a:=a) (b:=b))
      (Assumptions) := by
  circuit_proof_start [applyShiftExpr]

def circuit (k m : ShiftKind) (a b : Fin 64) :
    FormalCircuit (F p) (IMulInputs k m a b) IMulOutputs where
  elaborated := elaborated (k:=k) (m:=m) (a:=a) (b:=b)
  Assumptions := Assumptions
  Spec := Spec
  soundness := soundness (k:=k) (m:=m) (a:=a) (b:=b)
  completeness := completeness (k:=k) (m:=m) (a:=a) (b:=b)

end IMul

end Gadgets.Binius64
