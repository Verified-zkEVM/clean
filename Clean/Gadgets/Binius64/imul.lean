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
  sorry

theorem completeness (k m : ShiftKind) (a b : Fin 64) :
    Completeness (F p) (elaborated (k:=k) (m:=m) (a:=a) (b:=b))
      (Assumptions) := by
  sorry

def circuit (k m : ShiftKind) (a b : Fin 64) :
    FormalCircuit (F p) (IMulInputs k m a b) IMulOutputs where
  elaborated := elaborated (k:=k) (m:=m) (a:=a) (b:=b)
  Assumptions := Assumptions
  Spec := Spec
  soundness := soundness (k:=k) (m:=m) (a:=a) (b:=b)
  completeness := completeness (k:=k) (m:=m) (a:=a) (b:=b)

end IMul

end Gadgets.Binius64
