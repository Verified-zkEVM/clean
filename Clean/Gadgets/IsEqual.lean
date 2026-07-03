/-
This file provides the `IsEqual` gadget, which takes two values of any provable type
and returns a field element that is 1 when the inputs are equal, 0 otherwise.

This is the boolean-returning counterpart of `Gadgets.Equality`, which asserts
equality without returning a value.
-/
import Clean.Circuit.Basic
import Clean.Circuit.Provable
import Clean.Circuit.Theorems
import Clean.Circuit.Loops
import Clean.Gadgets.IsZeroField
import Clean.Gadgets.IsZero
import Clean.Utils.Field
import Clean.Utils.Tactics

namespace Gadgets.IsEqual

variable {F : Type} [FiniteField F] [DecidableEq F]
variable {α : TypeMap} [ProvableType α] [DecidableEq (α F)]

/--
Compute element-wise differences between two values of a ProvableType.
Defined separately so it survives circuit normalization as a single vector.
-/
def diffs (x y : Var α F) : Vector (Expression F) (size α) :=
  Vector.mapFinRange (size α) fun i => (toElements (M:=α) x)[↑i] - (toElements (M:=α) y)[↑i]

/--
Circuit that checks if two values of a ProvableType are equal.
Returns 1 if the inputs are equal, otherwise returns 0.
Uses three constraints per field element (IsZeroField on each component difference + one multiplication).
-/
def main (input : Var α F × Var α F) : Circuit F (Var field F) := do
  let (x, y) := input
  let d := diffs x y
  IsZero.circuit (fromElements (M:=α) d)

@[reducible]
instance elaborated : ElaboratedCircuit F (ProvablePair α α) field main := by
  elaborate_circuit

def Assumptions (_ : α F × α F) : Prop := True

def Spec (input : α F × α F) (output : F) : Prop :=
  output = if input.1 = input.2 then 1 else 0

theorem soundness : Soundness (Input:=ProvablePair α α) (Output:=field) F (main (α:=α)) Assumptions Spec := by
  circuit_proof_start [IsZero.circuit, IsZero.elaborated, IsZero.Assumptions, IsZero.Spec]
  rw [h_holds]
  have h_x : eval env input_var.1 = input.1 := congrArg Prod.fst h_input
  have h_y : eval env input_var.2 = input.2 := congrArg Prod.snd h_input
  apply if_congr _ rfl rfl
  -- Helper: relate evaluated diffs to element-wise subtraction
  have h_diff : ∀ (i : ℕ) (_ : i < size α),
      Expression.eval env (diffs input_var.1 input_var.2)[i] =
      (toElements input.1)[i] - (toElements input.2)[i] := by
    intro i hi
    simp only [diffs, Vector.getElem_mapFinRange, Expression.eval, neg_one_mul]
    erw [ProvableType.getElem_eval_toElements input_var.1 i, ProvableType.getElem_eval_toElements input_var.2 i,
      h_x, h_y]
    ring
  -- Helper: (toElements 0)[i] = 0
  have h_zero_elem : ∀ (i : ℕ) (_ : i < size α), (toElements (0 : α F))[i] = (0 : F) := by
    intro i _
    change (toElements (fromElements (Vector.replicate _ (0 : F))))[i] = 0
    rw [ProvableType.toElements_fromElements, Vector.getElem_replicate]
  constructor
  · -- forward: diffs evaluated to zero → inputs equal
    intro h_zero
    rw [ProvableType.ext_iff]; intro i hi
    have h_elem := congrArg (fun (x : α F) => (toElements x)[i]) h_zero
    simp only [ProvableType.eval_fromElements, ProvableType.toElements_fromElements,
      Vector.getElem_map] at h_elem
    rw [h_diff i hi, h_zero_elem i hi] at h_elem
    exact sub_eq_zero.mp h_elem
  · -- backward: inputs equal → diffs evaluated to zero
    intro h_eq
    rw [ProvableType.ext_iff]; intro i hi
    simp only [ProvableType.eval_fromElements, ProvableType.toElements_fromElements,
      Vector.getElem_map]
    rw [h_diff i hi, h_zero_elem i hi]
    rw [ProvableType.ext_iff] at h_eq; rw [h_eq i hi]; ring

theorem completeness : Completeness (Input:=ProvablePair α α) (Output:=field) F (main (α:=α)) Assumptions := by
  circuit_proof_start [IsZero.circuit, IsZero.elaborated, IsZero.Assumptions]

def circuit : FormalCircuit F (ProvablePair α α) field where
  main
  elaborated
  Assumptions
  Spec
  soundness
  completeness

end Gadgets.IsEqual
