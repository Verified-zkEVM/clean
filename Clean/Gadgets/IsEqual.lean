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

variable {F : Type} [Field F] [DecidableEq F]
variable {α : TypeMap} [ProvableType α]

/--
Compute element-wise differences between two values of a ProvableType.
Defined separately so it survives circuit normalization as a single vector.
-/
def diffs (x y : Var α F) : Vector (Expression F) (size α) :=
  Vector.mapFinRange (size α) fun i => (toVars x)[↑i] - (toVars y)[↑i]

/--
Circuit that checks if two values of a ProvableType are equal.
Returns 1 if the inputs are equal, otherwise returns 0.
Uses three constraints per field element (IsZeroField on each component difference + one multiplication).
-/
def main (input : Var α F × Var α F) : Circuit F (Var field F) := do
  let (x, y) := input
  let d := diffs x y
  IsZero.circuit (fromVars d)

instance elaborated : ElaboratedCircuit F (ProvablePair α α) field where
  main
  localLength _ := 2 * size α
  localLength_eq := by simp +arith [circuit_norm, main, diffs, IsZero.main, IsZeroField.circuit]
  subcircuitsConsistent := by simp +arith [circuit_norm, main, diffs, IsZero.main, IsZeroField.circuit]

def Assumptions (_ : α F × α F) : Prop := True

def Spec [DecidableEq (α F)] (input : α F × α F) (output : F) : Prop :=
  output = if input.1 = input.2 then 1 else 0

theorem soundness [DecidableEq (α F)] : Soundness F (elaborated (α := α)) Assumptions Spec := by
  circuit_proof_start [IsZero.main, ProvableType.toElements_fromElements]
  have h_pair := h_input; rw [eval_pair] at h_pair
  have h_x : eval env input_var.1 = input.1 := congrArg Prod.fst h_pair
  have h_y : eval env input_var.2 = input.2 := congrArg Prod.snd h_pair
  simp only [explicit_provable_type] at h_input
  -- Use convert to apply foldl_isZero_eq_one_iff despite Fin/ℕ GetElem mismatch
  set d := diffs input_var.1 input_var.2
  conv_rhs => arg 1; rw [ProvableType.ext_iff]
  -- Provide vals explicitly to help unification
  set vals : Vector F (size α) := Vector.map (Expression.eval env) d
  convert @IsZero.foldl_isZero_eq_one_iff F _ _ (size α) d vals env i₀ rfl ?_ using 1
  · -- (if ∀ i hi, x[i] = y[i] then 1 else 0) = (if ∀ i hi, vals[i] = 0 then 1 else 0)
    -- vals[i] evaluates to (toElements input.1)[i] - (toElements input.2)[i]
    -- so vals[i] = 0 iff input.1[i] = input.2[i]
    have h_vals : ∀ (i : ℕ) (hi : i < size α),
        vals[i] = (toElements input.1)[i] - (toElements input.2)[i] := by
      intro i hi
      show (Vector.map (Expression.eval env) (diffs input_var.1 input_var.2))[i] = _
      simp only [Vector.getElem_map, diffs, Vector.getElem_mapFinRange, Expression.eval, neg_one_mul]
      -- Goal: eval (toVars input_var.1)[⟨i,⋯⟩] + -(eval (toVars input_var.2)[⟨i,⋯⟩]) = input.1[i] - input.2[i]
      erw [ProvableType.getElem_eval_toVars input_var.1 i, ProvableType.getElem_eval_toVars input_var.2 i, h_x, h_y]
      ring
    exact if_congr
      ⟨fun h i hi => by rw [h_vals i hi, h i hi, sub_self],
       fun h i hi => by have := h i hi; rw [h_vals i hi] at this; exact sub_eq_zero.mp this⟩
      rfl rfl
  · exact h_holds

theorem completeness : Completeness F (elaborated (α := α)) Assumptions := by
  circuit_proof_start [IsZeroField.circuit, IsZeroField.Assumptions, IsZero.main, diffs]

def circuit [DecidableEq (α F)] : FormalCircuit F (ProvablePair α α) field := {
  elaborated with Assumptions, Spec, soundness, completeness
}

end Gadgets.IsEqual
