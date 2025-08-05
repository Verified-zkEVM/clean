import Clean.Circuit.Basic
import Clean.Circuit.Provable
import Clean.Circuit.Theorems
import Clean.Circuit.Loops
import Clean.Gadgets.IsZeroField
import Clean.Utils.Field
import Clean.Utils.Tactics

namespace Gadgets.IsZero

variable {F : Type} [Field F] [DecidableEq F]
variable {M : TypeMap} [ProvableType M]

/--
Main circuit that checks if all components of a ProvableType are zero.
Returns 1 if all components are 0, otherwise returns 0.
-/
def main (input : Var M F) : Circuit F (Var field F) := do
  let elemVars := toVars input
  -- Use foldlRange to multiply all IsZero results together
  -- Start with 1, and for each element, multiply by its IsZero result
  let result ← Circuit.foldlRange (size M) (1 : Expression F) fun acc i => do
    let isZeroElem ← IsZeroField.circuit elemVars[i]
    return acc * isZeroElem
  return result

instance elaborated : ElaboratedCircuit F M field where
  main
  localLength _ := 2 * size M
  localLength_eq := by
    simp +arith [circuit_norm, main, IsZeroField.circuit.localLength_eq, IsZeroField.circuit]
  subcircuitsConsistent := by
    simp +arith [circuit_norm, main, IsZeroField.circuit.localLength_eq, IsZeroField.circuit]

def Assumptions (_ : M F) : Prop := True

def Spec (input : M F) (output : F) : Prop :=
  output = if (∀ i : Fin (size M), (toElements input)[i] = 0) then 1 else 0

/--
lemma for soundness. Separate because the statement is optimized for induction.
-/
lemma foldl_isZero_eq_one_iff {n : ℕ} {vars : Vector (Expression F) n} {vals : Vector F n}
    {env : Environment F} {i₀ : ℕ}
    (h_eval : Vector.map (Expression.eval env) vars = vals)
    (h_isZero : ∀ (i : Fin n),
      IsZeroField.circuit.Assumptions (Expression.eval (F:=F) env vars[i]) →
        IsZeroField.circuit.Spec (Expression.eval (F:=F) env vars[i])
          (Expression.eval (F:=F) env
            (IsZeroField.circuit.output vars[i]
              (i₀ + i * IsZeroField.circuit.localLength vars[i])))) :
    Expression.eval env
      (Fin.foldl n
        (fun acc i => acc * (IsZeroField.circuit.output vars[i] (i₀ + i * IsZeroField.circuit.localLength vars[i]) : Var field F))
        1) =
    if ∀ (i : Fin n), vals[i] = 0 then 1 else 0 := by
  simp only [IsZeroField.circuit, IsZeroField.Assumptions, IsZeroField.Spec] at h_isZero
  induction n generalizing i₀
  · simp only [id_eq, Fin.getElem_fin, Fin.foldl_zero, IsEmpty.forall_iff, ↓reduceIte, Expression.eval]
  · rename_i pre h_ih
    simp only [Fin.foldl_succ_last, Expression.eval]
    let vars_pre := vars.take pre |>.cast (by simp : min pre (pre + 1) = pre)
    let vals_pre := vals.take pre |>.cast (by simp : min pre (pre + 1) = pre)
    have h_eval_pre : Vector.map (Expression.eval env) vars_pre = vals_pre := by
      simp only [Vector.take_eq_extract, add_tsub_cancel_right, Vector.extract_eq_pop,
        Nat.add_one_sub_one, Nat.sub_zero, Vector.cast_cast, Vector.cast_rfl, Vector.map_pop,
        vals_pre, vars_pre, h_eval]
    specialize h_ih h_eval_pre (i₀:=i₀)
    simp only [vars_pre, vals_pre] at *
    simp only [Nat.add_one_sub_one, Vector.drop_eq_cast_extract, Vector.cast_rfl, Fin.getElem_fin,
      Vector.getElem_cast, Vector.getElem_extract, forall_const, id_eq] at h_ih
    simp only [id_eq, Fin.getElem_fin, Fin.coe_castSucc, Fin.val_last]
    specialize h_ih (by
      intro i
      specialize h_isZero i
      norm_num at h_isZero ⊢
      simp only [Nat.add_one_sub_one, Nat.sub_zero, Vector.getElem_cast, Vector.getElem_pop',
        h_isZero])
    simp only [Vector.getElem_take] at h_ih
    rw [h_ih]
    specialize h_isZero pre trivial
    norm_num at h_isZero ⊢
    simp only [h_isZero, Fin.forall_fin_succ']
    norm_num
    split
    · rename_i h
      simp only [h]
      simp only [implies_true, true_and, ← h_eval, Vector.getElem_map]
    · rename_i h
      simp only [h]
      simp only [false_and, ↓reduceIte]

theorem soundness : Soundness F (elaborated (M := M)) Assumptions Spec := by
  circuit_proof_start
  let s := size M
  let vars : Vector (Expression F) s := toElements (M:=M) input_var
  let vals : Vector F s := toElements (M:=M) input
  -- need to change h_ionput into an element-wise condition
  simp only [Parser.Attr.explicit_provable_type, ProvableType.eval] at h_input
  simp only [ProvableType.fromElements_eq_iff] at h_input
  apply foldl_isZero_eq_one_iff
  · assumption
  · assumption

theorem completeness : Completeness F (elaborated (M := M)) Assumptions := by
  circuit_proof_start [IsZeroField.circuit, IsZeroField.Assumptions]

def circuit : FormalCircuit F M field := {
  elaborated with Assumptions, Spec, soundness, completeness
}

end Gadgets.IsZero
