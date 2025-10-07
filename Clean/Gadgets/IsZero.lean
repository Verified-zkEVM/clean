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
Main circuit that checks if all elements of a ProvableType are zero.
Returns 1 if all elementts are 0, otherwise returns 0.
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
    simp +arith [circuit_norm, main, IsZeroField.circuit]
  yields_eq := by
    intros; simp [circuit_norm, main, IsZeroField.circuit]
  subcircuitsConsistent := by
    simp +arith [circuit_norm, main, IsZeroField.circuit]

def Assumptions (_ : M F) : Prop := True

def Spec [DecidableEq (M F)] (input : M F) (output : F) : Prop :=
  output = if input = 0 then 1 else 0

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
    if ∀ (i : ℕ) (x : i < n), vals[i] = 0 then 1 else 0 := by
  simp only [IsZeroField.circuit, IsZeroField.Assumptions, IsZeroField.Spec] at h_isZero
  induction n generalizing i₀
  · simp only [id_eq, Fin.getElem_fin, Fin.foldl_zero, Expression.eval]
    simp only [not_lt_zero', IsEmpty.forall_iff, implies_true, ↓reduceIte]
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
    simp only [Fin.getElem_fin,
      Vector.getElem_cast, forall_const, id_eq] at h_ih
    simp only [id_eq, Fin.getElem_fin, Fin.coe_castSucc, Fin.val_last]
    specialize h_ih (by
      intro i
      specialize h_isZero i.castSucc
      norm_num at h_isZero ⊢
      simp only [Nat.add_one_sub_one, Nat.sub_zero, Vector.getElem_cast, Vector.getElem_pop',
        h_isZero])
    simp only [Vector.getElem_take] at h_ih
    rw [h_ih]
    specialize h_isZero (.last pre) trivial
    norm_num at h_isZero ⊢
    simp only [h_isZero]
    split_ifs <;> try rfl
    · rename_i h_smaller h_last h_all
      apply False.elim
      apply h_all
      intro i
      by_cases h : i < pre
      · intro _
        aesop
      intro _
      have : i = pre := by omega
      aesop
    · rename_i h_smaller h_last h_all
      apply False.elim
      apply h_last
      aesop
    · aesop

theorem soundness [DecidableEq (M F)] : Soundness F (elaborated (M := M)) Assumptions Spec := by
  circuit_proof_start
  simp only [explicit_provable_type, ProvableType.fromElements_eq_iff] at h_input
  conv_rhs =>
    arg 1
    rw [Zero.toOfNat0, OfNat.ofNat]
    simp only [Zero.zero]
    rw [ProvableType.fromElements_eq_iff']
    rw [Vector.ext_iff]
    simp only [Vector.getElem_replicate]
  apply foldl_isZero_eq_one_iff <;> assumption

theorem completeness : Completeness F (elaborated (M := M)) Assumptions := by
  circuit_proof_start [IsZeroField.circuit, IsZeroField.Assumptions]

def circuit [DecidableEq (M F)] : FormalCircuit F M field := {
  elaborated with Assumptions, Spec, soundness, completeness
}

end Gadgets.IsZero
