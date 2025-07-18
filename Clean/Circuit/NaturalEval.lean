import Mathlib.Init
import Lean.Meta.Tactic.Simp.SimpTheorems
import Lean.Meta.Tactic.Simp.RegisterCommand
import Lean.LabelAttribute

import Clean.Circuit.Provable
import Clean.Circuit.Expression
import Clean.Circuit.Basic

variable (F : Type) [Field F]

@[natural_eval]
lemma reduce_fst {M N : TypeMap} [ProvableType M] [ProvableType N] env (i_var : Var (ProvablePair M N) F) :
    eval env i_var.1 = (eval env i_var).1 := by
  rw [eval_pair]

@[natural_eval]
lemma reduce_snd {M N : TypeMap} [ProvableType M] [ProvableType N] env (i_var : Var (ProvablePair M N) F) :
    eval env i_var.2 = (eval env i_var).2 := by
  rw [eval_pair]

@[natural_eval]
lemma reduce_vector_get {M : TypeMap} [NonEmptyProvableType M] {n : ℕ} env
    (v_var : Var (ProvableVector M n) F) (i : Fin n) :
    eval env v_var[i] = (eval env v_var)[i] := by apply getElem_eval_vector
