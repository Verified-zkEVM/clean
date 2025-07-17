import Clean.Circuit.Basic
import Clean.Circuit.Provable

/-!
# Automatic derivation of eval equations

This module provides lemmas and tactics for automatically deriving equations
of the form `eval env (suffix input_var) = suffix input` from a main assumption
`h_input : eval env input_var = input`.

This allows avoiding manual decomposition of compound inputs into individual equations.
-/

variable {F : Type} [Field F]

namespace EvalDerive

-- Lemma for pair first projection
@[circuit_norm]
theorem eval_pair_fst {α β : TypeMap} [ProvableType α] [ProvableType β]
    (env : Environment F) (p : Var (ProvablePair α β) F) :
    eval env p.1 = (eval env p).1 := by
  rw [eval_pair]

-- Lemma for pair second projection
@[circuit_norm]
theorem eval_pair_snd {α β : TypeMap} [ProvableType α] [ProvableType β]
    (env : Environment F) (p : Var (ProvablePair α β) F) :
    eval env p.2 = (eval env p).2 := by
  rw [eval_pair]

-- Lemma for vector indexing with ProvableVector
@[circuit_norm]
theorem eval_provable_vector_index {α : TypeMap} [NonEmptyProvableType α] {n : ℕ}
    (env : Environment F) (v : Var (ProvableVector α n) F) (i : Fin n) :
    eval env v[i] = (eval env v)[i] := by
  rw [eval_vector]
  simp [Vector.getElem_map]

-- Lemma for fields vector indexing
@[circuit_norm]
theorem eval_fields_index {n : ℕ}
    (env : Environment F) (v : Var (fields n) F) (i : Fin n) :
    v[i].eval env = (eval env v)[i] := by
  -- The key observation: v is of type Vector (Expression F) n
  -- and eval for fields n just maps Expression.eval over the vector
  simp only [eval, toVars, toElements, fromElements, fields]
  -- Now we have: v[i].eval env = (Vector.map (Expression.eval env) v)[i]
  -- This is exactly what Vector.getElem_map gives us
  exact (Vector.getElem_map (Expression.eval env) (i.2)).symm

-- Triple decomposition lemmas
@[circuit_norm]
theorem eval_triple_1 (env : Environment F) (t : Var fieldTriple F) :
    t.1.eval env = (eval env t).1 := by
  simp only [eval, toElements, fromElements, fieldTriple, Expression.eval]
  rfl

@[circuit_norm]
theorem eval_triple_2_1 (env : Environment F) (t : Var fieldTriple F) :
    t.2.1.eval env = (eval env t).2.1 := by
  simp only [eval, toElements, fromElements, fieldTriple, Expression.eval]
  rfl

@[circuit_norm]
theorem eval_triple_2_2 (env : Environment F) (t : Var fieldTriple F) :
    t.2.2.eval env = (eval env t).2.2 := by
  simp only [eval, toElements, fromElements, fieldTriple, Expression.eval]
  rfl

-- Convenience tactic for decomposing eval assumptions
macro "eval_decompose" h:ident : tactic => `(tactic|
  simp only [eval_pair_fst, eval_pair_snd, eval_fields_index,
             eval_triple_1, eval_triple_2_1, eval_triple_2_2] at $h ⊢
)

end EvalDerive

-- Example usage:
example {env : Environment F} {input_var : Var (ProvablePair field field) F}
    {input : ProvablePair field field F}
    (h_input : eval env input_var = input) :
    eval env input_var.1 = input.1 ∧ eval env input_var.2 = input.2 := by
  rw [EvalDerive.eval_pair_fst, EvalDerive.eval_pair_snd, h_input]
  exact ⟨rfl, rfl⟩

-- Example with triple decomposition
example {env : Environment F} {input_var : Var fieldTriple F} {input : fieldTriple F}
    (h_input : eval env input_var = input) :
    input_var.1.eval env = input.1 ∧
    input_var.2.1.eval env = input.2.1 ∧
    input_var.2.2.eval env = input.2.2 := by
  eval_decompose h_input
  rw [h_input]
  exact ⟨rfl, rfl, rfl⟩

-- Example showing how to use with existing patterns in the codebase
example {env : Environment F} {input_var : Var fieldTriple F}
    {x y carry_in : F}
    (h_inputs : eval env input_var = (x, y, carry_in)) :
    input_var.1.eval env = x ∧ input_var.2.1.eval env = y ∧ input_var.2.2.eval env = carry_in := by
  -- Before: would need manual decomposition
  -- Now: can use the lemmas
  have h1 : input_var.1.eval env = (eval env input_var).1 :=
    EvalDerive.eval_triple_1 env input_var
  have h2 : input_var.2.1.eval env = (eval env input_var).2.1 :=
    EvalDerive.eval_triple_2_1 env input_var
  have h3 : input_var.2.2.eval env = (eval env input_var).2.2 :=
    EvalDerive.eval_triple_2_2 env input_var
  rw [h_inputs] at h1 h2 h3
  exact ⟨h1, h2, h3⟩

-- Alternative approach using the tactic
example {env : Environment F} {input_var : Var fieldTriple F}
    {x y carry_in : F}
    (h_inputs : eval env input_var = (x, y, carry_in)) :
    input_var.1.eval env = x ∧ input_var.2.1.eval env = y ∧ input_var.2.2.eval env = carry_in := by
  eval_decompose h_inputs
  rw [h_inputs]
  exact ⟨rfl, rfl, rfl⟩
