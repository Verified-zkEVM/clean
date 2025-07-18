import Clean.Circuit.Provable
import Clean.Circuit.Expression
import Clean.Circuit.Basic

/-!
# Natural Transformation Framework for `eval env`

This module provides a systematic framework for handling the natural transformation
property of `eval env : Expression F → F`. The key insight is that evaluation commutes
with most structural operations in our circuit framework.

## Main definitions

* Lemmas that capture the naturality of evaluation for various operations
* A tactic `natural_eval` that automatically applies these lemmas

## Implementation notes

The key patterns we handle:
1. Struct field projections: `eval env s.field = (eval env s).field`
2. Vector operations: `eval env (v.map f) = (eval env v).map (eval env ∘ f)`
3. Struct construction: `eval env ⟨x, y⟩ = ⟨eval env x, eval env y⟩`
4. Property preservation through evaluation
-/

open ProvableType ProvableStruct

variable {F : Type} [Field F]

/--
For ProvableStruct types, when we know the whole struct evaluates to a value,
we can extract what each component evaluates to.
-/
theorem eval_struct_component {α : TypeMap} [ProvableStruct α]
    (env : Environment F) (struct_var : Var α F) (struct_val : α F)
    (h_eval : ProvableType.eval env struct_var = struct_val) :
    ProvableStruct.toComponents (α := α) (ProvableType.eval env struct_var) = 
    ProvableStruct.toComponents struct_val := by
  rw [h_eval]

/--
When a struct is constructed from components, evaluating the struct
is the same as constructing from evaluated components.
-/
theorem eval_struct_from_components {α : TypeMap} [ProvableStruct α]
    (env : Environment F) (comps : ProvableTypeList (Expression F) (components α)) :
    ProvableType.eval env (fromComponents comps : α (Expression F)) = 
    fromComponents (ProvableStruct.eval.go env (components α) comps) := by
  -- Use ProvableStruct.eval definition
  rw [ProvableStruct.eval_eq_eval]
  simp only [ProvableStruct.eval]
  -- Need to show toComponents (fromComponents comps) = comps
  rw [toComponents_fromComponents]

/--
Evaluation distributes over vector construction.
-/
theorem eval_vector_mk {α : TypeMap} [NonEmptyProvableType α] {n : ℕ}
    (env : Environment F) (elems : Var (ProvableVector α n) F) :
    ProvableType.eval env elems = Vector.map (ProvableType.eval env) elems := by
  exact eval_vector env elems

/--
For the common pattern where we need to show a property holds after evaluation.
If P holds for the evaluated value, it holds for the evaluation of the variable.
-/
theorem eval_preserves_property {α : TypeMap} [ProvableType α]
    (P : α F → Prop) (env : Environment F) (var : Var α F) (val : α F)
    (h_eval : ProvableType.eval env var = val) (h_prop : P val) :
    P (ProvableType.eval env var) := by
  rw [h_eval]
  exact h_prop

/--
Vector indexing commutes with evaluation.
-/
theorem eval_vector_get {α : TypeMap} [NonEmptyProvableType α] {n : ℕ}
    (env : Environment F) (v : Var (ProvableVector α n) F) (i : Fin n) :
    ProvableType.eval env v[i] = (ProvableType.eval env v)[i] := by
  exact getElem_eval_vector env v i i.2

/--
Common pattern in circuit proofs: When we have a struct equality after evaluation,
we can extract field equalities. This is the pattern that replaces `injection`.
-/
theorem eval_struct_injective {α : TypeMap} [ProvableStruct α]
    (env : Environment F) (struct_var : Var α F) (struct_val : α F)
    (h_eval : ProvableType.eval env struct_var = struct_val) :
    ProvableStruct.toComponents (ProvableType.eval env struct_var) = 
    ProvableStruct.toComponents struct_val := by
  rw [h_eval]

/--
For the specific pattern with struct reconstruction that appears frequently.
If we know a struct evaluates to a certain value, and we reconstruct the struct
from its fields, the reconstruction equals the original value.
-/
theorem eval_struct_reconstruction {α : TypeMap} [ProvableStruct α]
    (env : Environment F) (s_var : Var α F) (s_val : α F)
    (h_eval : ProvableType.eval env s_var = s_val) :
    fromComponents (toComponents (ProvableType.eval env s_var)) = s_val := by
  rw [h_eval, fromComponents_toComponents]

/--
Specialized lemma for the common pattern where we need to prove something about
a casted evaluation result.
-/
theorem eval_with_cast {α β : TypeMap} [ProvableType α] [ProvableType β]
    (env : Environment F) (var : Var α F) (val : α F)
    (cast : α F → β F)
    (h_eval : ProvableType.eval env var = val) :
    cast (ProvableType.eval env var) = cast val := by
  rw [h_eval]

/--
Tactic for automatically applying natural evaluation lemmas.
This simplifies proofs involving `eval env` on structured data.
-/
macro "natural_eval" : tactic => 
  `(tactic| simp only [eval_struct_component, eval_struct_from_components, 
                      eval_vector_mk, eval_preserves_property, eval_vector_get,
                      eval_struct_reconstruction, eval_with_cast])

/--
Extended version that also applies circuit_norm simplifications.
-/
macro "natural_eval!" : tactic => 
  `(tactic| simp only [eval_struct_component, eval_struct_from_components, 
                      eval_vector_mk, eval_preserves_property, eval_vector_get,
                      eval_struct_reconstruction, eval_with_cast, circuit_norm])

/--
Tactic that combines natural_eval with common proof patterns.
Use this when you have `eval env struct_var = struct_val` and need field equalities.
-/
macro "natural_eval_struct" h:ident : tactic => 
  `(tactic| (
    have := eval_struct_injective _ _ _ $h;
    natural_eval!
  ))