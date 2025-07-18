import Mathlib.Init
import Lean.Meta.Tactic.Simp.SimpTheorems
import Lean.Meta.Tactic.Simp.RegisterCommand
import Lean.LabelAttribute

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

-- Var (ProvablePair a b) -> Var a
-- ProvablePair (A (Expression F)) (B (Expression F)) -> A (Expression F)
-- ProvablePair X Y -> X

class NaturalEval (F : Type) [Field F] (M N : TypeMap) [ProvableType M] [ProvableType N]
  (f_var : Var M F → Var N F) (f_val : outParam (M F → N F)) where
  natural (env : Environment F) (x : Var M F) :
    ProvableType.eval env (f_var x) = f_val (ProvableType.eval env x)

variable {F : Type} [Field F]

/--
First projection from a pair is natural with respect to evaluation.
-/
instance instNaturalEvalFst {A B : TypeMap} [ProvableType A] [ProvableType B] :
    NaturalEval F (ProvablePair A B) A (fun p => p.1) (fun p => p.1) where
  natural (env : Environment F) x := by
    -- We need to show: eval env x.1 = (eval env x).1
    -- Unfold the definition of eval for pairs
    rcases x with ⟨ x, y ⟩
    simp only [eval_pair]

/--
Second projection from a pair is natural with respect to evaluation.
-/
instance instNaturalEvalSnd {A B : TypeMap} [ProvableType A] [ProvableType B] :
    NaturalEval F (ProvablePair A B) B (fun p => p.2) (fun p => p.2) where
  natural env x := by
    rcases x with ⟨ x, y ⟩
    simp only [eval_pair]

/--
Function composition preserves naturality. If f : M → N and g : N → P are both natural
with respect to evaluation, then their composition g ∘ f : M → P is also natural.
-/
instance {M N P : TypeMap} [ProvableType M] [ProvableType N] [ProvableType P]
    (f_var : Var M F → Var N F) (g_var : Var N F → Var P F)
    (f_val : M F → N F) (g_val : N F → P F)
    [NaturalEval F M N f_var f_val] [NaturalEval F N P g_var g_val] :
    NaturalEval F M P (g_var ∘ f_var) (g_val ∘ f_val) where
  natural env x := by
    -- We need to show: eval env (g ∘ f) x = (g ∘ f) (eval env x)
    -- Which expands to: eval env (g (f x)) = g (eval env (f x))
    simp only [Function.comp_apply]
    -- Apply naturality of g
    rw [NaturalEval.natural (f_var := g_var) (f_val := g_val)]
    -- Apply naturality of f
    rw [NaturalEval.natural (f_var := f_var) (f_val := f_val)]

-- Note: This lemma should NOT have the @[circuit_norm] attribute as it can cause
-- infinite reduction cycles. Use it explicitly when needed.
@[natural_eval]
lemma transpose {M N : TypeMap} [ProvableType M] [ProvableType N]
     (f_var : Var M F → Var N F) (f_val : M F → N F)
    [NaturalEval F M N f_var f_val]
    (env : Environment F) (input_var : Var M F) (input : M F)
    (h_eval : ProvableType.eval env input_var = input) :
    ProvableType.eval env (f_var input_var) = f_val input := by
  rw [NaturalEval.natural, h_eval]

section Examples

set_option diagnostics true

/--
Simple example: Working with a pair of field elements.
This demonstrates basic usage of transpose with pair projections.
-/

example (env : Environment F)
    (pair_var : Var (ProvablePair field field) F)
    (pair_val : ProvablePair field field F)
    (h_eval : ProvableType.eval env pair_var = pair_val) :
    ProvableType.eval env pair_var.1 = pair_val.1 := by
  simp only [natural_eval, h_eval]
