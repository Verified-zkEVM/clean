import Clean.Circuit

open Clean

namespace Witgen

/-- A bounded table read evaluates the selected expression. -/
theorem evalList_map_expr {F : Type} [FiniteField F] (ctx : Ctx F)
    (xs : List (Expression F)) (i : ℕ) (hi : i < xs.length) :
    FExprOver.evalList ctx i (xs.map FExpr.expr) = Expression.eval ctx.env.toEnvironment xs[i] := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih i (Nat.lt_of_succ_lt_succ hi)

/-- The bounds premise rules out the interpreter's out-of-range default. -/
theorem eval_vector_read {F : Type} [FiniteField F] {n : ℕ} (ctx : Ctx F)
    (xs : Vector (Expression F) n) (index : NExpr F) (hi : index.eval ctx < n) :
    (xs[index]).eval ctx = Expression.eval ctx.env.toEnvironment xs[index.eval ctx] := by
  change FExprOver.evalList ctx (index.eval ctx) (xs.toList.map FExpr.expr) = _
  rw [evalList_map_expr ctx xs.toList _ (by simpa using hi)]
  rfl

/-- A bounded read of constants evaluates the selected constant. -/
theorem evalList_map_const {F : Type} [FiniteField F] (ctx : Ctx F)
    (xs : List F) (i : ℕ) (hi : i < xs.length) :
    FExprOver.evalList ctx i (xs.map (fun x => (FExpr.const x : FExpr F))) = xs[i] := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih i (Nat.lt_of_succ_lt_succ hi)

/-- The bounds premise rules out the interpreter's out-of-range default. -/
theorem eval_vector_const_read {F : Type} [FiniteField F] {n : ℕ} (ctx : Ctx F)
    (xs : Vector F n) (index : NExpr F) (hi : index.eval ctx < n) :
    (xs[index]).eval ctx = xs[index.eval ctx] := by
  change FExprOver.evalList ctx (index.eval ctx) (xs.toList.map (fun x => (FExpr.const x : FExpr F))) = _
  rw [evalList_map_const ctx xs.toList _ (by simpa using hi)]
  rfl

/-- Expose the IR operator without unfolding natural-number XOR. -/
theorem eval_xor {F : Type} [FiniteField F] (ctx : Ctx F) (a b : NExpr F) :
    (a ^^^ b).eval ctx = a.eval ctx ^^^ b.eval ctx := rfl

/-- Expose IR division without unfolding natural-number division. -/
theorem eval_div {F : Type} [FiniteField F] (ctx : Ctx F) (a b : NExpr F) :
    (a / b).eval ctx = a.eval ctx / b.eval ctx := rfl

/-- Expose IR reduction modulo an evaluated modulus. -/
theorem eval_mod {F : Type} [FiniteField F] (ctx : Ctx F) (a b : NExpr F) :
    (a % b).eval ctx = a.eval ctx % b.eval ctx := rfl

end Witgen
