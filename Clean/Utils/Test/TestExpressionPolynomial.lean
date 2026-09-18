/-
Copyright (c) 2024-2025 zkSecurity, LLC
Released under MIT license as described in the file LICENSE.
-/
/-
  Clean.Utils.Test.TestExpressionPolynomial
-/

module

public import Clean.Circuit.ExpressionPolynomial
public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

/-!
# Expression polynomial controls

Multiplication of two columns has degree two. A width-two row accepts indices zero and one
and rejects index two; the range proof cannot be manufactured from array defaulting.
-/

namespace TestExpressionPolynomial

public section

def product : Expression ℚ := .mul (.var ⟨0⟩) (.var ⟨1⟩)

example : product.degreeBound = 2 := rfl
example : product.WithinWidth 2 := by decide
example : ¬ (Expression.var (F:=ℚ) ⟨2⟩).WithinWidth 2 := by decide

example : product.toMvPolynomial.totalDegree = 2 := by
  simp [product, Expression.toMvPolynomial, MvPolynomial.totalDegree_mul_of_isDomain
    (MvPolynomial.X_ne_zero (R:=ℚ) (0 : ℕ)) (MvPolynomial.X_ne_zero (R:=ℚ) (1 : ℕ))]

example : MvPolynomial.eval (fun i : Fin 2 ↦ (#v[3, 7] : Vector ℚ 2)[i.val])
    (product.toBoundedPolynomial 2 (by decide)) = 21 := by
  norm_num [product, Expression.toBoundedPolynomial]

example (data : ProverData ℚ) :
    product.eval (Environment.fromArray #[3, 7] data) = 21 := by
  rw [← Expression.eval_toBoundedPolynomial 2 product (by decide) #v[3, 7] data]
  norm_num [product, Expression.toBoundedPolynomial]

example : (Expression.const (0 : ℚ)).toMvPolynomial = 0 := by
  simp [Expression.toMvPolynomial]

example : ¬ (Expression.var (F:=ℚ) ⟨0⟩).WithinWidth 0 := by decide

example : ((Expression.const (0 : ℚ)).toBoundedPolynomial 0 (by decide)).totalDegree = 0 := by
  simp [Expression.toBoundedPolynomial]

example (data : ProverData ℚ) :
    (Expression.const (7 : ℚ)).eval (Environment.fromArray #[] data) = 7 := by
  rw [← Expression.eval_toBoundedPolynomial 0 (.const 7) (by decide) #v[] data]
  simp [Expression.toBoundedPolynomial]

end
end TestExpressionPolynomial
