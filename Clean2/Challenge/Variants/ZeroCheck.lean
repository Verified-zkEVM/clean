/-
A zero check, as a user writes it: `c` is the zero vector, by checking `∑ c i * α ^ i = 0`.

One identity, no division: complete at every challenge, error bound `n - 1`. The symbolic
argument is that a polynomial is zero exactly when its coefficients are.
-/
module

public import Clean2.Challenge.Variants.Identity

@[expose] public section

namespace Clean2
open Polynomial

namespace ZeroCheck
variable {Native : Type} [Field Native]

/-- The symbolic argument: the coefficients of the zero polynomial are zero. -/
theorem eq_zero_of_sum_eq_zero {n : ℕ} {c : Fin n → Native}
    (h : ∑ i, RatFunc.C (c i) * RatFunc.X ^ (i : ℕ) = 0) : ∀ i, c i = 0 := by
  have h_poly : ∑ i : Fin n, Polynomial.C (c i) * Polynomial.X ^ (i : ℕ) = 0 := by
    apply RatFunc.algebraMap_injective Native
    simpa [map_sum, RatFunc.algebraMap_C, RatFunc.algebraMap_X] using h
  intro j
  have h_coeff := congrArg (fun p => p.coeff j) h_poly
  simpa [finsetSum_coeff, coeff_C_mul_X_pow, Fin.val_inj] using h_coeff

/-- `c` is zero. -/
@[reducible]
def interface (n : ℕ) : Interface Native where
  input := Vector Native n × Native
  inputCType := .natives n ×ᵗ .native
  output := Unit
  outputCType := .unit
  Spec := fun (c, _) _ => ∀ i : Fin n, c[i] = 0
  ProverAssumptions := fun (c, _) => ∀ i : Fin n, c[i] = 0

/-- `∑ c i * X ^ i`. -/
def expr (n : ℕ) : RExpr Native n := .sum n fun i => .leaf i * .X ^ (i : ℕ)

variable {B : Backend} [Field B.Native]
  (identity : ∀ {k : ℕ} (e : RExpr B.Native k), Impl B (Identity.interface e))

def impl (n : ℕ) : Impl B (interface n) where
  main | (c, α) => identity (expr n) (c, α)
  soundness := by
    intro s env (c, α) _ h
    simp only [circuit_norm] at h ⊢
    exact eq_zero_of_sum_eq_zero (by simpa [expr] using h (by simp [expr]))
  completeness := by
    intro s env (c, α) _ h_prover
    simp only [circuit_norm] at h_prover ⊢
    exact ⟨by simp [expr], by simp [expr, h_prover], by simp [expr]⟩

end ZeroCheck
end Clean2
