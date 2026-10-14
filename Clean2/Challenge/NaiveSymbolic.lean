/-
Why challenges are not read as polynomial variables.

The tempting semantics: a challenge is a fresh variable `X`, and a constraint that mentions it is
an identity in `F[X]`. For the cells that the prover fills after the challenge, that would mean
a polynomial (or rational function) in `X`. But a cheating prover chooses those cells after seeing
`α`, as arbitrary functions of it.

The constraint `w * w = α`, with `w` chosen after `α`:
- symbolically, no polynomial `w` satisfies `w * w = X` (`not_exists_mul_self_eq_X`). Every claim
  about such a circuit would hold vacuously, at "soundness error zero";
- pointwise, it is satisfied at every square `α` (`exists_mul_self_eq_of_isSquare`), which is
  about half of all challenges in an odd prime field.

`ChallengeCheck` avoids this by never interpreting a constraint symbolically. The constraints
are checked pointwise, at an arbitrary `α`, and only the conclusion, a polynomial built from the
phase-1 values, is symbolic. For this circuit, the best pointwise spec is `IsSquare α`. That is a
root condition only for `α ^ ((p - 1) / 2) - 1` (times `α`), of degree about `p / 2`, so the bound
`ncard_accepting_le` gives is about `1 / 2`: correct, and useless.
-/
module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Group.Even

@[expose] public section

namespace Clean2.NaiveSymbolic
open Polynomial

variable {F : Type} [Field F]

/-- Symbolically, `w * w = X` has no solution. -/
theorem not_exists_mul_self_eq_X : ¬∃ w : F[X], w * w = X := by
  rintro ⟨w, h⟩
  have hw : w ≠ 0 := by
    rintro rfl
    exact X_ne_zero (by rw [← h, zero_mul])
  have h_deg := congrArg natDegree h
  rw [natDegree_mul hw hw, natDegree_X] at h_deg
  omega

/-- Pointwise, it is satisfied at every square. -/
theorem exists_mul_self_eq_of_isSquare {α : F} (h : IsSquare α) : ∃ w : F, w * w = α := by
  obtain ⟨r, hr⟩ := h
  exact ⟨r, hr.symm⟩

end Clean2.NaiveSymbolic
