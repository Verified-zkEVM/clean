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

The challenge library avoids this by never reading a constraint symbolically. Gadgets have
pointwise specs, at an arbitrary `α`; only at a boundary (`AssertIdentity`) is a value read as a
rational function `R` (`x ≙[α] R`), and `R` is built from committed values only, so that its bad
challenges are bounded by its degree. A user who wants `w * w = α` has no such `R`: `w` is chosen
after the challenge, so it cannot be a committed value.
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
