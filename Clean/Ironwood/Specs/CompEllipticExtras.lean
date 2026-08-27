import CompElliptic.CurveForms.ShortWeierstrass
import CompElliptic.Fields.Pasta

/-!
# Clean-side additions to CompElliptic

Small generic lemmas (and the `Fp`/`Fq` field abbreviations) that the formerly vendored
CompElliptic copy carried on top of upstream `daira/CompElliptic`, kept in CompElliptic's
own namespaces so call sites read as the natural continuations — all candidates for
upstreaming. The Pallas-side curve twins (`neg_five_not_isCube`/`no_onCurve_y_zero`)
live in `Zcash.Circuits.Specs.Pallas`.
-/

namespace CompElliptic.Fields.Pasta

/-- The Pallas base field (= the Vesta scalar field). -/
abbrev Fp := PallasBaseField

/-- The Pallas scalar field (= the Vesta base field). -/
abbrev Fq := PallasScalarField

end CompElliptic.Fields.Pasta

namespace CompElliptic.CurveForms.ShortWeierstrass

variable {F : Type*} [Field F] [DecidableEq F]

lemma SWPoint.add_x {E : SWCurve F} (P Q : SWPoint E) :
    (P + Q).x = (add E.A (P.x, P.y) (Q.x, Q.y)).1 := rfl

lemma SWPoint.add_y {E : SWCurve F} (P Q : SWPoint E) :
    (P + Q).y = (add E.A (P.x, P.y) (Q.x, Q.y)).2 := rfl

omit [DecidableEq F] in
/-- Two points on the curve sharing an `x`-coordinate have equal or opposite `y`. -/
theorem y_eq_or_y_eq_neg_of_onCurve {a b x y₁ y₂ : F}
    (h₁ : OnCurve a b (x, y₁)) (h₂ : OnCurve a b (x, y₂)) : y₁ = y₂ ∨ y₁ = -y₂ := by
  have h : (y₁ - y₂) * (y₁ + y₂) = 0 := by
    simp only [OnCurve] at h₁ h₂
    linear_combination h₁ - h₂
  rcases mul_eq_zero.mp h with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · exact Or.inr (by linear_combination h)

omit [DecidableEq F] in
/-- A nonzero representable point is on the curve. -/
theorem SWPoint.onCurve_of_ne_zero {E : SWCurve F} {P : SWPoint E} (h : P ≠ 0) :
    OnCurve E.A E.B (P.x, P.y) := by
  rcases P.onCurve with hc | h0
  · exact hc
  · exact absurd (SWPoint.ext_pair (by rw [h0]; rfl)) h

omit [DecidableEq F] in
/-- Nonzero representable points sharing an `x`-coordinate are equal or opposite. -/
theorem SWPoint.eq_or_eq_neg_of_x_eq {E : SWCurve F} {P Q : SWPoint E}
    (hP : P ≠ 0) (hQ : Q ≠ 0) (h : P.x = Q.x) : P = Q ∨ P = -Q := by
  have hPC := onCurve_of_ne_zero hP
  have hQC := onCurve_of_ne_zero hQ
  rw [h] at hPC
  rcases y_eq_or_y_eq_neg_of_onCurve hPC hQC with hy | hy
  · exact Or.inl (ext_pair (by rw [h, hy]))
  · exact Or.inr (ext_pair (by rw [h, hy]; rfl))

end CompElliptic.CurveForms.ShortWeierstrass
