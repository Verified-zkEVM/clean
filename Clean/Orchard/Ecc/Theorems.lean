import Clean.Orchard.Ecc.Defs
import Mathlib.Tactic

open CompElliptic.Curves.Pasta.Pallas CompElliptic.CurveForms

namespace Orchard.Ecc

namespace Point

theorem ext_coords {F : Type} {p q : Point F} (h : p.coords = q.coords) : p = q := by
  rcases p with ⟨px, py⟩
  rcases q with ⟨qx, qy⟩
  simpa [Point.coords, Prod.ext_iff, Point.mk.injEq] using h

lemma neg_coords (point : Point Fp) :
    point.neg.coords = ShortWeierstrass.neg point.coords := by
  simp only [Point.neg, Point.coords, ShortWeierstrass.neg]

theorem valid_neg {point : Point Fp} (h : Valid point.coords) :
    Valid point.neg.coords := by
  rw [neg_coords]
  exact ShortWeierstrass.valid_neg h

theorem not_onCurve_of_x_eq_zero (y : Fp) :
    ¬ OnCurve ({ x := 0, y } : Point Fp).coords := by
  apply CompElliptic.Curves.Pasta.Pallas.no_onCurve_x_zero y

theorem ne_zero_of_onCurve {point : Point Fp}
  (hPoint : OnCurve point.coords) :
    point ≠ zero := by
  rcases point with ⟨x, y⟩
  intro hIdentity
  simp only [zero, mk.injEq] at hIdentity
  rw [hIdentity.1] at hPoint
  exact not_onCurve_of_x_eq_zero y hPoint

theorem y_eq_zero_of_valid_of_x_eq_zero {point : Point Fp}
  (hPoint : Valid point.coords) :
    point.x = 0 → point.y = 0 := by
  rcases point with ⟨x, y⟩
  simp only [Point.coords] at *
  intro hx
  rcases hPoint with hCurve | hIdentity
  · rw [hx] at hCurve
    nomatch not_onCurve_of_x_eq_zero y hCurve
  · simp_all

theorem y_ne_zero_of_valid_of_x_ne_zero {point : Point Fp}
    (hPoint : Valid point.coords) (hx : point.x ≠ 0) :
    point.y ≠ 0 := by
  rcases point with ⟨x, y⟩
  simp only [Point.coords] at *
  rintro rfl
  rcases hPoint with hCurve | hIdentity
  · apply no_onCurve_y_zero x hCurve
  · simp_all

end Orchard.Ecc.Point

namespace Orchard.Ecc

/-! ### Pallas group order -/

open CompElliptic.Fields.Pasta (PALLAS_SCALAR_CARD)

/--
**Axiom**: the Pallas curve group has exactly `q = PALLAS_SCALAR_CARD` points.

This is the published point count of the Pallas curve. The vendored CompElliptic
formalization has no point counting, so this is the one central trust assumption behind
scalar-multiplication circuit proofs; all consumers needing order facts derive them from
here (see `pallas_addOrderOf`).
-/
axiom pallas_natCard :
    Nat.card (ShortWeierstrass.SWPoint curve) = PALLAS_SCALAR_CARD

/-- Every non-identity Pallas point generates the full prime-order group. -/
theorem pallas_addOrderOf {P : ShortWeierstrass.SWPoint curve} (h : P ≠ 0) :
    addOrderOf P = PALLAS_SCALAR_CARD := by
  have hdvd := addOrderOf_dvd_natCard P
  rw [pallas_natCard] at hdvd
  rcases CompElliptic.Fields.Pasta.PALLAS_SCALAR_is_prime.eq_one_or_self_of_dvd
      _ hdvd with h1 | hq
  · exact absurd (AddMonoid.addOrderOf_eq_one_iff.mp h1) h
  · exact hq

end Orchard.Ecc
