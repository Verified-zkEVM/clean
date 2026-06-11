import Clean.Orchard.Ecc.Defs
import Mathlib.Tactic

open CompElliptic.Curves.Pasta.Pallas CompElliptic.CurveForms

namespace Orchard.Ecc

namespace Point

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
