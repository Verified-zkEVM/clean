import Clean.Orchard.Ecc.Defs
import Mathlib.Tactic

namespace Orchard
namespace Ecc

namespace Point

theorem isPointOrIdentity_neg {point : Point Fp}
    (h : Point.isPointOrIdentity point) :
    Point.isPointOrIdentity (Point.neg point) := by
  rcases point with ⟨x, y⟩
  rcases h with hIdentity | hCurve
  · left
    rcases hIdentity with ⟨hx, hy⟩
    change x = 0 at hx
    change y = 0 at hy
    simp [Point.neg, Point.isIdentityEncoding, hx, hy]
  · right
    unfold Point.onCurve pallasB at hCurve
    change Point.onCurve ({ x := x, y := -y } : Point Fp)
    unfold Point.onCurve pallasB
    ring_nf at hCurve ⊢
    linear_combination hCurve

theorem not_onCurve_of_x_eq_zero (y : Fp) :
    ¬ Point.onCurve ({ x := 0, y } : Point Fp) := by
  intro h
  apply CompElliptic.Curves.Pasta.Pallas.no_onCurve_x_zero y
  unfold CompElliptic.CurveForms.ShortWeierstrass.OnCurve
    CompElliptic.Curves.Pasta.Pallas.a CompElliptic.Curves.Pasta.Pallas.b
  unfold Point.onCurve pallasB at h
  rw [pow_two]
  linear_combination h

theorem not_isIdentityEncoding_of_onCurve {point : Point Fp}
    (hPoint : Point.onCurve point) :
    ¬ Point.isIdentityEncoding point := by
  rcases point with ⟨x, y⟩
  intro hIdentity
  change x = 0 ∧ y = 0 at hIdentity
  rw [hIdentity.1] at hPoint
  exact not_onCurve_of_x_eq_zero y hPoint

theorem y_eq_zero_of_isPointOrIdentity_of_x_eq_zero {point : Point Fp}
    (hPoint : Point.isPointOrIdentity point) :
    point.x = 0 → point.y = 0 := by
  rcases point with ⟨x, y⟩
  intro hx
  rcases hPoint with hIdentity | hCurve
  · exact hIdentity.2
  · by_contra hy
    exact not_onCurve_of_x_eq_zero y (by
      change x = 0 at hx
      rw [hx] at hCurve
      exact hCurve)

theorem y_ne_zero_of_isPointOrIdentity_of_x_ne_zero {point : Point Fp}
    (hPoint : Point.isPointOrIdentity point) (hx : point.x ≠ 0) :
    point.y ≠ 0 := by
  intro hy
  rcases point with ⟨x, y⟩
  change x ≠ 0 at hx
  change y = 0 at hy
  rcases hPoint with hIdentity | hCurve
  · exact hx hIdentity.1
  · subst hy
    apply CompElliptic.Curves.Pasta.Pallas.no_onCurve_y_zero x
    unfold CompElliptic.CurveForms.ShortWeierstrass.OnCurve
      CompElliptic.Curves.Pasta.Pallas.a CompElliptic.Curves.Pasta.Pallas.b
    unfold Point.onCurve pallasB at hCurve
    rw [pow_two]
    linear_combination hCurve

end Point

end Ecc
end Orchard
