import Clean.Orchard.Ecc.Defs
import Mathlib.Tactic

namespace Orchard
namespace Ecc

variable {F : Type} [Field F]

theorem negPoint_isPointOrIdentity {point : Point PallasBaseField}
    (h : isPointOrIdentity point) :
    isPointOrIdentity (negPoint point) := by
  rcases point with ⟨x, y⟩
  rcases h with hIdentity | hCurve
  · left
    rcases hIdentity with ⟨hx, hy⟩
    change x = 0 at hx
    change y = 0 at hy
    simp [negPoint, isIdentityEncoding, hx, hy]
  · right
    unfold onCurve curveEquation pallasB at hCurve
    change onCurve ({ x := x, y := -y } : Point PallasBaseField)
    unfold onCurve curveEquation pallasB
    ring_nf at hCurve ⊢
    linear_combination hCurve

theorem pallasNoCurvePointWithXZero : NoCurvePointWithXZero (F := PallasBaseField) := by
  intro y h
  apply CompElliptic.Curves.Pasta.Pallas.no_onCurve_x_zero y
  unfold CompElliptic.CurveForms.ShortWeierstrass.OnCurve
    CompElliptic.Curves.Pasta.Pallas.a CompElliptic.Curves.Pasta.Pallas.b
  unfold onCurve curveEquation pallasB at h
  rw [pow_two]
  linear_combination h

theorem xZeroImpliesIdentity_of_pointOrIdentity
    (hNoXZero : NoCurvePointWithXZero (F := F)) {point : Point F}
    (hPoint : isPointOrIdentity point) :
    point.x = 0 → point.y = 0 := by
  rcases point with ⟨x, y⟩
  intro hx
  rcases hPoint with hIdentity | hCurve
  · exact hIdentity.2
  · by_contra hy
    exact hNoXZero y (by
      change x = 0 at hx
      rw [hx] at hCurve
      exact hCurve)

theorem pallas_y_ne_zero_of_pointOrIdentity_x_ne_zero {point : Point PallasBaseField}
    (hPoint : isPointOrIdentity point) (hx : point.x ≠ 0) :
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
    unfold onCurve curveEquation pallasB at hCurve
    rw [pow_two]
    linear_combination hCurve

end Ecc
end Orchard
