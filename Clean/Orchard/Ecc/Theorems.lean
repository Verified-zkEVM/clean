import Clean.Orchard.Ecc.Defs
import Mathlib.Tactic

namespace Orchard
namespace Ecc

namespace Point

theorem shortWeierstrass_onCurve_iff {point : Point Fp} :
    CompElliptic.CurveForms.ShortWeierstrass.OnCurve (0 : Fp) (5 : Fp) point.coords ↔ point.onCurve := by
  rcases point with ⟨x, y⟩
  unfold CompElliptic.CurveForms.ShortWeierstrass.OnCurve Point.coords Point.onCurve pallasB
  constructor <;> intro h <;> ring_nf at h ⊢ <;> linear_combination h

theorem shortWeierstrass_onCurve_of_onCurve {point : Point Fp}
    (hPoint : point.onCurve) :
    CompElliptic.CurveForms.ShortWeierstrass.OnCurve (0 : Fp) (5 : Fp) point.coords :=
  shortWeierstrass_onCurve_iff.mpr hPoint

theorem onCurve_of_shortWeierstrass_onCurve {point : Point Fp}
    (hPoint : CompElliptic.CurveForms.ShortWeierstrass.OnCurve (0 : Fp) (5 : Fp) point.coords) :
    point.onCurve :=
  shortWeierstrass_onCurve_iff.mp hPoint

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

theorem shortWeierstrass_add_onCurve_of_onCurve_of_x_ne {p q : Point Fp}
    (hp : p.onCurve) (hq : q.onCurve) (hx : p.x ≠ q.x) :
    CompElliptic.CurveForms.ShortWeierstrass.OnCurve (0 : Fp) (5 : Fp)
      (CompElliptic.CurveForms.ShortWeierstrass.add (0 : Fp) p.coords q.coords) := by
  rcases p with ⟨px, py⟩
  rcases q with ⟨qx, qy⟩
  have hpOn : CompElliptic.CurveForms.ShortWeierstrass.OnCurve (0 : Fp) (5 : Fp) (px, py) :=
    shortWeierstrass_onCurve_of_onCurve hp
  have hqOn : CompElliptic.CurveForms.ShortWeierstrass.OnCurve (0 : Fp) (5 : Fp) (qx, qy) :=
    shortWeierstrass_onCurve_of_onCurve hq
  have hp0 : (px, py) ≠ ((0 : Fp), 0) := by
    intro h
    have hx0 : px = 0 := (Prod.ext_iff.mp h).1
    exact not_onCurve_of_x_eq_zero py (by
      rw [hx0] at hp
      exact hp)
  have hq0 : (qx, qy) ≠ ((0 : Fp), 0) := by
    intro h
    have hx0 : qx = 0 := (Prod.ext_iff.mp h).1
    exact not_onCurve_of_x_eq_zero qy (by
      rw [hx0] at hq
      exact hq)
  have hxy : ¬(px = qx ∧ py + qy = 0) := by
    intro h
    exact hx h.1
  simp only [Point.coords]
  rw [CompElliptic.CurveForms.ShortWeierstrass.add_eq_addXY hp0 hq0 hxy]
  have hxy' :
      ¬(px = qx ∧ py =
        WeierstrassCurve.Affine.negY
          (CompElliptic.CurveForms.ShortWeierstrass.toW (0 : Fp) (5 : Fp)) qx qy) := by
    rintro ⟨hxeq, _⟩
    exact hx hxeq
  letI : (CompElliptic.CurveForms.ShortWeierstrass.toW (0 : Fp) (5 : Fp)).IsElliptic := by
    change (CompElliptic.CurveForms.ShortWeierstrass.toW
      CompElliptic.Curves.Pasta.Pallas.curve.A
      CompElliptic.Curves.Pasta.Pallas.curve.B).IsElliptic
    infer_instance
  have hns := WeierstrassCurve.Affine.nonsingular_add
    (CompElliptic.CurveForms.ShortWeierstrass.nonsingular_toW hpOn)
    (CompElliptic.CurveForms.ShortWeierstrass.nonsingular_toW hqOn)
    hxy'
  exact CompElliptic.CurveForms.ShortWeierstrass.equation_toW.mp hns.left

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
