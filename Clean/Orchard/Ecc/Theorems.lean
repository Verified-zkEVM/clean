import Clean.Orchard.Ecc.Defs
import Mathlib.Tactic

open CompElliptic.Curves.Pasta CompElliptic.CurveForms

namespace Orchard.Ecc

lemma sw_add_coords (P Q : ShortWeierstrass.SWPoint Pallas.curve) :
  ShortWeierstrass.add pallasA (P.x, P.y) (Q.x, Q.y) = ((P + Q).x, (P + Q).y) := rfl

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
    Nat.card (ShortWeierstrass.SWPoint Pallas.curve) = PALLAS_SCALAR_CARD

/-- Every non-identity Pallas point generates the full prime-order group. -/
theorem pallas_addOrderOf {P : ShortWeierstrass.SWPoint Pallas.curve} (h : P ≠ 0) :
    addOrderOf P = PALLAS_SCALAR_CARD := by
  have hdvd := addOrderOf_dvd_natCard P
  rw [pallas_natCard] at hdvd
  rcases CompElliptic.Fields.Pasta.PALLAS_SCALAR_is_prime.eq_one_or_self_of_dvd
      _ hdvd with h1 | hq
  · exact absurd (AddMonoid.addOrderOf_eq_one_iff.mp h1) h
  · exact hq

theorem pallas_nsmul_eq_zero_iff {P : ShortWeierstrass.SWPoint Pallas.curve} (hP : P ≠ 0)
    (n : ℕ) : n • P = 0 ↔ PALLAS_SCALAR_CARD ∣ n := by
  rw [← pallas_addOrderOf hP, addOrderOf_dvd_iff_nsmul_eq_zero]

theorem pallas_nsmul_ne_zero {P : ShortWeierstrass.SWPoint Pallas.curve} (hP : P ≠ 0)
    {n : ℕ} (hn : 0 < n) (hlt : n < PALLAS_SCALAR_CARD) : n • P ≠ 0 := by
  rw [Ne, pallas_nsmul_eq_zero_iff hP]
  intro hdvd
  have := Nat.le_of_dvd hn hdvd
  omega

theorem pallas_nsmul_onCurve {P : ShortWeierstrass.SWPoint Pallas.curve} (hP : P ≠ 0)
    {n : ℕ} (hn : 0 < n) (hlt : n < PALLAS_SCALAR_CARD) :
    Pallas.OnCurve ((n • P).x, (n • P).y) :=
  ShortWeierstrass.SWPoint.onCurve_of_ne_zero (pallas_nsmul_ne_zero hP hn hlt)

/--
The collision-freedom fact behind incomplete additions on a variable base: distinct
small positive multiples of a non-identity point have distinct `x`-coordinates, since
equal `x` would force equal-or-opposite points and hence a relation `t ∓ s ≡ 0` modulo
the (large) group order.
-/
theorem pallas_nsmul_x_ne {P : ShortWeierstrass.SWPoint Pallas.curve} (hP : P ≠ 0)
    {s t : ℕ} (hs : 0 < s) (hst : s < t) (hsum : s + t < PALLAS_SCALAR_CARD) :
    (t • P).x ≠ (s • P).x := by
  have hs_ne : s • P ≠ 0 := pallas_nsmul_ne_zero hP hs (by omega)
  have ht_ne : t • P ≠ 0 := pallas_nsmul_ne_zero hP (by omega) (by omega)
  intro hx
  rcases ShortWeierstrass.SWPoint.eq_or_eq_neg_of_x_eq ht_ne hs_ne hx with heq | hneg
  · rw [nsmul_eq_nsmul_iff_modEq, pallas_addOrderOf hP, Nat.ModEq,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at heq
    omega
  · have hzero : (t + s) • P = 0 := by
      rw [add_nsmul, hneg, neg_add_cancel]
    rw [pallas_nsmul_eq_zero_iff hP] at hzero
    have := Nat.le_of_dvd (by omega) hzero
    omega

end Orchard.Ecc
