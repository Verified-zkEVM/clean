/-
Copyright (c) 2026 CompElliptic Contributors. All rights reserved.
Released under the Apache License, Version 2.0, or the MIT license, at your option,
as described in the files LICENSE-APACHE and LICENSE-MIT.
Authors: Daira-Emma Hopwood
-/
import Clean.Orchard.Specs.CompElliptic.CurveForms.ShortWeierstrass
import Clean.Orchard.Specs.CompElliptic.Fields.Pasta
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.LegendreSymbol.Basic

/-!
# The Pasta curves as short-Weierstrass elliptic curves

Concrete `SWCurve` instances for Pallas and Vesta (both `y² = x³ + 5`, over the Pallas and Vesta
base fields respectively). Plus the curve-specific facts the `(0, 0) ≡ 𝒪` representation relies on
(`five_not_isSquare` ⟹ `no_onCurve_x_zero`, spec §5.4.9.7) and `native_decide` sanity checks
exercising the raw computable kernel.

Sanity checks use `native_decide` (compiler-trusted): they exercise the *definitions*
computationally and are independent of the soundness theorems to come.
-/

namespace CompElliptic.Curves.Pasta

open CompElliptic.CurveForms.ShortWeierstrass CompElliptic.Fields.Pasta

namespace Pallas

/-- Pallas: `y² = x³ + 5` over the Pallas base field (`A = 0`, `B = 5`). -/
def a : PallasBaseField := 0
def b : PallasBaseField := 5

/-- A convenient prime-order point `(-1, 2)` for testing (just a test point, not a
protocol-specified base). -/
def G : PallasBaseField × PallasBaseField := (-1, 2)

theorem b_ne_zero : b ≠ 0 := by decide

/-- The Pallas curve as a rich `SWCurve`: ellipticity (`sw_Δ 0 5 = -10800 ≠ 0`, so `IsUnit`) and
`B ≠ 0` discharged by computation. -/
def curve : SWCurve PallasBaseField where
  A := a
  B := b
  IsElliptic := by rw [isUnit_iff_ne_zero]; native_decide
  B_nonzero := b_ne_zero

instance instIsElliptic : (toW a b).IsElliptic := by
  change (toW curve.A curve.B).IsElliptic
  infer_instance

/-- The `(0, 0)` sentinel is off the Pallas curve. -/
theorem not_onCurve_zero : ¬ OnCurve a b (0, 0) :=
  CurveForms.ShortWeierstrass.not_onCurve_zero b_ne_zero

/-- `5` is a quadratic non-residue in the Pallas base field, so `y² = x³ + 5` has no point with
`x = 0` (Zcash protocol spec §5.4.9.7).

Euler's criterion (`ZMod.euler_criterion`) reduces this to `5 ^ (p / 2) ≠ 1`. The LHS (`-1`) is
evaluated by `reduce_mod_char` (fast modular exponentiation via `NormNum.PowMod`), the same
machinery the `PrattPartList.prime` legs use for their `a ^ k ≠ 1` conditions. -/
theorem five_not_isSquare : ¬ IsSquare (5 : PallasBaseField) := by
  rw [ZMod.euler_criterion PALLAS_BASE_CARD (by decide : (5 : PallasBaseField) ≠ 0)]
  reduce_mod_char
  decide

/-- Consequently no point on the Pallas curve has `x`-coordinate `0`, so `x = 0` denotes `𝒪`
unambiguously. -/
theorem no_onCurve_x_zero (y : PallasBaseField) : ¬ OnCurve a b (0, y) := by
  intro h
  have h' : y ^ 2 = 5 := by simpa [OnCurve, a, b] using h
  exact five_not_isSquare ⟨y, by rw [← h', pow_two]⟩

/-- `-5` is not a cube in the Pallas base field, so `y = 0` is impossible for a curve point. -/
theorem neg_five_not_isCube : ¬ ∃ x : PallasBaseField, x ^ 3 = -(5 : PallasBaseField) := by
  rintro ⟨x, hx⟩
  have hx0 : x ≠ 0 := by
    intro hzero
    have hneg : (-(5 : PallasBaseField)) = 0 := by
      rw [← hx, hzero]
      norm_num
    exact (by decide : (-(5 : PallasBaseField)) ≠ 0) hneg
  have hfermat : x ^ (PALLAS_BASE_CARD - 1) = 1 := by
    simpa [ZMod.card] using FiniteField.pow_card_sub_one_eq_one x hx0
  have hpow : (-(5 : PallasBaseField)) ^ ((PALLAS_BASE_CARD - 1) / 3) = 1 := by
    rw [← hx, ← pow_mul]
    have hm : 3 * ((PALLAS_BASE_CARD - 1) / 3) = PALLAS_BASE_CARD - 1 := by
      native_decide
    rw [hm]
    exact hfermat
  have hnon : (-(5 : PallasBaseField)) ^ ((PALLAS_BASE_CARD - 1) / 3) ≠ 1 := by
    native_decide
  exact hnon hpow

/-- No point on the Pallas curve has `y`-coordinate `0`. -/
theorem no_onCurve_y_zero (x : PallasBaseField) : ¬ OnCurve a b (x, 0) := by
  intro h
  have hsum : x ^ 3 + 5 = 0 := by
    simpa [OnCurve, a, b] using h.symm
  have h' : x ^ 3 = -(5 : PallasBaseField) := by
    linear_combination hsum
  exact neg_five_not_isCube ⟨x, h'⟩

-- `(-1, 2)` is on the curve: `2² = 4 = (-1)³ + 5`.
example : OnCurve a b G := by native_decide

-- `G + (-G) = 𝒪` (hits the `q = -p` branch; no inversion).
example : add a G (neg G) = (0, 0) := by native_decide

-- `G + 𝒪 = G`.
example : add a G (0, 0) = G := by native_decide

-- Doubling and tripling stay on the curve (exercises the slope/inverse).
example : OnCurve a b (smul a 2 G) := by native_decide
example : OnCurve a b (smul a 3 G) := by native_decide

-- The `AddCommGroup (SWPoint curve)` instance provides working scalar actions `n • _` (over `ℕ`)
-- and `k • _` (over `ℤ`), interoperating with the generic group lemmas.
example (P : SWPoint curve) : (0 : ℕ) • P = 0 := zero_nsmul P
example (P : SWPoint curve) : (2 : ℕ) • P = P + P := two_nsmul P
example (P : SWPoint curve) : (1 : ℤ) • P = P := one_zsmul P
example (P : SWPoint curve) : (-1 : ℤ) • P = -P := neg_one_zsmul P

/-- Pallas on-curve predicate specialized from short-Weierstrass form. -/
abbrev OnCurve (point : PallasBaseField × PallasBaseField) : Prop :=
  CurveForms.ShortWeierstrass.OnCurve a b point

/-- Pallas valid point predicate specialized from short-Weierstrass form. -/
abbrev Valid (point : PallasBaseField × PallasBaseField) : Prop :=
  CurveForms.ShortWeierstrass.Valid a b point

/-- Pallas complete addition specialized from short-Weierstrass form. -/
abbrev add (p q : PallasBaseField × PallasBaseField) : PallasBaseField × PallasBaseField :=
  CurveForms.ShortWeierstrass.add a p q

/-- Complete addition on coordinates agrees with the `SWPoint` group operation. -/
theorem add_coords (P Q : SWPoint curve) :
    add (P.x, P.y) (Q.x, Q.y) = ((P + Q).x, (P + Q).y) := rfl

end Pallas

namespace Vesta

/-- Vesta: `y² = x³ + 5` over the Vesta base field (`= PallasScalarField`; `A = 0`, `B = 5`). -/
def a : VestaBaseField := 0
def b : VestaBaseField := 5

/-- A convenient prime-order point `(-1, 2)` for testing (just a test point, not a
protocol-specified base). -/
def G : VestaBaseField × VestaBaseField := (-1, 2)

theorem b_ne_zero : b ≠ 0 := by decide

/-- The Vesta curve as a rich `SWCurve`: ellipticity (`sw_Δ 0 5 = -10800 ≠ 0`, so `IsUnit`) and
`B ≠ 0` discharged by computation. -/
def curve : SWCurve VestaBaseField where
  A := a
  B := b
  IsElliptic := by rw [isUnit_iff_ne_zero]; native_decide
  B_nonzero := b_ne_zero

/-- The `(0, 0)` sentinel is off the Vesta curve. -/
theorem not_onCurve_zero : ¬ OnCurve a b (0, 0) :=
  CurveForms.ShortWeierstrass.not_onCurve_zero b_ne_zero

/-- `5` is a quadratic non-residue in the Vesta base field, so `y² = x³ + 5` has no point with
`x = 0` (Zcash protocol spec §5.4.9.7).

As for Pallas: Euler's criterion (`ZMod.euler_criterion`) reduces this to `5 ^ (q / 2) ≠ 1`, and
`reduce_mod_char` (fast modular exponentiation) evaluates the power to `-1`. -/
theorem five_not_isSquare : ¬ IsSquare (5 : VestaBaseField) := by
  rw [ZMod.euler_criterion PALLAS_SCALAR_CARD (by decide : (5 : VestaBaseField) ≠ 0)]
  reduce_mod_char
  decide

/-- Consequently no point on the Vesta curve has `x`-coordinate `0`, so `x = 0` denotes `𝒪`
unambiguously. -/
theorem no_onCurve_x_zero (y : VestaBaseField) : ¬ OnCurve a b (0, y) := by
  intro h
  have h' : y ^ 2 = 5 := by simpa [OnCurve, a, b] using h
  exact five_not_isSquare ⟨y, by rw [← h', pow_two]⟩

-- `(-1, 2)` is on the curve: `2² = 4 = (-1)³ + 5`.
example : OnCurve a b G := by native_decide

-- `G + (-G) = 𝒪` (hits the `q = -p` branch; no inversion).
example : add a G (neg G) = (0, 0) := by native_decide

-- `G + 𝒪 = G`.
example : add a G (0, 0) = G := by native_decide

-- Doubling and tripling stay on the curve (exercises the slope/inverse).
example : OnCurve a b (smul a 2 G) := by native_decide
example : OnCurve a b (smul a 3 G) := by native_decide

end Vesta

end CompElliptic.Curves.Pasta
