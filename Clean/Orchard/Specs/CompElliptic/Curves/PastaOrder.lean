import Clean.Orchard.Specs.CompElliptic.Curves.Pasta
import Clean.Orchard.Specs.CompElliptic.CurveForms.ShortWeierstrassOrder

/-!
# Group orders of the Pasta curves

Proofs that `Nat.card (SWPoint Pallas.curve) = q` and `Nat.card (SWPoint Vesta.curve) = p`
(where `p`/`q` are the Pallas base/scalar primes), via the generic order-pinning machinery
of `CurveForms.ShortWeierstrassOrder`:

* the point `G = (-1, 2)` lies on both curves, and `native_decide` on the compiled
  double-and-add `fastNsmul` certifies `q • G = 0` on Pallas and `p • G = 0` on Vesta;
* the trivial count bound `Nat.card ≤ 2 * |F| + 1` then pins the order to the prime
  (no Hasse bound needed): for Pallas `2p + 1 < 2q` suffices directly, while for Vesta
  `2q + 1 < 3p` combines with the absence of 2-torsion (no curve point has `y = 0`,
  since `-5` is not a cube in the Vesta base field).
-/

namespace CompElliptic.CurveForms.ShortWeierstrass

variable {F : Type*} [Field F] [DecidableEq F]

/-- Point equality is decidable coordinate-wise (`onCurve` is a `Prop`), so scalar-multiple
certificates like `fastNsmul n G = 0` can be discharged by `native_decide`. -/
instance {E : SWCurve F} : DecidableEq (SWPoint E) := fun P Q =>
  decidable_of_iff ((P.x, P.y) = (Q.x, Q.y)) ⟨SWPoint.ext_pair, fun h => h ▸ rfl⟩

end CompElliptic.CurveForms.ShortWeierstrass

namespace CompElliptic.Curves.Pasta

open CompElliptic.CurveForms.ShortWeierstrass CompElliptic.Fields.Pasta

namespace Pallas

/-- The test point `G = (-1, 2)` as a bundled point on the Pallas curve
(`2² = 4 = (-1)³ + 5`). -/
def Gpt : SWPoint curve := ⟨-1, 2, Or.inl (by native_decide)⟩

theorem Gpt_ne_zero : Gpt ≠ 0 := by
  intro h
  have hx : (-1 : PallasBaseField) = 0 := congrArg SWPoint.x h
  exact (by decide : (-1 : PallasBaseField) ≠ 0) hx

/-- Order certificate: the Pallas scalar prime `q` kills `G`, evaluated via the compiled
double-and-add `fastNsmul` (the group's own `n • _` is unary and cannot be evaluated). -/
theorem scalar_nsmul_Gpt : PALLAS_SCALAR_CARD • Gpt = 0 := by
  rw [← fastNsmul_eq]
  native_decide

/-- The Pallas curve group has exactly `q = PALLAS_SCALAR_CARD` points: `q` is prime and
kills the nonzero point `G`, and the crude count bound gives `Nat.card ≤ 2p + 1 < 2q`. -/
theorem natCard : Nat.card (SWPoint curve) = PALLAS_SCALAR_CARD := by
  apply natCard_eq_of_prime_nsmul PALLAS_SCALAR_is_prime Gpt_ne_zero scalar_nsmul_Gpt
  rw [ZMod.card]
  decide

end Pallas

namespace Vesta

/-- `-5` is not a cube in the Vesta base field, so `y = 0` is impossible for a curve point. -/
theorem neg_five_not_isCube : ¬ ∃ x : VestaBaseField, x ^ 3 = -(5 : VestaBaseField) := by
  rintro ⟨x, hx⟩
  have hx0 : x ≠ 0 := by
    intro hzero
    have hneg : (-(5 : VestaBaseField)) = 0 := by
      rw [← hx, hzero]
      norm_num
    exact (by decide : (-(5 : VestaBaseField)) ≠ 0) hneg
  have hfermat : x ^ (PALLAS_SCALAR_CARD - 1) = 1 := by
    simpa [ZMod.card] using FiniteField.pow_card_sub_one_eq_one x hx0
  have hpow : (-(5 : VestaBaseField)) ^ ((PALLAS_SCALAR_CARD - 1) / 3) = 1 := by
    rw [← hx, ← pow_mul]
    have hm : 3 * ((PALLAS_SCALAR_CARD - 1) / 3) = PALLAS_SCALAR_CARD - 1 := by
      native_decide
    rw [hm]
    exact hfermat
  have hnon : (-(5 : VestaBaseField)) ^ ((PALLAS_SCALAR_CARD - 1) / 3) ≠ 1 := by
    native_decide
  exact hnon hpow

/-- No point on the Vesta curve has `y`-coordinate `0`. -/
theorem no_onCurve_y_zero (x : VestaBaseField) : ¬ OnCurve a b (x, 0) := by
  intro h
  have hsum : x ^ 3 + 5 = 0 := by
    simpa [OnCurve, a, b] using h.symm
  have h' : x ^ 3 = -(5 : VestaBaseField) := by
    linear_combination hsum
  exact neg_five_not_isCube ⟨x, h'⟩

/-- The test point `G = (-1, 2)` as a bundled point on the Vesta curve
(`2² = 4 = (-1)³ + 5`). -/
def Gpt : SWPoint curve := ⟨-1, 2, Or.inl (by native_decide)⟩

theorem Gpt_ne_zero : Gpt ≠ 0 := by
  intro h
  have hx : (-1 : VestaBaseField) = 0 := congrArg SWPoint.x h
  exact (by decide : (-1 : VestaBaseField) ≠ 0) hx

/-- Order certificate: the Vesta scalar prime `p` (= Pallas base prime) kills `G`, evaluated
via the compiled double-and-add `fastNsmul`. -/
theorem scalar_nsmul_Gpt : PALLAS_BASE_CARD • Gpt = 0 := by
  rw [← fastNsmul_eq]
  native_decide

/-- The Vesta curve group has exactly `p = PALLAS_BASE_CARD` points: `p` is prime and kills
the nonzero point `G`, the crude count bound gives `Nat.card ≤ 2q + 1 < 3p` (here `p` is
*below* the field size `q`, so the factor-2 bound alone does not suffice), and the group has
no 2-torsion because no curve point has `y = 0`. -/
theorem natCard : Nat.card (SWPoint curve) = PALLAS_BASE_CARD := by
  apply natCard_eq_of_prime_nsmul_odd PALLAS_BASE_is_prime Gpt_ne_zero scalar_nsmul_Gpt
  · rw [ZMod.card]
    decide
  · exact two_nsmul_eq_zero (by decide) no_onCurve_y_zero

end Vesta

end CompElliptic.Curves.Pasta
