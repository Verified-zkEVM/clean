/-
Copyright (c) 2026 CompElliptic Contributors. All rights reserved.
Released under the Apache License, Version 2.0, or the MIT license, at your option,
as described in the files LICENSE-APACHE and LICENSE-MIT.
Authors: Daira-Emma Hopwood
-/
import Clean.Orchard.Specs.CompElliptic.CurveForms.ShortWeierstrass
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
# Curve order machinery for short-Weierstrass curves

Generic tools to pin down `Nat.card (SWPoint E)` for a concrete curve `E` over a finite field:

1. **Finiteness and a crude cardinality bound** — `SWPoint E` embeds into `F × F`, and each
   `x`-coordinate carries at most two curve points (the roots of `y² = x³ + A x + B`), so
   `Nat.card (SWPoint E) ≤ 2 * Fintype.card F + 1` (`natCard_le`). This is a weak stand-in for
   Hasse's bound, but it is enough to pin the group order given a prime `q` with `q • G = 0`.

2. **Fast scalar multiplication** — the group `n • P` is unary (`nsmulRec`), hopeless for
   `native_decide` at cryptographic sizes. `fastNsmul` is the double-and-add form, proven equal to
   `n • P` (`fastNsmul_eq`), so concrete call sites can evaluate `q • G = 0` via `native_decide`.

3. **Order pinning** — if a prime `q` kills a nonzero point and `2 * Fintype.card F + 1 < 2 * q`,
   then `Nat.card (SWPoint E) = q` (`natCard_eq_of_prime_nsmul`). When the prime is *smaller* than
   the field (as for a curve of order `p` over a field of order `q > p`), the weaker bound
   `2 * Fintype.card F + 1 < 3 * p` suffices provided the group has no 2-torsion
   (`natCard_eq_of_prime_nsmul_odd`); `two_nsmul_eq_zero` discharges the no-2-torsion side
   condition from the absence of points with `y = 0`.
-/

namespace CompElliptic.CurveForms.ShortWeierstrass

variable {F : Type*} [Field F] [DecidableEq F]

instance (a b : F) (p : F × F) : Decidable (Valid a b p) := by
  unfold Valid; infer_instance

/-! ## Finiteness and the cardinality bound -/

/-- Representable points on `E` are exactly the valid coordinate pairs. -/
def SWPoint.equivSubtype (E : SWCurve F) : SWPoint E ≃ { pr : F × F // Valid E.A E.B pr } where
  toFun P := ⟨(P.x, P.y), P.onCurve⟩
  invFun pr := ⟨pr.1.1, pr.1.2, pr.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance {E : SWCurve F} [Finite F] : Finite (SWPoint E) :=
  Finite.of_injective (fun P => (P.x, P.y)) fun _ _ h => SWPoint.ext_pair h

instance {E : SWCurve F} : Nonempty (SWPoint E) := ⟨0⟩

/-- Each `x`-coordinate carries at most two on-curve points: the fiber injects into the square
roots of `x³ + A x + B`. -/
theorem card_filter_onCurve_fst_le [Fintype F] (E : SWCurve F) (x : F) :
    ((Finset.univ.filter fun pr : F × F => OnCurve E.A E.B pr).filter
      fun pr => pr.1 = x).card ≤ 2 := by
  have hmap : ∀ pr ∈ (Finset.univ.filter fun pr : F × F => OnCurve E.A E.B pr).filter
      (fun pr => pr.1 = x),
      pr.2 ∈ (Polynomial.nthRoots 2 (x ^ 3 + E.A * x + E.B)).toFinset := by
    intro pr hpr
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hpr
    obtain ⟨hOn, hx⟩ := hpr
    rw [Multiset.mem_toFinset, Polynomial.mem_nthRoots two_pos]
    rw [OnCurve, hx] at hOn
    exact hOn
  have hinj : Set.InjOn (fun pr : F × F => pr.2)
      ((Finset.univ.filter fun pr : F × F => OnCurve E.A E.B pr).filter fun pr => pr.1 = x) := by
    intro p hp q hq hpq
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_filter, Finset.mem_univ,
      true_and] at hp hq
    exact Prod.ext (hp.2.trans hq.2.symm) hpq
  calc ((Finset.univ.filter fun pr : F × F => OnCurve E.A E.B pr).filter
        fun pr => pr.1 = x).card
      ≤ (Polynomial.nthRoots 2 (x ^ 3 + E.A * x + E.B)).toFinset.card :=
        Finset.card_le_card_of_injOn _ hmap hinj
    _ ≤ Multiset.card (Polynomial.nthRoots 2 (x ^ 3 + E.A * x + E.B)) :=
        Multiset.toFinset_card_le _
    _ ≤ 2 := Polynomial.card_nthRoots 2 _

/-- Crude cardinality bound: at most two points per `x`-coordinate, plus the identity `𝒪`. -/
theorem natCard_le [Fintype F] {E : SWCurve F} :
    Nat.card (SWPoint E) ≤ 2 * Fintype.card F + 1 := by
  rw [Nat.card_congr (SWPoint.equivSubtype E), Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hsub : (Finset.univ.filter fun pr : F × F => Valid E.A E.B pr) ⊆
      (Finset.univ.filter fun pr : F × F => OnCurve E.A E.B pr) ∪ {((0 : F), (0 : F))} := by
    intro pr hpr
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
      Finset.mem_singleton] at hpr ⊢
    exact hpr
  calc (Finset.univ.filter fun pr : F × F => Valid E.A E.B pr).card
      ≤ ((Finset.univ.filter fun pr : F × F => OnCurve E.A E.B pr) ∪
          {((0 : F), (0 : F))}).card :=
        Finset.card_le_card hsub
    _ ≤ (Finset.univ.filter fun pr : F × F => OnCurve E.A E.B pr).card + 1 :=
        le_trans (Finset.card_union_le _ _) (by simp)
    _ ≤ 2 * Fintype.card F + 1 := by
        have h := Finset.card_le_mul_card_image_of_maps_to
          (f := Prod.fst) (t := (Finset.univ : Finset F))
          (fun _ _ => Finset.mem_univ _) 2 (fun x _ => card_filter_onCurve_fst_le E x)
        rw [Finset.card_univ] at h
        omega

/-! ## Fast scalar multiplication

The `AddCommGroup (SWPoint E)` instance uses `nsmulRec`, so `n • P` is a unary tower of additions
and cannot be evaluated for cryptographic `n`. `fastNsmul` is the standard double-and-add form;
`fastNsmul_eq` lets concrete call sites decide `n • G = 0` by `native_decide` on `fastNsmul`. -/

/-- Double-and-add scalar multiplication, evaluable for cryptographic-size `n`. -/
def fastNsmul {E : SWCurve F} (n : ℕ) (P : SWPoint E) : SWPoint E :=
  if _h : n = 0 then 0
  else
    let half := fastNsmul (n / 2) P
    if n % 2 = 0 then half + half else half + half + P
  termination_by n
  decreasing_by omega

/-- `fastNsmul` computes the group-theoretic `n • P`. -/
theorem fastNsmul_eq {E : SWCurve F} (n : ℕ) (P : SWPoint E) : fastNsmul n P = n • P := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [fastNsmul]
    by_cases h : n = 0
    · rw [dif_pos h, h, zero_nsmul]
    · rw [dif_neg h, ih (n / 2) (Nat.div_lt_self (Nat.pos_of_ne_zero h) one_lt_two)]
      rcases Nat.mod_two_eq_zero_or_one n with hm | hm
      · rw [if_pos hm, ← two_nsmul, ← mul_nsmul']
        congr 1
        omega
      · rw [if_neg (by omega), ← two_nsmul, ← mul_nsmul', ← succ_nsmul]
        congr 1
        omega

/-! ## Order pinning -/

/-- If a prime `q` kills a nonzero point and `q` exceeds half the crude cardinality bound, the
group order is exactly `q`: the order divides `Nat.card`, and `Nat.card < 2 * q` leaves `q` as the
only multiple in range. -/
theorem natCard_eq_of_prime_nsmul [Fintype F] {E : SWCurve F} {q : ℕ} (hq : Nat.Prime q)
    {G : SWPoint E} (hG : G ≠ 0) (hsmul : q • G = 0)
    (hbound : 2 * Fintype.card F + 1 < 2 * q) : Nat.card (SWPoint E) = q := by
  haveI := Fact.mk hq
  have horder : addOrderOf G = q := addOrderOf_eq_prime hsmul hG
  have hdvd : q ∣ Nat.card (SWPoint E) := horder ▸ addOrderOf_dvd_natCard G
  have hpos : 0 < Nat.card (SWPoint E) := Nat.card_pos
  exact Nat.eq_of_dvd_of_lt_two_mul hpos.ne' hdvd (lt_of_le_of_lt natCard_le hbound)

/-- Variant of `natCard_eq_of_prime_nsmul` for a prime `p` *below* the field size (so only
`Nat.card < 3 * p` is available): the multiple `2 * p` is excluded by the absence of 2-torsion,
via Cauchy's theorem. -/
theorem natCard_eq_of_prime_nsmul_odd [Fintype F] {E : SWCurve F} {p : ℕ} (hp : Nat.Prime p)
    {G : SWPoint E} (hG : G ≠ 0) (hsmul : p • G = 0)
    (hbound : 2 * Fintype.card F + 1 < 3 * p)
    (h2 : ∀ Q : SWPoint E, 2 • Q = 0 → Q = 0) : Nat.card (SWPoint E) = p := by
  haveI := Fact.mk hp
  have horder : addOrderOf G = p := addOrderOf_eq_prime hsmul hG
  have hdvd : p ∣ Nat.card (SWPoint E) := horder ▸ addOrderOf_dvd_natCard G
  have hpos : 0 < Nat.card (SWPoint E) := Nat.card_pos
  have hle : Nat.card (SWPoint E) ≤ 2 * Fintype.card F + 1 := natCard_le
  obtain ⟨k, hk⟩ := hdvd
  have hklt : k < 3 := by
    have h3 : p * k < p * 3 := by
      calc p * k = Nat.card (SWPoint E) := hk.symm
        _ ≤ 2 * Fintype.card F + 1 := hle
        _ < 3 * p := hbound
        _ = p * 3 := Nat.mul_comm 3 p
    exact Nat.lt_of_mul_lt_mul_left h3
  have hk2 : k ≠ 2 := by
    rintro rfl
    have h2dvd : 2 ∣ Nat.card (SWPoint E) := ⟨p, by omega⟩
    haveI : Fintype (SWPoint E) := Fintype.ofFinite _
    rw [Nat.card_eq_fintype_card] at h2dvd
    obtain ⟨Q, hQ⟩ := exists_prime_addOrderOf_dvd_card 2 h2dvd
    have hQ2 : 2 • Q = 0 := hQ ▸ addOrderOf_nsmul_eq_zero Q
    have hQ0 : Q ≠ 0 := by
      intro h
      rw [h, addOrderOf_zero] at hQ
      omega
    exact hQ0 (h2 Q hQ2)
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [Nat.mul_zero] at hk
    omega
  have hk1 : k = 1 := by omega
  rw [hk, hk1, Nat.mul_one]

/-- No 2-torsion when the field has odd characteristic and no curve point has `y = 0`
(a doubled point `Q = -Q` forces `2 * Q.y = 0`). Discharges the `h2` side condition of
`natCard_eq_of_prime_nsmul_odd` at concrete call sites. -/
theorem two_nsmul_eq_zero {E : SWCurve F} (h2 : (2 : F) ≠ 0)
    (hy : ∀ x : F, ¬OnCurve E.A E.B (x, 0)) (Q : SWPoint E) (hQ : 2 • Q = 0) : Q = 0 := by
  rw [two_nsmul] at hQ
  have hneg : Q = -Q := eq_neg_of_add_eq_zero_left hQ
  have hyy : Q.y = -Q.y := by rw [← SWPoint.neg_y Q, ← hneg]
  have hQy : Q.y = 0 := by
    have h2y : 2 * Q.y = 0 := by linear_combination hyy
    exact (mul_eq_zero.mp h2y).resolve_left h2
  rcases Q.onCurve with hc | h0
  · rw [hQy] at hc
    exact absurd hc (hy Q.x)
  · exact SWPoint.ext_pair h0

end CompElliptic.CurveForms.ShortWeierstrass
