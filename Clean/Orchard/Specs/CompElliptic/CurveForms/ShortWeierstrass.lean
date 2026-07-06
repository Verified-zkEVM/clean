/-
Copyright (c) 2026 CompElliptic Contributors. All rights reserved.
Released under the Apache License, Version 2.0, or the MIT license, at your option,
as described in the files LICENSE-APACHE and LICENSE-MIT.
Authors: Daira-Emma Hopwood
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms
import Clean.Orchard.Specs.CompElliptic.CoordinateSystem

/-!
# Short-Weierstrass elliptic curves

One module for the short-Weierstrass curve form `y² = x³ + A x + B`, layered:

1. **Raw computable kernel** — `OnCurve`, `neg`, complete `add` (identity `𝒪 ≡ (0, 0)`), `smul`,
   as plain functions on `F × F`. `add` models complete addition: it is total and evaluable
   using `native_decide`, with a decidable case split for `𝒪` / doubling / `P + (-P)`.
2. **Transport foundation** — `toW`, identifying the form with Mathlib's `WeierstrassCurve` so
   that the hard group axioms can be borrowed from Mathlib's proven `AddCommGroup`.
3. **Rich bundled types** — `SWCurve` (bundles ellipticity and `B ≠ 0`) and `SWPoint E`
   (correct-by-construction: on the curve or `𝒪`). This is the correct-by-construction interface
   used to express the group structure and circuit gadgets.

The field assumption is a generic `[Field F]`: `SWCurve.IsElliptic` excludes characteristic 2
(`sw_Δ = 0` there), so binary fields are gracefully excluded, but without precluding any future
separate binary-field curve form. See `TODO.md`.
-/

namespace CompElliptic.CurveForms.ShortWeierstrass

variable {F : Type*} [Field F] [DecidableEq F]

/-! ## Raw computable kernel -/

/-- `p` lies on `y² = x³ + a x + b` as an affine point. -/
def OnCurve (a b : F) (p : F × F) : Prop := p.2 ^ 2 = p.1 ^ 3 + a * p.1 + b

instance (a b : F) (p : F × F) : Decidable (OnCurve a b p) := by unfold OnCurve; infer_instance

/-- A representable point: on the curve, or the `(0, 0)` identity sentinel `𝒪`. -/
def Valid (a b : F) (p : F × F) : Prop := OnCurve a b p ∨ p = (0, 0)

omit [DecidableEq F] in
/-- The `(0, 0)` sentinel is off the curve exactly when `b ≠ 0` (which holds for any elliptic
curve: `a = b = 0` is the singular cusp `y² = x³`). This is what makes `(0, 0) ≡ 𝒪` unambiguous. -/
theorem not_onCurve_zero {a b : F} (hb : b ≠ 0) : ¬ OnCurve a b (0, 0) := by
  intro h
  apply hb
  have h' : (0 : F) ^ 2 = (0 : F) ^ 3 + a * 0 + b := h
  simpa using h'.symm

/-- Negation `(x, y) ↦ (x, -y)`; fixes the `(0, 0)` sentinel. -/
def neg (p : F × F) : F × F := (p.1, -p.2)

/-- Complete affine addition with `(0, 0) ≡ 𝒪`.
Only the curve coefficient `a` appears (in the doubling slope `(3x² + a)/(2y)`);
`b` is not needed. -/
def add (a : F) (p q : F × F) : F × F :=
  if p = (0, 0) then q
  else if q = (0, 0) then p
  else if p.1 = q.1 then
    if p.2 + q.2 = 0 then (0, 0)                 -- q = -p ⇒ 𝒪
    else                                         -- doubling (same x, so same nonzero y)
      let lam := (3 * p.1 ^ 2 + a) / (2 * p.2)
      let x₃ := lam ^ 2 - p.1 - q.1
      (x₃, lam * (p.1 - x₃) - p.2)
  else                                           -- distinct x-coordinates
    let lam := (q.2 - p.2) / (q.1 - p.1)
    let x₃ := lam ^ 2 - p.1 - q.1
    (x₃, lam * (p.1 - x₃) - p.2)

/-- `n • p`, by iterated addition (spec-level, not the windowed circuit form). On `SWPoint E` the
`AddCommGroup` instance below provides the genuine `n • _` / `k • _` scalar actions. -/
def smul (a : F) : ℕ → F × F → F × F
  | 0, _ => (0, 0)
  | n + 1, p => add a (smul a n p) p

/-! ## Identity, involution, and inverse laws (raw, no hypotheses) -/

/-- `𝒪 + p = p`. -/
theorem zero_add (a : F) (p : F × F) : add a (0, 0) p = p := by
  simp [add]

/-- `p + 𝒪 = p`. -/
theorem add_zero (a : F) (p : F × F) : add a p (0, 0) = p := by
  rcases eq_or_ne p (0, 0) with h | h <;> simp [add, h]

omit [DecidableEq F] in
/-- `-(-p) = p`. -/
theorem neg_neg (p : F × F) : neg (neg p) = p := by
  simp [neg]

/-- `p + (-p) = 𝒪`: for `p = 𝒪` immediate; otherwise the addends share an `x`-coordinate with
`p.2 + (neg p).2 = 0`, so the `q = -p` branch fires. Proved by an explicit `if`-branch walk
rather than `split_ifs <;> simp_all`, which blows the recursion limit on the nested `ite`. -/
theorem add_neg (a : F) (p : F × F) : add a p (neg p) = (0, 0) := by
  rcases eq_or_ne p (0, 0) with h | h
  · simp [add, neg, h]
  · have hn : neg p ≠ (0, 0) := fun hc => h (by simpa [neg, Prod.ext_iff] using hc)
    have hx : p.1 = (neg p).1 := rfl
    have hy : p.2 + (neg p).2 = 0 := by simp [neg]
    unfold add
    rw [if_neg h, if_neg hn, if_pos hx, if_pos hy]

/-! ## Transport foundation: identify the short form with a Mathlib `WeierstrassCurve`

For the short form (`a₁ = a₂ = a₃ = 0`, `a₄ = a`, `a₆ = b`) Mathlib's computable coordinate
formulas (`negY`, `slope`, `addX`, `addY`) reduce to exactly our `add`/`neg`, so closure and
associativity can be borrowed from Mathlib's proven `AddCommGroup` on `WeierstrassCurve.Affine.Point`
(`Affine/Point.lean`). The carried `Nonsingular` proof is a `Prop`, so the bridge is
computation-erasable. The curve must be nonsingular (`[(toW a b).IsElliptic]`). -/

/-- The short-Weierstrass curve `y² = x³ + a x + b` as a Mathlib `WeierstrassCurve`. -/
def toW (a b : F) : WeierstrassCurve F := { a₁ := 0, a₂ := 0, a₃ := 0, a₄ := a, a₆ := b }

omit [DecidableEq F]
@[simp] lemma toW_a₁ (a b : F) : (toW a b).a₁ = 0 := rfl
@[simp] lemma toW_a₂ (a b : F) : (toW a b).a₂ = 0 := rfl
@[simp] lemma toW_a₃ (a b : F) : (toW a b).a₃ = 0 := rfl
@[simp] lemma toW_a₄ (a b : F) : (toW a b).a₄ = a := rfl
@[simp] lemma toW_a₆ (a b : F) : (toW a b).a₆ = b := rfl

/-- Our on-curve predicate is Mathlib's affine curve equation for `toW a b`. -/
lemma equation_toW {a b x y : F} :
    WeierstrassCurve.Affine.Equation (toW a b) x y ↔ OnCurve a b (x, y) := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp only [toW_a₁, toW_a₂, toW_a₃, toW_a₄, toW_a₆, OnCurve]
  constructor <;> intro h <;> linear_combination h

/-- On a nonsingular curve, every on-curve point gives a nonsingular Mathlib point. -/
lemma nonsingular_toW {a b : F} [(toW a b).IsElliptic] {x y : F}
    (h : OnCurve a b (x, y)) : WeierstrassCurve.Affine.Nonsingular (toW a b) x y :=
  WeierstrassCurve.Affine.equation_iff_nonsingular.mp (equation_toW.mpr h)

end CompElliptic.CurveForms.ShortWeierstrass

namespace CompElliptic.CurveForms.ShortWeierstrass
variable {F : Type*} [Field F] [DecidableEq F]

/-! ## Closure, commutativity, associativity (raw workhorses)

Stated with the hypotheses the transport needs: `[(toW a b).IsElliptic]` throughout, and `b ≠ 0`
for the laws whose `𝒪`-sentinel cases require `(0, 0)` to be off the curve. The `SWPoint`
`AddCommGroup` instance below discharges these from `SWCurve`'s bundled fields. -/

open WeierstrassCurve.Affine

/-- For two on-curve points that are neither `𝒪` nor mutual inverses, our affine `add` agrees with
Mathlib's chord/tangent coordinates `(addX, addY)` for `toW a b`. This is the shared engine behind
closure (and, via the `Point` group, associativity). -/
lemma add_eq_addXY {a b : F} {x₁ y₁ x₂ y₂ : F}
    (hp0 : (x₁, y₁) ≠ (0, 0)) (hq0 : (x₂, y₂) ≠ (0, 0))
    (hxy : ¬(x₁ = x₂ ∧ y₁ + y₂ = 0)) :
    add a (x₁, y₁) (x₂, y₂)
      = (addX (toW a b) x₁ x₂ (slope (toW a b) x₁ x₂ y₁ y₂),
         addY (toW a b) x₁ x₂ y₁ (slope (toW a b) x₁ x₂ y₁ y₂)) := by
  have hnegY1 : negY (toW a b) x₁ y₁ = -y₁ := by simp [negY]
  have hnegY2 : negY (toW a b) x₂ y₂ = -y₂ := by simp [negY]
  unfold add
  dsimp only
  rw [if_neg hp0, if_neg hq0]
  by_cases hx : x₁ = x₂
  · have hy : ¬(y₁ + y₂ = 0) := fun h => hxy ⟨hx, h⟩
    have hyne : y₁ ≠ negY (toW a b) x₂ y₂ := by
      rw [hnegY2]; intro h; exact hy (by rw [h]; ring)
    rw [if_pos hx, if_neg hy]
    rw [slope_of_Y_ne hx hyne, hnegY1]
    simp only [addX, addY, negAddY, negY, toW_a₁, toW_a₂, toW_a₃, toW_a₄, mul_zero, zero_mul, sub_zero]
    rw [Prod.mk.injEq]
    refine ⟨by ring, by ring⟩
  · have hd1 : x₂ - x₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
    have hd2 : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx
    rw [if_neg hx]
    rw [slope_of_X_ne hx]
    simp only [addX, addY, negAddY, negY, toW_a₁, toW_a₂, toW_a₃, zero_mul, sub_zero]
    rw [Prod.mk.injEq]
    refine ⟨?_, ?_⟩ <;> field_simp <;> ring

/-- Closure: `add` preserves `Valid`. (Result coords = Mathlib `addX`/`addY`; `nonsingular_add`
gives on-curveness.) -/
theorem valid_add {a b : F} [(toW a b).IsElliptic] {p q : F × F}
    (hp : Valid a b p) (hq : Valid a b q) : Valid a b (add a p q) := by
  by_cases hp0 : p = (0, 0)
  · rw [hp0, zero_add]; exact hq
  by_cases hq0 : q = (0, 0)
  · rw [hq0, add_zero]; exact hp
  obtain ⟨x₁, y₁⟩ := p
  obtain ⟨x₂, y₂⟩ := q
  have hOp : OnCurve a b (x₁, y₁) := hp.resolve_right hp0
  have hOq : OnCurve a b (x₂, y₂) := hq.resolve_right hq0
  by_cases hinv : x₁ = x₂ ∧ y₁ + y₂ = 0
  · right
    obtain ⟨hx, hy⟩ := hinv
    have hqp : (x₂, y₂) = neg (x₁, y₁) := by
      simp only [neg, Prod.mk.injEq]
      exact ⟨hx.symm, by linear_combination hy⟩
    rw [hqp, add_neg]
  · left
    rw [add_eq_addXY hp0 hq0 hinv]
    have hn : negY (toW a b) x₂ y₂ = -y₂ := by simp [negY]
    have hxy' : ¬(x₁ = x₂ ∧ y₁ = negY (toW a b) x₂ y₂) := by
      rintro ⟨hx, hyeq⟩
      refine hinv ⟨hx, ?_⟩
      rw [hn] at hyeq; rw [hyeq]; ring
    have hns := nonsingular_add (nonsingular_toW hOp) (nonsingular_toW hOq) hxy'
    exact equation_toW.mp hns.left

/-- Commutativity. (Generic branch is pure field algebra; doubling branch forces `p = q` from
on-curve; `𝒪` branches from the identity laws.) -/
theorem add_comm {a b : F} {p q : F × F} (hp : Valid a b p) (hq : Valid a b q) :
    add a p q = add a q p := by
  by_cases hp0 : p = (0, 0)
  · rw [hp0, zero_add, add_zero]
  by_cases hq0 : q = (0, 0)
  · rw [hq0, zero_add, add_zero]
  obtain ⟨x₁, y₁⟩ := p
  obtain ⟨x₂, y₂⟩ := q
  have hOp : OnCurve a b (x₁, y₁) := hp.resolve_right hp0
  have hOq : OnCurve a b (x₂, y₂) := hq.resolve_right hq0
  by_cases hinv : x₁ = x₂ ∧ y₁ + y₂ = 0
  · obtain ⟨hx, hy⟩ := hinv
    have e1 : add a (x₁, y₁) (x₂, y₂) = (0, 0) := by
      have h : (x₂, y₂) = neg (x₁, y₁) := by
        simp only [neg, Prod.mk.injEq]; exact ⟨hx.symm, by linear_combination hy⟩
      rw [h, add_neg]
    have e2 : add a (x₂, y₂) (x₁, y₁) = (0, 0) := by
      have h : (x₁, y₁) = neg (x₂, y₂) := by
        simp only [neg, Prod.mk.injEq]; exact ⟨hx, by linear_combination hy⟩
      rw [h, add_neg]
    rw [e1, e2]
  · have hinv' : ¬(x₂ = x₁ ∧ y₂ + y₁ = 0) :=
      fun ⟨hx, hy⟩ => hinv ⟨hx.symm, by linear_combination hy⟩
    rw [add_eq_addXY (b := b) hp0 hq0 hinv, add_eq_addXY (b := b) hq0 hp0 hinv']
    by_cases hx : x₁ = x₂
    · have hsum : y₁ + y₂ ≠ 0 := fun h => hinv ⟨hx, h⟩
      have hy12 : y₁ = y₂ := by
        simp only [OnCurve] at hOp hOq
        have hsq : (y₁ - y₂) * (y₁ + y₂) = 0 := by rw [hx] at hOp; linear_combination hOp - hOq
        exact sub_eq_zero.mp ((mul_eq_zero.mp hsq).resolve_right hsum)
      subst hx; subst hy12; rfl
    · have hd1 : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx
      have hd2 : x₂ - x₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
      rw [slope_of_X_ne hx, slope_of_X_ne (Ne.symm hx)]
      simp only [addX, addY, negAddY, negY, toW_a₁, toW_a₂, toW_a₃, zero_mul, sub_zero]
      rw [Prod.mk.injEq]
      refine ⟨?_, ?_⟩ <;> field_simp <;> ring

/-! ### Transport to Mathlib's `Point` group for associativity

`toPt` sends a representable point to Mathlib's `Point` (`𝒪 ↦ 0`, on-curve `(x, y) ↦ some x y`),
with `ofPt` the coordinate left-inverse. `toPt_add` is the homomorphism property; associativity is
then inherited from Mathlib's `AddCommGroup (toW a b).Point`. All of this needs `b ≠ 0` so that
the `(0, 0)` sentinel maps to `0` (i.e. `(0, 0)` is genuinely off the curve). -/

/-- The Mathlib point of a representable point: `𝒪 ↦ 0`, on-curve `(x, y) ↦ some x y`. -/
noncomputable def toPt (a b : F) [(toW a b).IsElliptic] (p : F × F) : Point (toW a b) :=
  if h : OnCurve a b p then .some p.1 p.2 (nonsingular_toW h) else 0

/-- Coordinate left-inverse of `toPt` (`0 ↦ 𝒪`, `some x y _ ↦ (x, y)`). -/
def ofPt {a b : F} (P : Point (toW a b)) : F × F :=
  match P with
  | .zero => (0, 0)
  | @Point.some _ _ _ x y _ => (x, y)

lemma toPt_some {a b : F} [(toW a b).IsElliptic] {x y : F} (h : OnCurve a b (x, y)) :
    toPt a b (x, y) = .some x y (nonsingular_toW h) := dif_pos h

lemma toPt_zero {a b : F} (hb : b ≠ 0) [(toW a b).IsElliptic] : toPt a b (0, 0) = 0 :=
  dif_neg (not_onCurve_zero hb)

lemma ofPt_toPt {a b : F} (hb : b ≠ 0) [(toW a b).IsElliptic] {p : F × F} (hp : Valid a b p) :
    ofPt (toPt a b p) = p := by
  rcases hp with hOp | hp0
  · obtain ⟨x, y⟩ := p; rw [toPt_some hOp]; rfl
  · rw [hp0, toPt_zero hb]; rfl

/-- The homomorphism property: `toPt` carries our `add` to Mathlib's `Point` addition. -/
lemma toPt_add {a b : F} (hb : b ≠ 0) [(toW a b).IsElliptic] {p q : F × F}
    (hp : Valid a b p) (hq : Valid a b q) :
    toPt a b (add a p q) = toPt a b p + toPt a b q := by
  by_cases hp0 : p = (0, 0)
  · rw [hp0, zero_add, toPt_zero hb, _root_.zero_add]
  by_cases hq0 : q = (0, 0)
  · rw [hq0, add_zero, toPt_zero hb, _root_.add_zero]
  obtain ⟨x₁, y₁⟩ := p
  obtain ⟨x₂, y₂⟩ := q
  have hOp : OnCurve a b (x₁, y₁) := hp.resolve_right hp0
  have hOq : OnCurve a b (x₂, y₂) := hq.resolve_right hq0
  have hn : negY (toW a b) x₂ y₂ = -y₂ := by simp [negY]
  rw [toPt_some hOp, toPt_some hOq]
  by_cases hinv : x₁ = x₂ ∧ y₁ + y₂ = 0
  · obtain ⟨hx, hy⟩ := hinv
    have e : add a (x₁, y₁) (x₂, y₂) = (0, 0) := by
      have h : (x₂, y₂) = neg (x₁, y₁) := by
        simp only [neg, Prod.mk.injEq]; exact ⟨hx.symm, by linear_combination hy⟩
      rw [h, add_neg]
    rw [e, toPt_zero hb, Point.add_of_Y_eq hx (by rw [hn]; linear_combination hy)]
  · have hxy' : ¬(x₁ = x₂ ∧ y₁ = negY (toW a b) x₂ y₂) := by
      rintro ⟨hx, hyeq⟩; exact hinv ⟨hx, by rw [hn] at hyeq; rw [hyeq]; ring⟩
    have e : add a (x₁, y₁) (x₂, y₂)
        = (addX (toW a b) x₁ x₂ (slope (toW a b) x₁ x₂ y₁ y₂),
           addY (toW a b) x₁ x₂ y₁ (slope (toW a b) x₁ x₂ y₁ y₂)) :=
      add_eq_addXY hp0 hq0 hinv
    have hO : OnCurve a b
        (addX (toW a b) x₁ x₂ (slope (toW a b) x₁ x₂ y₁ y₂),
         addY (toW a b) x₁ x₂ y₁ (slope (toW a b) x₁ x₂ y₁ y₂)) :=
      equation_toW.mp (nonsingular_add (nonsingular_toW hOp) (nonsingular_toW hOq) hxy').left
    rw [e, Point.add_some hxy', toPt_some hO]

/-- Associativity (the hard axiom), by transport to Mathlib's `Point` `AddCommGroup`. -/
theorem add_assoc {a b : F} (hb : b ≠ 0) [(toW a b).IsElliptic] {p q r : F × F}
    (hp : Valid a b p) (hq : Valid a b q) (hr : Valid a b r) :
    add a (add a p q) r = add a p (add a q r) := by
  have key : toPt a b (add a (add a p q) r) = toPt a b (add a p (add a q r)) := by
    rw [toPt_add hb (valid_add hp hq) hr, toPt_add hb hp hq,
      toPt_add hb hp (valid_add hq hr), toPt_add hb hq hr, _root_.add_assoc]
  calc add a (add a p q) r
      = ofPt (toPt a b (add a (add a p q) r)) :=
        (ofPt_toPt hb (valid_add (valid_add hp hq) hr)).symm
    _ = ofPt (toPt a b (add a p (add a q r))) := by rw [key]
    _ = add a p (add a q r) := ofPt_toPt hb (valid_add hp (valid_add hq hr))

omit [DecidableEq F] in
/-- `neg` preserves `Valid` (on-curve since `(-y)² = y²`; the `𝒪` sentinel is fixed). -/
theorem valid_neg {a b : F} {p : F × F} (hp : Valid a b p) : Valid a b (neg p) := by
  rcases hp with h | h
  · left; simp only [OnCurve, neg] at h ⊢; linear_combination h
  · right; rw [h]; simp [neg]

/-- Closure of the spec-level `smul`: `n • p` stays `Valid`, by induction on `valid_add`. -/
theorem valid_smul {a b : F} [(toW a b).IsElliptic] {p : F × F} (hp : Valid a b p) :
    ∀ n : ℕ, Valid a b (smul a n p)
  | 0 => Or.inr rfl
  | n + 1 => valid_add (valid_smul hp n) hp

/-! ## Rich bundled types -/

/-- The discriminant of the short-Weierstrass curve `y² = x³ + A x + B`. -/
def sw_Δ (A B : F) : F := -16 * (4 * A ^ 3 + 27 * B ^ 2)

/-- A short-Weierstrass elliptic curve: coefficients `A`, `B`, bundled with nonsingularity
(`IsUnit sw_Δ`, which over a field is `sw_Δ ≠ 0` and self-excludes characteristic 2) and `B ≠ 0`
(so the `𝒪 = (0, 0)` sentinel is off the curve). -/
structure SWCurve (F : Type*) [Field F] where
  A : F
  B : F
  IsElliptic : IsUnit (sw_Δ A B)
  B_nonzero : B ≠ 0

/-- A point on `E`, correct by construction: on the curve, or the identity `𝒪 = (0, 0)`. -/
structure SWPoint (E : SWCurve F) where
  x : F
  y : F
  onCurve : Valid E.A E.B (x, y)
deriving Repr

omit [DecidableEq F] in
/-- `(0, 0)` is off the curve `E`, immediate from `E.B_nonzero`. -/
theorem origin_not_on_curve (E : SWCurve F) : ¬ OnCurve E.A E.B (0, 0) :=
  not_onCurve_zero E.B_nonzero

/-- The identity point `𝒪` on `E`. -/
def SWPoint.zero (E : SWCurve F) : SWPoint E := ⟨0, 0, Or.inr rfl⟩

omit [DecidableEq F] in
/-- For the short form, Mathlib's Weierstrass discriminant is our `sw_Δ`. -/
lemma toW_Δ (A B : F) : (toW A B).Δ = sw_Δ A B := by
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, toW_a₁, toW_a₂, toW_a₃, toW_a₄, toW_a₆, sw_Δ]
  ring

/-- `E`'s bundled `IsUnit (sw_Δ ..)` is exactly Mathlib's ellipticity of `toW E.A E.B`, so the raw
group-law lemmas (which require `[(toW A B).IsElliptic]`) apply to `E` by instance resolution. -/
instance instIsElliptic (E : SWCurve F) : (toW E.A E.B).IsElliptic where
  isUnit := by rw [toW_Δ]; exact E.IsElliptic

omit [DecidableEq F] in
/-- Two representable points are equal when their coordinate pairs agree (`onCurve` is a `Prop`). -/
theorem SWPoint.ext_pair {E : SWCurve F} {P Q : SWPoint E}
    (h : (P.x, P.y) = (Q.x, Q.y)) : P = Q := by
  obtain ⟨px, py, hP⟩ := P
  obtain ⟨qx, qy, hQ⟩ := Q
  injection h with hx hy
  subst hx; subst hy; rfl

/-- Addition lifted to `SWPoint E`; closure from `valid_add`. -/
def sw_add {E : SWCurve F} (P Q : SWPoint E) : SWPoint E :=
  haveI := instIsElliptic E
  ⟨(add E.A (P.x, P.y) (Q.x, Q.y)).1, (add E.A (P.x, P.y) (Q.x, Q.y)).2,
   valid_add P.onCurve Q.onCurve⟩

/-- Negation lifted to `SWPoint E`; closure from `valid_neg`. -/
def sw_neg {E : SWCurve F} (P : SWPoint E) : SWPoint E :=
  ⟨(neg (P.x, P.y)).1, (neg (P.x, P.y)).2, valid_neg P.onCurve⟩

instance (E : SWCurve F) : Zero (SWPoint E) := ⟨SWPoint.zero E⟩
instance (E : SWCurve F) : Add (SWPoint E) := ⟨sw_add⟩
instance (E : SWCurve F) : Neg (SWPoint E) := ⟨sw_neg⟩

/-- The abelian group of representable points on `E`: identity laws and inverses are immediate;
commutativity and associativity transport from the raw `add` lemmas, whose hypotheses `E`'s bundled
fields (`IsElliptic`, `B_nonzero`) discharge. -/
instance (E : SWCurve F) : AddCommGroup (SWPoint E) where
  add := sw_add
  zero := SWPoint.zero E
  neg := sw_neg
  nsmul := nsmulRec
  zsmul := zsmulRec
  add_assoc P Q R := by
    haveI := instIsElliptic E
    exact SWPoint.ext_pair (add_assoc E.B_nonzero P.onCurve Q.onCurve R.onCurve)
  zero_add P := SWPoint.ext_pair (ShortWeierstrass.zero_add E.A (P.x, P.y))
  add_zero P := SWPoint.ext_pair (ShortWeierstrass.add_zero E.A (P.x, P.y))
  add_comm P Q := SWPoint.ext_pair (add_comm P.onCurve Q.onCurve)
  neg_add_cancel P := SWPoint.ext_pair (by
    show add E.A (neg (P.x, P.y)) (P.x, P.y) = (0, 0)
    rw [add_comm (valid_neg P.onCurve) P.onCurve]
    exact add_neg E.A (P.x, P.y))

omit [DecidableEq F] in
@[simp] lemma SWPoint.zero_x {E : SWCurve F} : (0 : SWPoint E).x = 0 := rfl
omit [DecidableEq F] in
@[simp] lemma SWPoint.zero_y {E : SWCurve F} : (0 : SWPoint E).y = 0 := rfl
omit [DecidableEq F] in
@[simp] lemma SWPoint.neg_x {E : SWCurve F} (P : SWPoint E) : (-P).x = P.x := rfl
omit [DecidableEq F] in
@[simp] lemma SWPoint.neg_y {E : SWCurve F} (P : SWPoint E) : (-P).y = -P.y := rfl
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

/-- The group action `n • P` on `SWPoint E` is the spec-level `smul` on the underlying coordinates,
so the two notions of scalar multiplication agree. -/
theorem coords_nsmul {E : SWCurve F} (n : ℕ) (P : SWPoint E) :
    ((n • P).x, (n • P).y) = smul E.A n (P.x, P.y) := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [succ_nsmul]
    show add E.A ((k • P).x, (k • P).y) (P.x, P.y) = smul E.A (k + 1) (P.x, P.y)
    rw [ih]
    rfl

/-! ## The affine coordinate system

`E` as an instance of the general `CoordinateSystem` abstraction: the injective (`Rel = Eq`) case,
built from the proven affine group law. This validates `CoordinateSystem` against a real curve. Its
`.Quot` is the affine group element (a quotient by `Eq`, hence isomorphic to `SWPoint E`). -/

/-- The affine coordinate system of a short-Weierstrass curve `E` (`Rel = Eq`). -/
def affineCoordinateSystem (E : SWCurve F) : CoordinateSystem (F × F) :=
  haveI := instIsElliptic E
  { Valid := ShortWeierstrass.Valid E.A E.B
    Rel := Eq
    zero := (0, 0)
    add := ShortWeierstrass.add E.A
    neg := ShortWeierstrass.neg
    valid_zero := Or.inr rfl
    valid_add := fun hp hq => ShortWeierstrass.valid_add hp hq
    valid_neg := fun h => ShortWeierstrass.valid_neg h
    rel_refl := fun _ => rfl
    rel_symm := Eq.symm
    rel_trans := Eq.trans
    add_congr := fun ha hb => by rw [ha, hb]
    neg_congr := fun ha => by rw [ha]
    zero_add := fun {p} _ => ShortWeierstrass.zero_add E.A p
    add_zero := fun {p} _ => ShortWeierstrass.add_zero E.A p
    add_assoc := fun hp hq hr => ShortWeierstrass.add_assoc E.B_nonzero hp hq hr
    add_comm := fun hp hq => ShortWeierstrass.add_comm hp hq
    neg_add := fun {p} h => by
      rw [ShortWeierstrass.add_comm (ShortWeierstrass.valid_neg h) h]
      exact ShortWeierstrass.add_neg E.A p }

end CompElliptic.CurveForms.ShortWeierstrass
