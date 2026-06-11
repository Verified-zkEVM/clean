import Clean.Orchard.Ecc.WitnessPoint
import Clean.Orchard.Ecc.Theorems
import Clean.Utils.Tactics
import Mathlib.Tactic

namespace Orchard
namespace Ecc

/-!
Reference:
`halo2@halo2_gadgets-0.5.0/halo2_gadgets/src/ecc/chip/add.rs`
- `complete addition`

This ports the complete-addition custom gate as a row assertion over the copied input
points, output point, and auxiliary advice values `lambda`, `alpha`, `beta`, `gamma`, and
`delta`. The Rust assignment logic computes these auxiliaries by case-splitting on
exceptional point-addition cases; higher-level Clean circuits can witness them and call
this assertion.
-/

structure CompleteAddRow (F : Type) where
  p : Point F
  q : Point F
  r : Point F
  lambda : F
  alpha : F
  beta : F
  gamma : F
  delta : F
deriving ProvableStruct

namespace CompleteAdd

structure Input (F : Type) where
  p : Point F
  q : Point F
deriving ProvableStruct

section ValueModel

variable {F : Type} [Field F] [DecidableEq F]

/-- The semantic side condition needed by Halo2's complete-add assignment logic.

The Rust implementation treats `x = 0` as the identity branch. This is sound for the
Pallas encoding because `(0, y)` is not a non-identity curve point. We keep that property
explicit here instead of baking it into the row constraints. -/
def XZeroImpliesIdentity (point : Point F) : Prop :=
  point.x = 0 → point.y = 0

def lambdaValue (input : Input F) : F :=
  if input.q.x = input.p.x then
    if input.p.y ≠ 0 then
      (3 * input.p.x * input.p.x) * (2 * input.p.y)⁻¹
    else
      0
  else
    (input.q.y - input.p.y) * (input.q.x - input.p.x)⁻¹

def outputValue (input : Input F) : Point F :=
  let lambda := lambdaValue input
  if input.p.x = 0 then
    input.q
  else if input.q.x = 0 then
    input.p
  else if input.q.x = input.p.x ∧ input.q.y = -input.p.y then
    { x := 0, y := 0 }
  else
    let xR := lambda * lambda - input.p.x - input.q.x
    let yR := lambda * (input.p.x - xR) - input.p.y
    { x := xR, y := yR }

def rowValue (input : Input F) : CompleteAddRow F where
  p := input.p
  q := input.q
  r := outputValue input
  lambda := lambdaValue input
  alpha := (input.q.x - input.p.x)⁻¹
  beta := input.p.x⁻¹
  gamma := input.q.x⁻¹
  delta :=
    if input.q.x = input.p.x then
      (input.q.y + input.p.y)⁻¹
    else
      0

theorem outputValue_eq_swAdd {input : Input F}
    (hpZero : XZeroImpliesIdentity input.p)
    (hqZero : XZeroImpliesIdentity input.q) :
    Point.coords (outputValue input) =
      CompElliptic.CurveForms.ShortWeierstrass.add
        (0 : F) (Point.coords input.p) (Point.coords input.q) := by
  rcases input with ⟨⟨px, py⟩, ⟨qx, qy⟩⟩
  unfold Point.coords outputValue lambdaValue
    CompElliptic.CurveForms.ShortWeierstrass.add XZeroImpliesIdentity at *
  simp only
  by_cases hpx : px = 0
  · have hpy : py = 0 := hpZero hpx
    simp [hpx, hpy]
  · by_cases hqx : qx = 0
    · have hqy : qy = 0 := hqZero hqx
      simp [hpx, hqx, hqy]
    · simp [hpx, hqx]
      by_cases hx : px = qx
      · have hx' : qx = px := hx.symm
        rw [if_pos hx', if_pos hx]
        by_cases hy : py + qy = 0
        · have hqy : qy = -py := by linear_combination hy
          simp [hx', hqy]
        · have hqy : ¬ qy = -py := by
            intro h
            apply hy
            rw [h]
            ring
          simp [hx', hqy, hy]
          constructor <;>
            by_cases hpy : py = 0 <;>
              simp [hpy] <;> ring
      · have hx' : ¬ qx = px := fun h => hx h.symm
        simp [hx, hx']
        constructor <;> ring

theorem outputValue_eq_swAdd_pallas {input : Input Fp}
    (hp : Point.isPointOrIdentity input.p)
    (hq : Point.isPointOrIdentity input.q) :
    Point.coords (outputValue input) =
      CompElliptic.CurveForms.ShortWeierstrass.add
        (0 : Fp) (Point.coords input.p) (Point.coords input.q) :=
  outputValue_eq_swAdd
    (Point.y_eq_zero_of_isPointOrIdentity_of_x_eq_zero hp)
    (Point.y_eq_zero_of_isPointOrIdentity_of_x_eq_zero hq)

theorem pallas_two_ne_zero : (2 : Fp) ≠ 0 := by
  decide

theorem pallas_add_self_ne_zero {y : Fp} (hy : y ≠ 0) :
    y + y ≠ 0 := by
  intro h
  have hmul : (2 : Fp) * y = 0 := by
    linear_combination h
  exact hy ((mul_eq_zero.mp hmul).resolve_left pallas_two_ne_zero)

theorem pallas_y_eq_or_neg_of_same_x {p q : Point Fp}
    (hp : Point.isPointOrIdentity p) (hq : Point.isPointOrIdentity q)
    (hpx : p.x ≠ 0) (hqx : q.x ≠ 0) (hx : q.x = p.x) :
    q.y = p.y ∨ q.y = -p.y := by
  have hpCurve : Point.onCurve p := by
    rcases hp with hId | hCurve
    · exact False.elim (hpx hId.1)
    · exact hCurve
  have hqCurve : Point.onCurve q := by
    rcases hq with hId | hCurve
    · exact False.elim (hqx hId.1)
    · exact hCurve
  unfold Point.onCurve pallasB at hpCurve hqCurve
  have hsquare : (q.y - p.y) * (q.y + p.y) = 0 := by
    rw [hx] at hqCurve
    linear_combination hqCurve - hpCurve
  rcases mul_eq_zero.mp hsquare with h | h
  · left
    exact sub_eq_zero.mp h
  · right
    linear_combination h

end ValueModel

namespace Gate

def xQMinusXP {K : Type} [Sub K] (row : CompleteAddRow K) : K :=
  row.q.x - row.p.x

def xPMinusXR {K : Type} [Sub K] (row : CompleteAddRow K) : K :=
  row.p.x - row.r.x

def yQPlusYP {K : Type} [Add K] (row : CompleteAddRow K) : K :=
  row.q.y + row.p.y

def ifAlpha {K : Type} [Sub K] [Mul K] (row : CompleteAddRow K) : K :=
  xQMinusXP row * row.alpha

def ifBeta {K : Type} [Mul K] (row : CompleteAddRow K) : K :=
  row.p.x * row.beta

def ifGamma {K : Type} [Mul K] (row : CompleteAddRow K) : K :=
  row.q.x * row.gamma

def ifDelta {K : Type} [Add K] [Mul K] (row : CompleteAddRow K) : K :=
  yQPlusYP row * row.delta

def nonexceptionalXR {K : Type} [Sub K] [Mul K] (row : CompleteAddRow K) : K :=
  row.lambda * row.lambda - row.p.x - row.q.x - row.r.x

def nonexceptionalYR {K : Type} [Sub K] [Mul K] (row : CompleteAddRow K) : K :=
  row.lambda * xPMinusXR row - row.p.y - row.r.y

def poly1 {K : Type} [Add K] [Sub K] [Mul K] (row : CompleteAddRow K) : K :=
  let incomplete := xQMinusXP row * row.lambda - (row.q.y - row.p.y)
  xQMinusXP row * incomplete

def poly2 {K : Type} [One K] [Add K] [Sub K] [Mul K] [OfNat K 2] [OfNat K 3]
    (row : CompleteAddRow K) : K :=
  (1 - ifAlpha row) * (2 * row.p.y * row.lambda - 3 * row.p.x * row.p.x)

def poly3a {K : Type} [Sub K] [Mul K] (row : CompleteAddRow K) : K :=
  row.p.x * row.q.x * xQMinusXP row * nonexceptionalXR row

def poly3b {K : Type} [Sub K] [Mul K] (row : CompleteAddRow K) : K :=
  row.p.x * row.q.x * xQMinusXP row * nonexceptionalYR row

def poly3c {K : Type} [Add K] [Sub K] [Mul K] (row : CompleteAddRow K) : K :=
  row.p.x * row.q.x * yQPlusYP row * nonexceptionalXR row

def poly3d {K : Type} [Add K] [Sub K] [Mul K] (row : CompleteAddRow K) : K :=
  row.p.x * row.q.x * yQPlusYP row * nonexceptionalYR row

def poly4a {K : Type} [One K] [Sub K] [Mul K] (row : CompleteAddRow K) : K :=
  (1 - ifBeta row) * (row.r.x - row.q.x)

def poly4b {K : Type} [One K] [Sub K] [Mul K] (row : CompleteAddRow K) : K :=
  (1 - ifBeta row) * (row.r.y - row.q.y)

def poly5a {K : Type} [One K] [Sub K] [Mul K] (row : CompleteAddRow K) : K :=
  (1 - ifGamma row) * (row.r.x - row.p.x)

def poly5b {K : Type} [One K] [Sub K] [Mul K] (row : CompleteAddRow K) : K :=
  (1 - ifGamma row) * (row.r.y - row.p.y)

def poly6a {K : Type} [One K] [Add K] [Sub K] [Mul K] (row : CompleteAddRow K) : K :=
  (1 - ifAlpha row - ifDelta row) * row.r.x

def poly6b {K : Type} [One K] [Add K] [Sub K] [Mul K] (row : CompleteAddRow K) : K :=
  (1 - ifAlpha row - ifDelta row) * row.r.y

def slopeLine {K : Type} [Sub K] [Mul K] (row : CompleteAddRow K) : Prop :=
  xQMinusXP row * row.lambda = row.q.y - row.p.y

def tangentLine {K : Type} [Mul K] [OfNat K 2] [OfNat K 3] (row : CompleteAddRow K) : Prop :=
  2 * row.p.y * row.lambda = 3 * row.p.x * row.p.x

def nonexceptionalResult {K : Type} [Sub K] [Mul K] (row : CompleteAddRow K) : Prop :=
  row.r.x = row.lambda * row.lambda - row.p.x - row.q.x ∧
    row.r.y = row.lambda * xPMinusXR row - row.p.y

def leftIdentityResult {K : Type} (row : CompleteAddRow K) : Prop :=
  row.r = row.q

def rightIdentityResult {K : Type} (row : CompleteAddRow K) : Prop :=
  row.r = row.p

def inverseResult {K : Type} [Zero K] (row : CompleteAddRow K) : Prop :=
  row.r.x = 0 ∧ row.r.y = 0

def Spec (row : CompleteAddRow Fp) : Prop :=
  (xQMinusXP row ≠ 0 → slopeLine row) ∧
    (ifAlpha row ≠ 1 → tangentLine row) ∧
    (row.p.x * row.q.x * xQMinusXP row ≠ 0 → nonexceptionalResult row) ∧
    (row.p.x * row.q.x * yQPlusYP row ≠ 0 → nonexceptionalResult row) ∧
    (ifBeta row ≠ 1 → leftIdentityResult row) ∧
    (ifGamma row ≠ 1 → rightIdentityResult row) ∧
    (ifAlpha row + ifDelta row ≠ 1 → inverseResult row)

def main (row : Var CompleteAddRow Fp) : Circuit Fp Unit := do
  assertZero (poly1 row)
  assertZero (poly2 row)
  assertZero (poly3a row)
  assertZero (poly3b row)
  assertZero (poly3c row)
  assertZero (poly3d row)
  assertZero (poly4a row)
  assertZero (poly4b row)
  assertZero (poly5a row)
  assertZero (poly5b row)
  assertZero (poly6a row)
  assertZero (poly6b row)

def circuit : FormalAssertion Fp CompleteAddRow where
  name := "GATE complete addition"
  main
  Spec := Spec
  soundness := by
    circuit_proof_start [main, Spec, slopeLine, tangentLine, nonexceptionalResult,
      leftIdentityResult, rightIdentityResult, inverseResult, poly1, poly2, poly3a, poly3b,
      poly3c, poly3d, poly4a, poly4b, poly5a, poly5b, poly6a, poly6b, nonexceptionalXR,
      nonexceptionalYR, ifAlpha, ifBeta, ifGamma, ifDelta, xQMinusXP, xPMinusXR, yQPlusYP]
    rcases input_p with ⟨px, py⟩
    rcases input_q with ⟨qx, qy⟩
    rcases input_r with ⟨rx, ry⟩
    simp_all [sub_eq_add_neg]
    rcases h_holds with
      ⟨h1, h2, h3a, h3b, h3c, h3d, h4a, h4b, h5a, h5b, h6a, h6b⟩
    constructor
    · intro hne
      rcases h1 with hzero | hline
      · exact False.elim (hne hzero)
      · linear_combination hline
    constructor
    · intro hne
      rcases h2 with hflag | htangent
      · have : (qx + -px) * input_alpha = 1 := by linear_combination -hflag
        exact False.elim (hne this)
      · linear_combination htangent
    constructor
    · intro hpx hqx hxdiff
      constructor
      · rcases h3a with hzero | hx
        · rcases hzero with hzero | hzero
          · rcases hzero with hzero | hzero
            · exact False.elim (hpx hzero)
            · exact False.elim (hqx hzero)
          · exact False.elim (hxdiff hzero)
        · linear_combination -hx
      · rcases h3b with hzero | hy
        · rcases hzero with hzero | hzero
          · rcases hzero with hzero | hzero
            · exact False.elim (hpx hzero)
            · exact False.elim (hqx hzero)
          · exact False.elim (hxdiff hzero)
        · linear_combination -hy
    constructor
    · intro hpx hqx hysum
      constructor
      · rcases h3c with hzero | hx
        · rcases hzero with hzero | hzero
          · rcases hzero with hzero | hzero
            · exact False.elim (hpx hzero)
            · exact False.elim (hqx hzero)
          · exact False.elim (hysum hzero)
        · linear_combination -hx
      · rcases h3d with hzero | hy
        · rcases hzero with hzero | hzero
          · rcases hzero with hzero | hzero
            · exact False.elim (hpx hzero)
            · exact False.elim (hqx hzero)
          · exact False.elim (hysum hzero)
        · linear_combination -hy
    constructor
    · intro hne
      constructor
      · rcases h4a with hflag | hx
        · have : px * input_beta = 1 := by linear_combination -hflag
          exact False.elim (hne this)
        · linear_combination hx
      · rcases h4b with hflag | hy
        · have : px * input_beta = 1 := by linear_combination -hflag
          exact False.elim (hne this)
        · linear_combination hy
    constructor
    · intro hne
      constructor
      · rcases h5a with hflag | hx
        · have : qx * input_gamma = 1 := by linear_combination -hflag
          exact False.elim (hne this)
        · linear_combination hx
      · rcases h5b with hflag | hy
        · have : qx * input_gamma = 1 := by linear_combination -hflag
          exact False.elim (hne this)
        · linear_combination hy
    · intro hne
      constructor
      · rcases h6a with hflag | hx
        · have : (qx + -px) * input_alpha + (qy + py) * input_delta = 1 := by
            linear_combination -hflag
          exact False.elim (hne this)
        · exact hx
      · rcases h6b with hflag | hy
        · have : (qx + -px) * input_alpha + (qy + py) * input_delta = 1 := by
            linear_combination -hflag
          exact False.elim (hne this)
        · exact hy
  completeness := by
    circuit_proof_start [main, Spec, slopeLine, tangentLine, nonexceptionalResult,
      leftIdentityResult, rightIdentityResult, inverseResult, poly1, poly2, poly3a, poly3b,
      poly3c, poly3d, poly4a, poly4b, poly5a, poly5b, poly6a, poly6b, nonexceptionalXR,
      nonexceptionalYR, ifAlpha, ifBeta, ifGamma, ifDelta, xQMinusXP, xPMinusXR, yQPlusYP]
    rcases input_p with ⟨px, py⟩
    rcases input_q with ⟨qx, qy⟩
    rcases input_r with ⟨rx, ry⟩
    simp_all [sub_eq_add_neg]
    rcases h_spec with ⟨h1, h2, h3, h3', h4, h5, h6⟩
    constructor
    · by_cases hzero : qx + -px = 0
      · exact Or.inl hzero
      · exact Or.inr (by
        have hline := h1 hzero
        linear_combination hline)
    constructor
    · by_cases hflag : (qx + -px) * input_alpha = 1
      · exact Or.inl (by linear_combination -hflag)
      · exact Or.inr (by
        have htangent := h2 hflag
        linear_combination htangent)
    constructor
    · by_cases hpx : px = 0
      · exact Or.inl (Or.inl (Or.inl hpx))
      · by_cases hqx : qx = 0
        · exact Or.inl (Or.inl (Or.inr hqx))
        · by_cases hxdiff : qx + -px = 0
          · exact Or.inl (Or.inr hxdiff)
          · exact Or.inr (by
              have hx := (h3 hpx hqx hxdiff).1
              linear_combination -hx)
    constructor
    · by_cases hpx : px = 0
      · exact Or.inl (Or.inl (Or.inl hpx))
      · by_cases hqx : qx = 0
        · exact Or.inl (Or.inl (Or.inr hqx))
        · by_cases hxdiff : qx + -px = 0
          · exact Or.inl (Or.inr hxdiff)
          · exact Or.inr (by
              have hy := (h3 hpx hqx hxdiff).2
              linear_combination -hy)
    constructor
    · by_cases hpx : px = 0
      · exact Or.inl (Or.inl (Or.inl hpx))
      · by_cases hqx : qx = 0
        · exact Or.inl (Or.inl (Or.inr hqx))
        · by_cases hysum : qy + py = 0
          · exact Or.inl (Or.inr hysum)
          · exact Or.inr (by
              have hx := (h3' hpx hqx hysum).1
              linear_combination -hx)
    constructor
    · by_cases hpx : px = 0
      · exact Or.inl (Or.inl (Or.inl hpx))
      · by_cases hqx : qx = 0
        · exact Or.inl (Or.inl (Or.inr hqx))
        · by_cases hysum : qy + py = 0
          · exact Or.inl (Or.inr hysum)
          · exact Or.inr (by
              have hy := (h3' hpx hqx hysum).2
              linear_combination -hy)
    constructor
    · by_cases hflag : px * input_beta = 1
      · exact Or.inl (by linear_combination -hflag)
      · exact Or.inr (by
          have hx := (h4 hflag).1
          linear_combination hx)
    constructor
    · by_cases hflag : px * input_beta = 1
      · exact Or.inl (by linear_combination -hflag)
      · exact Or.inr (by
          have hy := (h4 hflag).2
          linear_combination hy)
    constructor
    · by_cases hflag : qx * input_gamma = 1
      · exact Or.inl (by linear_combination -hflag)
      · exact Or.inr (by
          have hx := (h5 hflag).1
          linear_combination hx)
    constructor
    · by_cases hflag : qx * input_gamma = 1
      · exact Or.inl (by linear_combination -hflag)
      · exact Or.inr (by
          have hy := (h5 hflag).2
          linear_combination hy)
    constructor
    · by_cases hflag : (qx + -px) * input_alpha + (qy + py) * input_delta = 1
      · exact Or.inl (by linear_combination -hflag)
      · exact Or.inr (h6 hflag).1
    · by_cases hflag : (qx + -px) * input_alpha + (qy + py) * input_delta = 1
      · exact Or.inl (by linear_combination -hflag)
      · exact Or.inr (h6 hflag).2

end Gate

open Gate

section EntryPoint

theorem rowValue_spec_pallas {input : Input Fp}
    (hp : Point.isPointOrIdentity input.p) (hq : Point.isPointOrIdentity input.q) :
    Spec (rowValue input) := by
  constructor
  · intro hxdiff
    unfold xQMinusXP rowValue at hxdiff
    unfold rowValue slopeLine xQMinusXP lambdaValue
    simp at hxdiff ⊢
    rw [if_neg]
    · field_simp [hxdiff]
    · intro hx
      exact hxdiff (sub_eq_zero.mpr hx)
  constructor
  · intro hflag
    dsimp [rowValue, tangentLine, ifAlpha, xQMinusXP, lambdaValue] at hflag ⊢
    simp at hflag ⊢
    by_cases hx : input.q.x = input.p.x
    · by_cases hpy : input.p.y = 0
      · have hpx : input.p.x = 0 := by
          by_contra hpx
          exact Point.y_ne_zero_of_isPointOrIdentity_of_x_ne_zero hp hpx hpy
        simp [hx, hpy, hpx]
      · simp [hx, hpy]
        have hden : (2 : Fp) * input.p.y ≠ 0 :=
          mul_ne_zero pallas_two_ne_zero hpy
        field_simp [hden, pallas_two_ne_zero]
    · have hcontra : (input.q.x - input.p.x) * (input.q.x - input.p.x)⁻¹ = 1 := by
        field_simp [sub_ne_zero.mpr hx]
      exact False.elim (hflag hcontra)
  constructor
  · intro hprod
    dsimp [rowValue, nonexceptionalResult, outputValue, xPMinusXR, lambdaValue,
      xQMinusXP] at hprod ⊢
    simp at hprod ⊢
    have hpx : input.p.x ≠ 0 := hprod.1.1
    have hqx : input.q.x ≠ 0 := hprod.1.2
    have hxdiff : input.q.x - input.p.x ≠ 0 := hprod.2
    have hx : input.q.x ≠ input.p.x := fun h => hxdiff (sub_eq_zero.mpr h)
    simp [hpx, hqx, hx]
  constructor
  · intro hprod
    dsimp [rowValue, nonexceptionalResult, outputValue, xPMinusXR, lambdaValue,
      yQPlusYP] at hprod ⊢
    simp at hprod ⊢
    have hpx : input.p.x ≠ 0 := hprod.1.1
    have hqx : input.q.x ≠ 0 := hprod.1.2
    have hysum : input.q.y + input.p.y ≠ 0 := hprod.2
    by_cases hx : input.q.x = input.p.x
    · have hsame := pallas_y_eq_or_neg_of_same_x hp hq hpx hqx hx
      rcases hsame with hy | hy
      · have hnotInv : ¬(input.q.x = input.p.x ∧ input.q.y = -input.p.y) := by
          intro hinv
          apply hysum
          rw [hinv.2]
          ring
        have hpy : input.p.y ≠ 0 :=
          Point.y_ne_zero_of_isPointOrIdentity_of_x_ne_zero hp hpx
        have hnotY : input.q.y ≠ -input.p.y := fun h => hnotInv ⟨hx, h⟩
        simp [hpx, hx, hnotY, hpy]
      · exact False.elim (hysum (by rw [hy]; ring))
    · have hnotInv : ¬(input.q.x = input.p.x ∧ input.q.y = -input.p.y) := by
        exact fun h => hx h.1
      simp [hpx, hqx, hx]
  constructor
  · intro hflag
    dsimp [rowValue, leftIdentityResult, ifBeta, outputValue] at hflag ⊢
    simp at hflag ⊢
    by_cases hpx : input.p.x = 0
    · simp [hpx]
    · have hcontra : input.p.x * input.p.x⁻¹ = 1 := by
        field_simp [hpx]
      exact False.elim (hflag hcontra)
  constructor
  · intro hflag
    dsimp [rowValue, rightIdentityResult, ifGamma, outputValue] at hflag ⊢
    by_cases hpx : input.p.x = 0
    · have hpy := Point.y_eq_zero_of_isPointOrIdentity_of_x_eq_zero hp hpx
      by_cases hqx : input.q.x = 0
      · have hqy := Point.y_eq_zero_of_isPointOrIdentity_of_x_eq_zero hq hqx
        have hpEq : input.p = ({ x := 0, y := 0 } : Point Fp) := by
          rw [Point.mk.injEq]
          exact ⟨hpx, hpy⟩
        have hqEq : input.q = ({ x := 0, y := 0 } : Point Fp) := by
          rw [Point.mk.injEq]
          exact ⟨hqx, hqy⟩
        simp [hpEq, hqEq]
      · have hcontra : input.q.x * input.q.x⁻¹ = 1 := by
          field_simp [hqx]
        exact False.elim (hflag hcontra)
    · by_cases hqx : input.q.x = 0
      · simp [hpx, hqx]
      · have hcontra : input.q.x * input.q.x⁻¹ = 1 := by
          field_simp [hqx]
        exact False.elim (hflag hcontra)
  · intro hflag
    dsimp [rowValue, inverseResult, ifAlpha, ifDelta, xQMinusXP, yQPlusYP,
      outputValue] at hflag ⊢
    simp at hflag ⊢
    by_cases hpx : input.p.x = 0
    · have hpy := Point.y_eq_zero_of_isPointOrIdentity_of_x_eq_zero hp hpx
      by_cases hqx : input.q.x = 0
      · have hqy := Point.y_eq_zero_of_isPointOrIdentity_of_x_eq_zero hq hqx
        simp [hpx, hqx, hqy]
      · have hcontra :
            ((input.q.x - input.p.x) * (input.q.x - input.p.x)⁻¹ +
              if input.q.x = input.p.x then
                (input.q.y + input.p.y) * (input.q.y + input.p.y)⁻¹
          else 0) = 1 := by
          simp [hpx, hqx]
        exact False.elim (hflag hcontra)
    · by_cases hqx : input.q.x = 0
      · have hcontra :
            ((input.q.x - input.p.x) * (input.q.x - input.p.x)⁻¹ +
              if input.q.x = input.p.x then
                (input.q.y + input.p.y) * (input.q.y + input.p.y)⁻¹
          else 0) = 1 := by
          have hne : ¬ input.q.x = input.p.x := by
            rw [hqx]
            exact fun h => hpx h.symm
          have hne0 : ¬ (0 : Fp) = input.p.x := fun h => hpx h.symm
          simp [hpx, hqx, hne0]
        exact False.elim (hflag hcontra)
      · by_cases hx : input.q.x = input.p.x
        · by_cases hy : input.q.y = -input.p.y
          · simp [hpx, hx, hy]
          · have hsame := pallas_y_eq_or_neg_of_same_x hp hq hpx hqx hx
            rcases hsame with hyeq | hyneg
            · have hysum : input.q.y + input.p.y ≠ 0 := by
                rw [hyeq]
                exact pallas_add_self_ne_zero
                  (Point.y_ne_zero_of_isPointOrIdentity_of_x_ne_zero hp hpx)
              have hcontra :
                    ((input.q.x - input.p.x) * (input.q.x - input.p.x)⁻¹ +
                      if input.q.x = input.p.x then
                        (input.q.y + input.p.y) * (input.q.y + input.p.y)⁻¹
                      else 0) = 1 := by
                simp [hx, hysum]
              exact False.elim (hflag hcontra)
            · exact False.elim (hy hyneg)
        · have hcontra :
              ((input.q.x - input.p.x) * (input.q.x - input.p.x)⁻¹ +
                if input.q.x = input.p.x then
                  (input.q.y + input.p.y) * (input.q.y + input.p.y)⁻¹
                else 0) = 1 := by
            simp [hx]
            field_simp [sub_ne_zero.mpr hx]
          exact False.elim (hflag hcontra)

theorem spec_eq_outputValue_pallas {row : CompleteAddRow Fp}
    (hp : Point.isPointOrIdentity row.p) (hq : Point.isPointOrIdentity row.q) (hrow : Spec row) :
    row.r = outputValue ({ p := row.p, q := row.q } : Input Fp) := by
  rcases hrow with ⟨hSlope, hTangent, hNonexceptionalDiff, hNonexceptionalSum,
    hLeftIdentity, hRightIdentity, hInverse⟩
  by_cases hpx : row.p.x = 0
  · have hflag : ifBeta row ≠ 1 := by
      unfold ifBeta
      rw [hpx]
      simp
    have hr := hLeftIdentity hflag
    unfold leftIdentityResult at hr
    unfold outputValue
    simp [hpx, hr]
  · by_cases hqx : row.q.x = 0
    · have hflag : ifGamma row ≠ 1 := by
        unfold ifGamma
        rw [hqx]
        simp
      have hr := hRightIdentity hflag
      unfold rightIdentityResult at hr
      unfold outputValue
      simp [hpx, hqx, hr]
    · by_cases hinv : row.q.x = row.p.x ∧ row.q.y = -row.p.y
      · have hflag : ifAlpha row + ifDelta row ≠ 1 := by
          rcases hinv with ⟨hx, hy⟩
          unfold ifAlpha ifDelta xQMinusXP yQPlusYP
          simp [hx, hy]
        have hr := hInverse hflag
        unfold inverseResult at hr
        have hr0 : row.r = ({ x := 0, y := 0 } : Point Fp) := by
          rw [Point.mk.injEq]
          exact hr
        unfold outputValue
        simp [hpx, hinv, hr0]
      · have hr : nonexceptionalResult row := by
          by_cases hx : row.q.x = row.p.x
          · have hsame := pallas_y_eq_or_neg_of_same_x hp hq hpx hqx hx
            rcases hsame with hy | hy
            · have hysum : yQPlusYP row ≠ 0 := by
                unfold yQPlusYP
                rw [hy]
                exact pallas_add_self_ne_zero
                  (Point.y_ne_zero_of_isPointOrIdentity_of_x_ne_zero hp hpx)
              have hprod : row.p.x * row.q.x * yQPlusYP row ≠ 0 := by
                exact mul_ne_zero (mul_ne_zero hpx hqx) hysum
              exact hNonexceptionalSum hprod
            · exact False.elim (hinv ⟨hx, hy⟩)
          · have hxdiff : xQMinusXP row ≠ 0 := by
              unfold xQMinusXP
              intro hzero
              exact hx (sub_eq_zero.mp hzero)
            have hprod : row.p.x * row.q.x * xQMinusXP row ≠ 0 := by
              exact mul_ne_zero (mul_ne_zero hpx hqx) hxdiff
            exact hNonexceptionalDiff hprod
        have hlambda :
            row.lambda = lambdaValue ({ p := row.p, q := row.q } : Input Fp) := by
          by_cases hx : row.q.x = row.p.x
          · have hpy : row.p.y ≠ 0 :=
              Point.y_ne_zero_of_isPointOrIdentity_of_x_ne_zero hp hpx
            have hflag : ifAlpha row ≠ 1 := by
              unfold ifAlpha xQMinusXP
              simp [hx]
            have htangent := hTangent hflag
            unfold tangentLine at htangent
            unfold lambdaValue
            simp [hx, hpy]
            have hden : (2 : Fp) * row.p.y ≠ 0 :=
              mul_ne_zero pallas_two_ne_zero hpy
            field_simp [hden, pallas_two_ne_zero]
            linear_combination htangent
          · have hxdiff : xQMinusXP row ≠ 0 := by
              unfold xQMinusXP
              intro hzero
              exact hx (sub_eq_zero.mp hzero)
            have hslope := hSlope hxdiff
            unfold slopeLine xQMinusXP at hslope hxdiff
            unfold lambdaValue
            simp [hx]
            field_simp [hxdiff]
            linear_combination hslope
        unfold nonexceptionalResult at hr
        rw [hlambda] at hr
        unfold xPMinusXR at hr
        unfold outputValue
        simp [hpx, hqx, hinv]
        rw [Point.mk.injEq]
        constructor
        · exact hr.1
        · rw [← hr.1]
          exact hr.2

theorem spec_eq_swAdd_pallas {row : CompleteAddRow Fp}
    (hp : Point.isPointOrIdentity row.p) (hq : Point.isPointOrIdentity row.q) (hrow : Spec row) :
    Point.coords row.r =
      CompElliptic.CurveForms.ShortWeierstrass.add
        (0 : Fp) (Point.coords row.p) (Point.coords row.q) := by
  rw [spec_eq_outputValue_pallas hp hq hrow]
  exact outputValue_eq_swAdd_pallas hp hq

def main (input : Var Input Fp) :
    Circuit Fp (Var Point Fp) := do
  let xR ← witnessField fun env =>
    (rowValue ({ p := eval env input.p, q := eval env input.q } : Input Fp)).r.x
  let yR ← witnessField fun env =>
    (rowValue ({ p := eval env input.p, q := eval env input.q } : Input Fp)).r.y
  let lambda ← witnessField fun env =>
    (rowValue ({ p := eval env input.p, q := eval env input.q } : Input Fp)).lambda
  let alpha ← witnessField fun env =>
    (rowValue ({ p := eval env input.p, q := eval env input.q } : Input Fp)).alpha
  let beta ← witnessField fun env =>
    (rowValue ({ p := eval env input.p, q := eval env input.q } : Input Fp)).beta
  let gamma ← witnessField fun env =>
    (rowValue ({ p := eval env input.p, q := eval env input.q } : Input Fp)).gamma
  let delta ← witnessField fun env =>
    (rowValue ({ p := eval env input.p, q := eval env input.q } : Input Fp)).delta
  let row : Var CompleteAddRow Fp := {
    p := input.p
    q := input.q
    r := { x := xR, y := yR }
    lambda
    alpha
    beta
    gamma
    delta
  }
  Gate.circuit row
  return row.r

def Assumptions (input : Input Fp) : Prop :=
  Point.isPointOrIdentity input.p ∧ Point.isPointOrIdentity input.q

def Spec (input : Input Fp) (output : Point Fp) : Prop :=
  Point.coords output =
    CompElliptic.CurveForms.ShortWeierstrass.add
      (0 : Fp) (Point.coords input.p) (Point.coords input.q)

instance elaborated : ElaboratedCircuit Fp Input Point main := by
  elaborate_circuit

theorem soundness : Soundness Fp main Assumptions Spec := by
  circuit_proof_start [main, Assumptions, Spec, Point.isPointOrIdentity,
    Gate.circuit, Gate.Spec, spec_eq_swAdd_pallas]
  rcases h_assumptions with ⟨hp, hq⟩
  let row : CompleteAddRow Fp := {
    p := input_p
    q := input_q
    r := { x := env.get i₀, y := env.get (i₀ + 1) }
    lambda := env.get (i₀ + 1 + 1)
    alpha := env.get (i₀ + 1 + 1 + 1)
    beta := env.get (i₀ + 1 + 1 + 1 + 1)
    gamma := env.get (i₀ + 1 + 1 + 1 + 1 + 1)
    delta := env.get (i₀ + 1 + 1 + 1 + 1 + 1 + 1)
  }
  exact spec_eq_swAdd_pallas (row := row) hp hq h_holds

theorem completeness : Completeness Fp main Assumptions := by
  circuit_proof_start [main, Assumptions, Spec, Point.isPointOrIdentity,
    Gate.circuit, Gate.Spec, rowValue_spec_pallas]
  rcases h_assumptions with ⟨hp, hq⟩
  let row : CompleteAddRow Fp := {
    p := input_p
    q := input_q
    r := { x := env.get i₀, y := env.get (i₀ + 1) }
    lambda := env.get (i₀ + 1 + 1)
    alpha := env.get (i₀ + 1 + 1 + 1)
    beta := env.get (i₀ + 1 + 1 + 1 + 1)
    gamma := env.get (i₀ + 1 + 1 + 1 + 1 + 1)
    delta := env.get (i₀ + 1 + 1 + 1 + 1 + 1 + 1)
  }
  let expected := rowValue ({ p := input_p, q := input_q } : Input Fp)
  have hrowEq : row = expected := by
    dsimp [row, expected]
    rcases h_env with ⟨hx, hy, hlambda, halpha, hbeta, hgamma, hdelta⟩
    rw [hx, hy, hlambda, halpha, hbeta, hgamma, hdelta]
    rfl
  change Gate.Spec row
  rw [hrowEq]
  exact rowValue_spec_pallas (input := { p := input_p, q := input_q }) hp hq

def circuit : FormalCircuit Fp Input Point where
  main
  elaborated
  Assumptions
  Spec
  soundness
  completeness

end EntryPoint

end CompleteAdd

end Ecc
end Orchard
