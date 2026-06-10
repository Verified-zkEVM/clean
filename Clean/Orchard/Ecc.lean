import Clean.Circuit
import Clean.Orchard.Specs.Elliptic.Curves.Pasta
import Clean.Orchard.Specs.Elliptic.CurveForms.ShortWeierstrass
import Clean.Utils.Tactics
import Mathlib.Tactic

/-!
# Orchard ECC gadgets

Clean approximations of the Orchard/Pallas ECC gates.

Reference for the first gadgets:
`halo2@halo2_gadgets-0.5.0/halo2_gadgets/src/ecc/chip/witness_point.rs`
- `witness point`
- `witness non-identity point`

These gadgets model the arithmetic constraints, not the Halo2 selectors, regions, or copy
constraints.
-/

namespace Orchard
namespace Ecc

variable {F : Type} [Field F]

abbrev PallasBaseField := CompElliptic.Fields.Pasta.PallasBaseField

def pallasB : F := 5

structure Point (F : Type) where
  x : F
  y : F

instance : ProvableType Point where
  size := 2
  toElements point := #v[point.x, point.y]
  fromElements elems := {
    x := elems[0]
    y := elems[1]
  }

@[circuit_norm]
theorem eval_point (env : Environment F) (point : Point (Expression F)) :
    eval env point = ({ x := env point.x, y := env point.y } : Point F) := by
  with_unfolding_all rfl

def curveEquation (point : Point F) : F :=
  point.y * point.y - point.x * point.x * point.x - pallasB

def onCurve (point : Point F) : Prop :=
  curveEquation point = 0

def isIdentityEncoding (point : Point F) : Prop :=
  point.x = 0 ∧ point.y = 0

def isPointOrIdentity (point : Point F) : Prop :=
  isIdentityEncoding point ∨ onCurve point

def NoCurvePointWithXZero : Prop :=
  ∀ y : F, ¬ onCurve ({ x := 0, y } : Point F)

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

def pointCoords (point : Point F) : F × F :=
  (point.x, point.y)

namespace PointOrIdentity

def main (point : Var Point F) : Circuit F Unit := do
  let equation := point.y * point.y - point.x * point.x * point.x - (pallasB : F)
  assertZero (point.x * equation)
  assertZero (point.y * equation)

def circuit : FormalAssertion F Point where
  main
  Spec := isPointOrIdentity
  soundness := by
    circuit_proof_start [main, isPointOrIdentity, isIdentityEncoding, onCurve, curveEquation, pallasB]
    rw [← h_input]
    by_cases hx : Expression.eval env input_var.x = 0
    · by_cases hy : Expression.eval env input_var.y = 0
      · exact Or.inl ⟨hx, hy⟩
      · right
        have hy_mul :
            Expression.eval env input_var.y *
              (Expression.eval env input_var.y * Expression.eval env input_var.y -
                Expression.eval env input_var.x * Expression.eval env input_var.x *
                  Expression.eval env input_var.x - (5 : F)) = 0 := by
          simpa [sub_eq_add_neg] using h_holds.2
        exact (mul_eq_zero.mp hy_mul).resolve_left hy
    · right
      have hx_mul :
          Expression.eval env input_var.x *
            (Expression.eval env input_var.y * Expression.eval env input_var.y -
              Expression.eval env input_var.x * Expression.eval env input_var.x *
                Expression.eval env input_var.x - (5 : F)) = 0 := by
        simpa [sub_eq_add_neg] using h_holds.1
      exact (mul_eq_zero.mp hx_mul).resolve_left hx
  completeness := by
    circuit_proof_start [main, isPointOrIdentity, isIdentityEncoding, onCurve, curveEquation, pallasB]
    rw [← h_input] at h_spec
    rcases h_spec with h_identity | h_onCurve
    · rcases h_identity with ⟨hx, hy⟩
      constructor
      · rw [show Expression.eval env.toEnvironment input_var.x = 0 by simpa using hx]
        simp
      · rw [show Expression.eval env.toEnvironment input_var.y = 0 by simpa using hy]
        simp
    · have h_eq :
          Expression.eval env.toEnvironment input_var.y * Expression.eval env.toEnvironment input_var.y +
                -(Expression.eval env.toEnvironment input_var.x *
                  Expression.eval env.toEnvironment input_var.x *
                  Expression.eval env.toEnvironment input_var.x) +
              -5 =
            0 := by
        simpa [sub_eq_add_neg] using h_onCurve
      constructor <;> simp [h_eq]

end PointOrIdentity

namespace NonIdentityPoint

def main (point : Var Point F) : Circuit F Unit := do
  assertZero (point.y * point.y - point.x * point.x * point.x - (pallasB : F))

def circuit : FormalAssertion F Point where
  main
  Spec := onCurve
  soundness := by
    circuit_proof_start [main, onCurve, curveEquation, pallasB]
    rw [← h_input]
    simpa only [eval_point, onCurve, curveEquation, pallasB,
      sub_eq_add_neg] using h_holds
  completeness := by
    circuit_proof_start [main, onCurve, curveEquation, pallasB]
    rw [← h_input] at h_spec
    simpa only [eval_point, onCurve, curveEquation, pallasB,
      sub_eq_add_neg] using h_spec

end NonIdentityPoint

/-!
Reference:
`halo2@halo2_gadgets-0.5.0/halo2_gadgets/src/ecc/chip/add_incomplete.rs`
- `incomplete addition`

The Rust assignment rejects exceptional cases where either input is encoded identity or
`x_p = x_q`. This Clean approximation exposes those rejection cases as assumptions and
specifies the output as short-Weierstrass addition.
-/

structure AddInputs (F : Type) where
  p : Point F
  q : Point F
deriving ProvableStruct

namespace IncompleteAdd

variable [DecidableEq F]

def lambda (input : AddInputs F) : F :=
  (input.q.y - input.p.y) * (input.q.x - input.p.x)⁻¹

def outputValue (input : AddInputs F) : Point F :=
  let slope := lambda input
  let xR := slope * slope - input.p.x - input.q.x
  let yR := slope * (input.p.x - xR) - input.p.y
  { x := xR, y := yR }

theorem outputValue_eq_swAdd {input : AddInputs F}
    (hp : ¬ isIdentityEncoding input.p) (hq : ¬ isIdentityEncoding input.q)
    (hx : input.p.x ≠ input.q.x) :
    pointCoords (outputValue input) =
      CompElliptic.CurveForms.ShortWeierstrass.add
        (0 : F) (pointCoords input.p) (pointCoords input.q) := by
  rcases input with ⟨⟨px, py⟩, ⟨qx, qy⟩⟩
  unfold pointCoords outputValue lambda CompElliptic.CurveForms.ShortWeierstrass.add
  unfold isIdentityEncoding at hp hq
  simp only
  have hp0 : ¬(px, py) = (0, 0) := by
    intro h
    apply hp
    exact Prod.ext_iff.mp h
  have hq0 : ¬(qx, qy) = (0, 0) := by
    intro h
    apply hq
    exact Prod.ext_iff.mp h
  rw [if_neg hp0, if_neg hq0]
  have hx' : ¬ px = qx := hx
  rw [if_neg hx']
  rw [Prod.mk.injEq]
  constructor <;> ring

def poly1 (input : AddInputs F) (output : Point F) : F :=
  (output.x + input.q.x + input.p.x) *
      (input.p.x - input.q.x) *
      (input.p.x - input.q.x) -
    (input.p.y - input.q.y) * (input.p.y - input.q.y)

def poly2 (input : AddInputs F) (output : Point F) : F :=
  (output.y + input.q.y) * (input.p.x - input.q.x) -
    (input.p.y - input.q.y) * (input.q.x - output.x)

def constraints (input : AddInputs F) (output : Point F) : Prop :=
  poly1 input output = 0 ∧ poly2 input output = 0

def main (input : Var AddInputs F) : Circuit F (Var Point F) := do
  let xR ← witnessField fun env =>
    let slope := (env input.q.y - env input.p.y) * (env input.q.x - env input.p.x)⁻¹
    slope * slope - env input.p.x - env input.q.x
  let yR ← witnessField fun env =>
    let slope := (env input.q.y - env input.p.y) * (env input.q.x - env input.p.x)⁻¹
    let xR := slope * slope - env input.p.x - env input.q.x
    slope * (env input.p.x - xR) - env input.p.y
  assertZero ((xR + input.q.x + input.p.x) *
    (input.p.x - input.q.x) * (input.p.x - input.q.x) -
    (input.p.y - input.q.y) * (input.p.y - input.q.y))
  assertZero ((yR + input.q.y) * (input.p.x - input.q.x) -
    (input.p.y - input.q.y) * (input.q.x - xR))
  return { x := xR, y := yR }

def Assumptions (input : AddInputs F) : Prop :=
  ¬ isIdentityEncoding input.p ∧
    ¬ isIdentityEncoding input.q ∧
    input.p.x ≠ input.q.x

def Spec (input : AddInputs F) (output : Point F) : Prop :=
  pointCoords output =
    CompElliptic.CurveForms.ShortWeierstrass.add
      (0 : F) (pointCoords input.p) (pointCoords input.q)

instance elaborated : ElaboratedCircuit F AddInputs Point main := by
  elaborate_circuit

omit [DecidableEq F] in
theorem outputValue_constraints {input : AddInputs F} (hx : input.p.x ≠ input.q.x) :
    constraints input (outputValue input) := by
  unfold constraints poly1 poly2 outputValue lambda
  have hden : input.q.x - input.p.x ≠ 0 := by
    intro h
    apply hx
    exact (sub_eq_zero.mp h).symm
  constructor <;> field_simp [hden] <;> ring

omit [DecidableEq F] in
theorem constraints_eq_outputValue {input : AddInputs F} {output : Point F}
    (hx : input.p.x ≠ input.q.x) (h : constraints input output) :
    output = outputValue input := by
  rcases input with ⟨⟨px, py⟩, ⟨qx, qy⟩⟩
  rcases output with ⟨rx, ry⟩
  unfold constraints poly1 poly2 at h
  unfold outputValue lambda
  have hden : qx - px ≠ 0 := by
    intro hden
    apply hx
    exact (sub_eq_zero.mp hden).symm
  have hden' : px - qx ≠ 0 := by
    intro hden'
    apply hx
    exact sub_eq_zero.mp hden'
  rcases h with ⟨h1, h2⟩
  simp at h1 h2
  rw [Point.mk.injEq]
  simp
  have hxout :
      rx = (qy - py) * (qx - px)⁻¹ * ((qy - py) * (qx - px)⁻¹) - px - qx := by
    apply sub_eq_zero.mp
    field_simp [hden, hden']
    ring_nf at h1 ⊢
    exact h1
  constructor
  · exact hxout
  · rw [← hxout]
    apply sub_eq_zero.mp
    field_simp [hden, hden']
    ring_nf at h2 ⊢
    have h2neg := congrArg Neg.neg h2
    ring_nf at h2neg
    ring_nf
    exact h2neg

theorem soundness : Soundness F main Assumptions Spec := by
  circuit_proof_start [main, Assumptions, Spec, constraints, poly1, poly2]
  rcases input_p with ⟨px, py⟩
  rcases input_q with ⟨qx, qy⟩
  have hc : constraints { p := { x := px, y := py }, q := { x := qx, y := qy } }
      { x := env.get i₀, y := env.get (i₀ + 1) } := by
    simp_all [constraints, poly1, poly2, sub_eq_add_neg]
  have hout := constraints_eq_outputValue h_assumptions.2.2 hc
  rw [hout]
  exact outputValue_eq_swAdd h_assumptions.1 h_assumptions.2.1 h_assumptions.2.2

omit [DecidableEq F] in
theorem completeness : Completeness F main Assumptions := by
  circuit_proof_start [main, Assumptions, outputValue, lambda, constraints, poly1, poly2]
  have hc := outputValue_constraints (input := { p := input_p, q := input_q }) h_assumptions.2.2
  rcases input_p with ⟨px, py⟩
  rcases input_q with ⟨qx, qy⟩
  simp_all [outputValue, lambda, constraints, poly1, poly2, sub_eq_add_neg]

def circuit : FormalCircuit F AddInputs Point where
  main
  elaborated
  Assumptions
  Spec
  soundness
  completeness

end IncompleteAdd

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

variable {R : Type} [Zero R] [One R] [Add R] [Sub R] [Mul R] [OfNat R 2] [OfNat R 3]

section ValueModel

variable [DecidableEq F]

/-- The semantic side condition needed by Halo2's complete-add assignment logic.

The Rust implementation treats `x = 0` as the identity branch. This is sound for the
Pallas encoding because `(0, y)` is not a non-identity curve point. We keep that property
explicit here instead of baking it into the row constraints. -/
def XZeroImpliesIdentity (point : Point F) : Prop :=
  point.x = 0 → point.y = 0

def lambdaValue (input : AddInputs F) : F :=
  if input.q.x = input.p.x then
    if input.p.y ≠ 0 then
      (3 * input.p.x * input.p.x) * (2 * input.p.y)⁻¹
    else
      0
  else
    (input.q.y - input.p.y) * (input.q.x - input.p.x)⁻¹

def outputValue (input : AddInputs F) : Point F :=
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

def rowValue (input : AddInputs F) : CompleteAddRow F where
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

theorem outputValue_eq_swAdd {input : AddInputs F}
    (hpZero : XZeroImpliesIdentity input.p)
    (hqZero : XZeroImpliesIdentity input.q) :
    pointCoords (outputValue input) =
      CompElliptic.CurveForms.ShortWeierstrass.add
        (0 : F) (pointCoords input.p) (pointCoords input.q) := by
  rcases input with ⟨⟨px, py⟩, ⟨qx, qy⟩⟩
  unfold pointCoords outputValue lambdaValue
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

theorem outputValue_eq_swAdd_of_pointOrIdentity {input : AddInputs F}
    (hNoXZero : NoCurvePointWithXZero (F := F))
    (hp : isPointOrIdentity input.p)
    (hq : isPointOrIdentity input.q) :
    pointCoords (outputValue input) =
      CompElliptic.CurveForms.ShortWeierstrass.add
        (0 : F) (pointCoords input.p) (pointCoords input.q) :=
  outputValue_eq_swAdd
    (xZeroImpliesIdentity_of_pointOrIdentity hNoXZero hp)
    (xZeroImpliesIdentity_of_pointOrIdentity hNoXZero hq)

theorem outputValue_eq_swAdd_pallas {input : AddInputs PallasBaseField}
    (hp : isPointOrIdentity input.p)
    (hq : isPointOrIdentity input.q) :
    pointCoords (outputValue input) =
      CompElliptic.CurveForms.ShortWeierstrass.add
        (0 : PallasBaseField) (pointCoords input.p) (pointCoords input.q) :=
  outputValue_eq_swAdd_of_pointOrIdentity pallasNoCurvePointWithXZero hp hq

theorem pallas_two_ne_zero : (2 : PallasBaseField) ≠ 0 := by
  decide

theorem pallas_add_self_ne_zero {y : PallasBaseField} (hy : y ≠ 0) :
    y + y ≠ 0 := by
  intro h
  have hmul : (2 : PallasBaseField) * y = 0 := by
    linear_combination h
  exact hy ((mul_eq_zero.mp hmul).resolve_left pallas_two_ne_zero)

theorem pallas_y_eq_or_neg_of_same_x {p q : Point PallasBaseField}
    (hp : isPointOrIdentity p) (hq : isPointOrIdentity q)
    (hpx : p.x ≠ 0) (hqx : q.x ≠ 0) (hx : q.x = p.x) :
    q.y = p.y ∨ q.y = -p.y := by
  have hpCurve : onCurve p := by
    rcases hp with hId | hCurve
    · exact False.elim (hpx hId.1)
    · exact hCurve
  have hqCurve : onCurve q := by
    rcases hq with hId | hCurve
    · exact False.elim (hqx hId.1)
    · exact hCurve
  unfold onCurve curveEquation pallasB at hpCurve hqCurve
  have hsquare : (q.y - p.y) * (q.y + p.y) = 0 := by
    rw [hx] at hqCurve
    linear_combination hqCurve - hpCurve
  rcases mul_eq_zero.mp hsquare with h | h
  · left
    exact sub_eq_zero.mp h
  · right
    linear_combination h

end ValueModel

def xQMinusXP (row : CompleteAddRow R) : R :=
  row.q.x - row.p.x

def xPMinusXR (row : CompleteAddRow R) : R :=
  row.p.x - row.r.x

def yQPlusYP (row : CompleteAddRow R) : R :=
  row.q.y + row.p.y

def ifAlpha (row : CompleteAddRow R) : R :=
  xQMinusXP row * row.alpha

def ifBeta (row : CompleteAddRow R) : R :=
  row.p.x * row.beta

def ifGamma (row : CompleteAddRow R) : R :=
  row.q.x * row.gamma

def ifDelta (row : CompleteAddRow R) : R :=
  yQPlusYP row * row.delta

def nonexceptionalXR (row : CompleteAddRow R) : R :=
  row.lambda * row.lambda - row.p.x - row.q.x - row.r.x

def nonexceptionalYR (row : CompleteAddRow R) : R :=
  row.lambda * xPMinusXR row - row.p.y - row.r.y

def poly1 (row : CompleteAddRow R) : R :=
  let incomplete := xQMinusXP row * row.lambda - (row.q.y - row.p.y)
  xQMinusXP row * incomplete

def poly2 (row : CompleteAddRow R) : R :=
  (1 - ifAlpha row) * (2 * row.p.y * row.lambda - 3 * row.p.x * row.p.x)

def poly3a (row : CompleteAddRow R) : R :=
  row.p.x * row.q.x * xQMinusXP row * nonexceptionalXR row

def poly3b (row : CompleteAddRow R) : R :=
  row.p.x * row.q.x * xQMinusXP row * nonexceptionalYR row

def poly3c (row : CompleteAddRow R) : R :=
  row.p.x * row.q.x * yQPlusYP row * nonexceptionalXR row

def poly3d (row : CompleteAddRow R) : R :=
  row.p.x * row.q.x * yQPlusYP row * nonexceptionalYR row

def poly4a (row : CompleteAddRow R) : R :=
  (1 - ifBeta row) * (row.r.x - row.q.x)

def poly4b (row : CompleteAddRow R) : R :=
  (1 - ifBeta row) * (row.r.y - row.q.y)

def poly5a (row : CompleteAddRow R) : R :=
  (1 - ifGamma row) * (row.r.x - row.p.x)

def poly5b (row : CompleteAddRow R) : R :=
  (1 - ifGamma row) * (row.r.y - row.p.y)

def poly6a (row : CompleteAddRow R) : R :=
  (1 - ifAlpha row - ifDelta row) * row.r.x

def poly6b (row : CompleteAddRow R) : R :=
  (1 - ifAlpha row - ifDelta row) * row.r.y

def constraints (row : CompleteAddRow R) : Prop :=
  poly1 row = 0 ∧
  poly2 row = 0 ∧
  poly3a row = 0 ∧
  poly3b row = 0 ∧
  poly3c row = 0 ∧
  poly3d row = 0 ∧
  poly4a row = 0 ∧
  poly4b row = 0 ∧
  poly5a row = 0 ∧
  poly5b row = 0 ∧
  poly6a row = 0 ∧
  poly6b row = 0

def slopeLine (row : CompleteAddRow R) : Prop :=
  xQMinusXP row * row.lambda = row.q.y - row.p.y

def tangentLine (row : CompleteAddRow R) : Prop :=
  2 * row.p.y * row.lambda = 3 * row.p.x * row.p.x

def nonexceptionalResult (row : CompleteAddRow R) : Prop :=
  row.r.x = row.lambda * row.lambda - row.p.x - row.q.x ∧
    row.r.y = row.lambda * xPMinusXR row - row.p.y

def leftIdentityResult (row : CompleteAddRow R) : Prop :=
  row.r = row.q

def rightIdentityResult (row : CompleteAddRow R) : Prop :=
  row.r = row.p

def inverseResult (row : CompleteAddRow R) : Prop :=
  row.r.x = 0 ∧ row.r.y = 0

def Spec (row : CompleteAddRow R) : Prop :=
  (xQMinusXP row ≠ 0 → slopeLine row) ∧
    (ifAlpha row ≠ 1 → tangentLine row) ∧
    (row.p.x * row.q.x * xQMinusXP row ≠ 0 → nonexceptionalResult row) ∧
    (row.p.x * row.q.x * yQPlusYP row ≠ 0 → nonexceptionalResult row) ∧
    (ifBeta row ≠ 1 → leftIdentityResult row) ∧
    (ifGamma row ≠ 1 → rightIdentityResult row) ∧
    (ifAlpha row + ifDelta row ≠ 1 → inverseResult row)

def main (row : Var CompleteAddRow F) : Circuit F Unit := do
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

def circuit : FormalAssertion F CompleteAddRow where
  main
  Spec := Spec
  soundness := by
    circuit_proof_start [main, Spec, constraints, slopeLine, tangentLine, nonexceptionalResult,
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
    circuit_proof_start [main, Spec, constraints, slopeLine, tangentLine, nonexceptionalResult,
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

section EntryPoint

theorem rowValue_spec_pallas {input : AddInputs PallasBaseField}
    (hp : isPointOrIdentity input.p) (hq : isPointOrIdentity input.q) :
    Spec (rowValue input) := by
  sorry

theorem spec_eq_swAdd_pallas {row : CompleteAddRow PallasBaseField}
    (hp : isPointOrIdentity row.p) (hq : isPointOrIdentity row.q) (hrow : Spec row) :
    pointCoords row.r =
      CompElliptic.CurveForms.ShortWeierstrass.add
        (0 : PallasBaseField) (pointCoords row.p) (pointCoords row.q) := by
  sorry

namespace Entry

def main (input : Var AddInputs PallasBaseField) :
    Circuit PallasBaseField (Var Point PallasBaseField) := do
  PointOrIdentity.circuit input.p
  PointOrIdentity.circuit input.q
  let xR ← witnessField fun env =>
    (rowValue ({ p := eval env input.p, q := eval env input.q } : AddInputs PallasBaseField)).r.x
  let yR ← witnessField fun env =>
    (rowValue ({ p := eval env input.p, q := eval env input.q } : AddInputs PallasBaseField)).r.y
  let lambda ← witnessField fun env =>
    (rowValue ({ p := eval env input.p, q := eval env input.q } : AddInputs PallasBaseField)).lambda
  let alpha ← witnessField fun env =>
    (rowValue ({ p := eval env input.p, q := eval env input.q } : AddInputs PallasBaseField)).alpha
  let beta ← witnessField fun env =>
    (rowValue ({ p := eval env input.p, q := eval env input.q } : AddInputs PallasBaseField)).beta
  let gamma ← witnessField fun env =>
    (rowValue ({ p := eval env input.p, q := eval env input.q } : AddInputs PallasBaseField)).gamma
  let delta ← witnessField fun env =>
    (rowValue ({ p := eval env input.p, q := eval env input.q } : AddInputs PallasBaseField)).delta
  let row : Var CompleteAddRow PallasBaseField := {
    p := input.p
    q := input.q
    r := { x := xR, y := yR }
    lambda
    alpha
    beta
    gamma
    delta
  }
  CompleteAdd.circuit row
  return row.r

def Assumptions (input : AddInputs PallasBaseField) : Prop :=
  isPointOrIdentity input.p ∧ isPointOrIdentity input.q

def Spec (input : AddInputs PallasBaseField) (output : Point PallasBaseField) : Prop :=
  pointCoords output =
    CompElliptic.CurveForms.ShortWeierstrass.add
      (0 : PallasBaseField) (pointCoords input.p) (pointCoords input.q)

instance elaborated : ElaboratedCircuit PallasBaseField AddInputs Point main := by
  elaborate_circuit

theorem soundness : Soundness PallasBaseField main Assumptions Spec := by
  circuit_proof_start [main, Assumptions, Spec, PointOrIdentity.circuit,
    isPointOrIdentity, CompleteAdd.circuit, CompleteAdd.Spec, spec_eq_swAdd_pallas]
  rcases h_holds with ⟨hp, hq, hrow⟩
  let row : CompleteAddRow PallasBaseField := {
    p := input_p
    q := input_q
    r := { x := env.get i₀, y := env.get (i₀ + 1) }
    lambda := env.get (i₀ + 1 + 1)
    alpha := env.get (i₀ + 1 + 1 + 1)
    beta := env.get (i₀ + 1 + 1 + 1 + 1)
    gamma := env.get (i₀ + 1 + 1 + 1 + 1 + 1)
    delta := env.get (i₀ + 1 + 1 + 1 + 1 + 1 + 1)
  }
  exact spec_eq_swAdd_pallas (row := row) hp hq hrow

theorem completeness : Completeness PallasBaseField main Assumptions := by
  circuit_proof_start [main, Assumptions, Spec, PointOrIdentity.circuit,
    isPointOrIdentity, CompleteAdd.circuit, CompleteAdd.Spec, rowValue_spec_pallas]
  rcases h_assumptions with ⟨hp, hq⟩
  refine ⟨hp, hq, ?_⟩
  let row : CompleteAddRow PallasBaseField := {
    p := input_p
    q := input_q
    r := { x := env.get i₀, y := env.get (i₀ + 1) }
    lambda := env.get (i₀ + 1 + 1)
    alpha := env.get (i₀ + 1 + 1 + 1)
    beta := env.get (i₀ + 1 + 1 + 1 + 1)
    gamma := env.get (i₀ + 1 + 1 + 1 + 1 + 1)
    delta := env.get (i₀ + 1 + 1 + 1 + 1 + 1 + 1)
  }
  let expected := rowValue ({ p := input_p, q := input_q } : AddInputs PallasBaseField)
  have hrowEq : row = expected := by
    dsimp [row, expected]
    rcases h_env with ⟨hx, hy, hlambda, halpha, hbeta, hgamma, hdelta⟩
    rw [hx, hy, hlambda, halpha, hbeta, hgamma, hdelta]
    rfl
  change CompleteAdd.Spec row
  rw [hrowEq]
  exact rowValue_spec_pallas (input := { p := input_p, q := input_q }) hp hq

def circuit : FormalCircuit PallasBaseField AddInputs Point where
  main
  elaborated
  Assumptions
  Spec
  soundness
  completeness

end Entry

end EntryPoint

end CompleteAdd

end Ecc
end Orchard
