import Clean.Circuit
import Clean.Utils.Tactics

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
`x_p = x_q`. This Clean approximation exposes the nonzero-denominator requirement as an
assumption and models the two custom-gate polynomial constraints directly.
-/

structure AddInputs (F : Type) where
  p : Point F
  q : Point F
deriving ProvableStruct

namespace IncompleteAdd

def lambda (input : AddInputs F) : F :=
  (input.q.y - input.p.y) * (input.q.x - input.p.x)⁻¹

def outputValue (input : AddInputs F) : Point F :=
  let slope := lambda input
  let xR := slope * slope - input.p.x - input.q.x
  let yR := slope * (input.p.x - xR) - input.p.y
  { x := xR, y := yR }

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
  input.p.x ≠ input.q.x

def Spec (input : AddInputs F) (output : Point F) : Prop :=
  constraints input output

instance elaborated : ElaboratedCircuit F AddInputs Point main := by
  elaborate_circuit

theorem outputValue_constraints {input : AddInputs F} (hx : input.p.x ≠ input.q.x) :
    constraints input (outputValue input) := by
  unfold constraints poly1 poly2 outputValue lambda
  have hden : input.q.x - input.p.x ≠ 0 := by
    intro h
    apply hx
    exact (sub_eq_zero.mp h).symm
  constructor <;> field_simp [hden] <;> ring

theorem soundness : Soundness F main Assumptions Spec := by
  circuit_proof_start [main, Assumptions, Spec, constraints, poly1, poly2]
  rcases input_p with ⟨px, py⟩
  rcases input_q with ⟨qx, qy⟩
  simp_all [sub_eq_add_neg]

theorem completeness : Completeness F main Assumptions := by
  circuit_proof_start [main, Assumptions, outputValue, lambda, constraints, poly1, poly2]
  have hc := outputValue_constraints (input := { p := input_p, q := input_q }) h_assumptions
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

end Ecc
end Orchard
