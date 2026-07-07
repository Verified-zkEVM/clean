import Clean.Orchard.Specs.Pallas
import Clean.Orchard.Ecc.Defs
import Clean.Utils.Tactics
import Mathlib.Tactic

namespace Orchard
namespace Ecc

-- open CompElliptic.Curves.Pasta

/-!
Reference:
`halo2@halo2_gadgets-0.5.0/halo2_gadgets/src/ecc/chip/witness_point.rs`
- `witness point`
- `witness non-identity point`
-/

namespace WitnessPoint

namespace Gate

def main (point : Var Point Fp) : Circuit Fp Unit := do
  let equation := point.y * point.y - point.x * point.x * point.x - pallasB
  assertZero (point.x * equation)
  assertZero (point.y * equation)

def circuit : FormalAssertion Fp Point where
  name := "GATE witness point"
  main
  Spec point := point.Valid
  soundness := by
    circuit_proof_start [main, Point.Valid, Point.OnCurve, Point.zero, Point.coords, pallasB,
      CompElliptic.CurveForms.ShortWeierstrass.Valid,
      CompElliptic.CurveForms.ShortWeierstrass.OnCurve]
    rw [← h_input]
    set x := Expression.eval env input_var.x
    set y := Expression.eval env input_var.y
    by_cases hx : x = 0
    · by_cases hy : y = 0
      · exact Or.inr (by rw [hx, hy]; rfl)
      · left
        have hy_mul : y * (y * y - x * x * x - (5 : Fp)) = 0 := by
          simpa [sub_eq_add_neg] using h_holds.2
        have h_eq := (mul_eq_zero.mp hy_mul).resolve_left hy
        linear_combination h_eq
    · left
      have hx_mul : x * (y * y - x * x * x - (5 : Fp)) = 0 := by
        simpa [sub_eq_add_neg] using h_holds.1
      have h_eq := (mul_eq_zero.mp hx_mul).resolve_left hx
      linear_combination h_eq
  completeness := by
    circuit_proof_start [main, Point.Valid, Point.OnCurve, Point.zero, Point.coords, pallasB,
      CompElliptic.CurveForms.ShortWeierstrass.Valid,
      CompElliptic.CurveForms.ShortWeierstrass.OnCurve]
    rw [← h_input] at h_spec
    set x := Expression.eval env.toEnvironment input_var.x
    set y := Expression.eval env.toEnvironment input_var.y
    rcases h_spec with h_onCurve | h_identity
    · have h_eq : y * y - x * x * x - (5 : Fp) = 0 := by linear_combination h_onCurve
      constructor
      · linear_combination x * h_eq
      · linear_combination y * h_eq
    · have hx := congrArg Point.x h_identity
      have hy := congrArg Point.y h_identity
      change x = 0 at hx
      change y = 0 at hy
      constructor
      · rw [hx]; ring
      · rw [hy]; ring
end Gate

def circuit : GeneralFormalCircuit.WithHint Fp (Unconstrained Point) Point where
  main value := do
    let point ← witnessProgram value
    Gate.circuit point
    return point

  Spec _ output _ := output.Valid
  ProverAssumptions value _ _ := value.Valid
  ProverSpec value output _ := output = value

  soundness := by
    circuit_proof_start [Gate.circuit]
    exact h_holds

  completeness := by
    circuit_proof_start [Gate.circuit]
    rcases input with ⟨x, y⟩
    simp_all [circuit_norm]

end WitnessPoint

namespace WitnessNonIdentityPoint

namespace Gate

def main (point : Var Point Fp) : Circuit Fp Unit := do
  assertZero (point.y * point.y - point.x * point.x * point.x - (pallasB : Fp))

def circuit : FormalAssertion Fp Point where
  name := "GATE witness non-identity point"
  main
  Spec point := point.OnCurve
  soundness := by
    circuit_proof_start [main, Point.OnCurve, Point.coords, pallasB,
      CompElliptic.CurveForms.ShortWeierstrass.OnCurve]
    rw [← h_input]
    linear_combination h_holds
  completeness := by
    circuit_proof_start [main, Point.OnCurve, Point.coords, pallasB,
      CompElliptic.CurveForms.ShortWeierstrass.OnCurve]
    rw [← h_input] at h_spec
    linear_combination h_spec

end Gate

def circuit : GeneralFormalCircuit.WithHint Fp (Unconstrained Point) Point where
  main value := do
    let point ← witnessProgram value
    Gate.circuit point
    return point

  Spec _ output _ := output.OnCurve
  ProverAssumptions value _ _ := value.OnCurve
  ProverSpec value output _ := output = value

  soundness := by
    circuit_proof_start [Gate.circuit]
    exact h_holds

  completeness := by
    circuit_proof_start [Gate.circuit]
    rcases input with ⟨x, y⟩
    simp_all [circuit_norm]

end WitnessNonIdentityPoint

end Ecc
end Orchard
