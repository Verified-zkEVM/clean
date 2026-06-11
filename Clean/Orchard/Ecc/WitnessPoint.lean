import Clean.Orchard.Ecc.Theorems
import Clean.Utils.Tactics
import Mathlib.Tactic

namespace Orchard
namespace Ecc

open CompElliptic.Curves.Pasta

/-!
Reference:
`halo2@halo2_gadgets-0.5.0/halo2_gadgets/src/ecc/chip/witness_point.rs`
- `witness point`
- `witness non-identity point`
-/

namespace WitnessPoint

namespace Gate

def main (point : Var Point Fp) : Circuit Fp Unit := do
  let equation := point.y * point.y - point.x * point.x * point.x - (pallasB : Fp)
  assertZero (point.x * equation)
  assertZero (point.y * equation)

def circuit : FormalAssertion Fp Point where
  name := "GATE witness point"
  main
  Spec point := Pallas.Valid point.coords
  soundness := by
    circuit_proof_start [main, Pallas.Valid, Point.coords, pallasB,
      CompElliptic.CurveForms.ShortWeierstrass.Valid,
      CompElliptic.CurveForms.ShortWeierstrass.OnCurve, Pallas.a, Pallas.b]
    rw [← h_input]
    set x := Expression.eval env input_var.x
    set y := Expression.eval env input_var.y
    by_cases hx : x = 0
    · by_cases hy : y = 0
      · exact Or.inr (by rw [Prod.mk.injEq]; exact ⟨hx, hy⟩)
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
    circuit_proof_start [main, Pallas.Valid, Point.coords, pallasB,
      CompElliptic.CurveForms.ShortWeierstrass.Valid,
      CompElliptic.CurveForms.ShortWeierstrass.OnCurve, Pallas.a, Pallas.b]
    rw [← h_input] at h_spec
    set x := Expression.eval env.toEnvironment input_var.x
    set y := Expression.eval env.toEnvironment input_var.y
    rcases h_spec with h_onCurve | h_identity
    · have h_eq : y * y - x * x * x - (5 : Fp) = 0 := by linear_combination h_onCurve
      constructor
      · linear_combination x * h_eq
      · linear_combination y * h_eq
    · rw [Prod.mk.injEq] at h_identity
      obtain ⟨hx, hy⟩ := h_identity
      simp only at hx hy
      constructor
      · rw [hx]; ring
      · rw [hy]; ring
end Gate

def circuit : GeneralFormalCircuit.WithHint Fp (UnconstrainedDep Point) Point where
  main value := do
    let point ← witness value
    Gate.circuit point
    return point

  Spec _ output _ := Pallas.Valid output.coords
  ProverAssumptions value _ _ := Pallas.Valid value.coords
  ProverSpec value output _ := output = value

  soundness := by
    circuit_proof_start [Gate.circuit]
    exact h_holds

  completeness := by
    circuit_proof_start [Gate.circuit, explicit_provable_type]
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
  Spec point := Pallas.OnCurve point.coords
  soundness := by
    circuit_proof_start [main, Point.coords, pallasB,
      CompElliptic.CurveForms.ShortWeierstrass.OnCurve, Pallas.a, Pallas.b]
    rw [← h_input]
    linear_combination h_holds
  completeness := by
    circuit_proof_start [main, Point.coords, pallasB,
      CompElliptic.CurveForms.ShortWeierstrass.OnCurve, Pallas.a, Pallas.b]
    rw [← h_input] at h_spec
    linear_combination h_spec

end Gate

def circuit : GeneralFormalCircuit.WithHint Fp (UnconstrainedDep Point) Point where
  main value := do
    let point ← witness value
    Gate.circuit point
    return point

  Spec _ output _ := Pallas.OnCurve output.coords
  ProverAssumptions value _ _ := Pallas.OnCurve value.coords
  ProverSpec value output _ := output = value

  soundness := by
    circuit_proof_start [Gate.circuit]
    exact h_holds

  completeness := by
    circuit_proof_start [Gate.circuit, explicit_provable_type]
    rcases input with ⟨x, y⟩
    simp_all [circuit_norm]

end WitnessNonIdentityPoint

end Ecc
end Orchard
