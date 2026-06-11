import Clean.Orchard.Ecc.Defs
import Clean.Utils.Tactics
import Mathlib.Tactic

namespace Orchard
namespace Ecc

namespace WitnessPoint

namespace Gate

def main (point : Var Point Fp) : Circuit Fp Unit := do
  let equation := point.y * point.y - point.x * point.x * point.x - (pallasB : Fp)
  assertZero (point.x * equation)
  assertZero (point.y * equation)

def circuit : FormalAssertion Fp Point where
  name := "GATE witness point"
  main
  Spec := Point.isPointOrIdentity
  soundness := by
    circuit_proof_start [main, Point.isPointOrIdentity, Point.isIdentityEncoding, Point.onCurve, pallasB]
    rw [← h_input]
    by_cases hx : Expression.eval env input_var.x = 0
    · by_cases hy : Expression.eval env input_var.y = 0
      · exact Or.inl ⟨hx, hy⟩
      · right
        have hy_mul :
            Expression.eval env input_var.y *
              (Expression.eval env input_var.y * Expression.eval env input_var.y -
                Expression.eval env input_var.x * Expression.eval env input_var.x *
                  Expression.eval env input_var.x - (5 : Fp)) = 0 := by
          simpa [sub_eq_add_neg] using h_holds.2
        exact (mul_eq_zero.mp hy_mul).resolve_left hy
    · right
      have hx_mul :
          Expression.eval env input_var.x *
            (Expression.eval env input_var.y * Expression.eval env input_var.y -
              Expression.eval env input_var.x * Expression.eval env input_var.x *
                Expression.eval env input_var.x - (5 : Fp)) = 0 := by
        simpa [sub_eq_add_neg] using h_holds.1
      exact (mul_eq_zero.mp hx_mul).resolve_left hx
  completeness := by
    circuit_proof_start [main, Point.isPointOrIdentity, Point.isIdentityEncoding, Point.onCurve, pallasB]
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

end Gate

def circuit : GeneralFormalCircuit.WithHint Fp (UnconstrainedDep Point) Point where
  main value := do
    let point ← witness value
    Gate.circuit point
    return point

  Spec _ output _ := Point.isPointOrIdentity output
  ProverAssumptions value _ _ := Point.isPointOrIdentity value
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
  Spec := Point.onCurve
  soundness := by
    circuit_proof_start [main, Point.onCurve, pallasB]
    rw [← h_input]
    simpa only [Point.eval_eq, Point.onCurve, pallasB,
      sub_eq_add_neg] using h_holds
  completeness := by
    circuit_proof_start [main, Point.onCurve, pallasB]
    rw [← h_input] at h_spec
    simpa only [Point.eval_eq, Point.onCurve, pallasB,
      sub_eq_add_neg] using h_spec

end Gate

def circuit : GeneralFormalCircuit.WithHint Fp (UnconstrainedDep Point) Point where
  main value := do
    let x ← witnessField fun env => (value env).x
    let y ← witnessField fun env => (value env).y
    let point := ({ x, y } : Var Point Fp)
    Gate.circuit point
    return point

  Spec _ output _ := Point.onCurve output
  ProverAssumptions value _ _ := Point.onCurve value
  ProverSpec value output _ := output = value

  soundness := by
    circuit_proof_start [Gate.circuit]
    exact h_holds

  completeness := by
    circuit_proof_start [Gate.circuit]
    rcases h_env with ⟨hx, hy⟩
    constructor
    · rw [hx, hy]
      exact h_assumptions
    · simp [hx, hy]

end WitnessNonIdentityPoint

end Ecc
end Orchard
