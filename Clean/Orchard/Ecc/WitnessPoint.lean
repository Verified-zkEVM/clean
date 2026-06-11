import Clean.Orchard.Ecc.Defs
import Clean.Utils.Tactics
import Mathlib.Tactic

namespace Orchard
namespace Ecc

variable {F : Type} [Field F]

namespace PointOrIdentity

def main (point : Var Point Fp) : Circuit Fp Unit := do
  let equation := point.y * point.y - point.x * point.x * point.x - (pallasB : Fp)
  assertZero (point.x * equation)
  assertZero (point.y * equation)

def circuit : FormalAssertion Fp Point where
  name := "GATE witness point"
  main
  Spec := Point.isPointOrIdentity
  soundness := by
    circuit_proof_start [main, Point.isPointOrIdentity, Point.isIdentityEncoding, Point.onCurve, Point.curveEquation, pallasB]
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
    circuit_proof_start [main, Point.isPointOrIdentity, Point.isIdentityEncoding, Point.onCurve, Point.curveEquation, pallasB]
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

def main (point : Var Point Fp) : Circuit Fp Unit := do
  assertZero (point.y * point.y - point.x * point.x * point.x - (pallasB : Fp))

def circuit : FormalAssertion Fp Point where
  name := "GATE witness non-identity point"
  main
  Spec := Point.onCurve
  soundness := by
    circuit_proof_start [main, Point.onCurve, Point.curveEquation, pallasB]
    rw [← h_input]
    simpa only [Point.eval_eq, Point.onCurve, Point.curveEquation, pallasB,
      sub_eq_add_neg] using h_holds
  completeness := by
    circuit_proof_start [main, Point.onCurve, Point.curveEquation, pallasB]
    rw [← h_input] at h_spec
    simpa only [Point.eval_eq, Point.onCurve, Point.curveEquation, pallasB,
      sub_eq_add_neg] using h_spec

end NonIdentityPoint

end Ecc
end Orchard
