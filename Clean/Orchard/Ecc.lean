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

end Ecc
end Orchard
