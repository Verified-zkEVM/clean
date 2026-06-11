import Clean.Orchard.Ecc.Defs
import Clean.Utils.Tactics
import Mathlib.Tactic

namespace Orchard
namespace Ecc

/-!
Reference:
`halo2@halo2_gadgets-0.5.0/halo2_gadgets/src/ecc/chip/add_incomplete.rs`
- `incomplete addition`

The Rust assignment rejects exceptional cases where either input is encoded identity or
`x_p = x_q`. This Clean circuit exposes those rejection cases as assumptions and
specifies the output as short-Weierstrass addition.
-/


namespace IncompleteAdd

structure Input (F : Type) where
  p : Point F
  q : Point F
deriving ProvableStruct

structure Row (F : Type) where
  p : Point F
  q : Point F
  r : Point F
deriving ProvableStruct

def lambda (input : Input Fp) : Fp :=
  (input.q.y - input.p.y) * (input.q.x - input.p.x)⁻¹

def outputValue (input : Input Fp) : Point Fp :=
  let slope := lambda input
  let xR := slope * slope - input.p.x - input.q.x
  let yR := slope * (input.p.x - xR) - input.p.y
  { x := xR, y := yR }

theorem outputValue_eq_swAdd {input : Input Fp}
    (hp : ¬ Point.isIdentityEncoding input.p) (hq : ¬ Point.isIdentityEncoding input.q)
    (hx : input.p.x ≠ input.q.x) :
    Point.coords (outputValue input) =
      CompElliptic.CurveForms.ShortWeierstrass.add
        (0 : Fp) (Point.coords input.p) (Point.coords input.q) := by
  rcases input with ⟨⟨px, py⟩, ⟨qx, qy⟩⟩
  unfold Point.coords outputValue lambda CompElliptic.CurveForms.ShortWeierstrass.add
  unfold Point.isIdentityEncoding at hp hq
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

def poly1 {K : Type} [Add K] [Sub K] [Mul K] (input : Input K) (output : Point K) :
    K :=
  (output.x + input.q.x + input.p.x) *
      (input.p.x - input.q.x) *
      (input.p.x - input.q.x) -
    (input.p.y - input.q.y) * (input.p.y - input.q.y)

def poly2 {K : Type} [Add K] [Sub K] [Mul K] (input : Input K) (output : Point K) :
    K :=
  (output.y + input.q.y) * (input.p.x - input.q.x) -
    (input.p.y - input.q.y) * (input.q.x - output.x)

def Assumptions (input : Input Fp) : Prop :=
  ¬ Point.isIdentityEncoding input.p ∧
    ¬ Point.isIdentityEncoding input.q ∧
    input.p.x ≠ input.q.x

def Spec (input : Input Fp) (output : Point Fp) : Prop :=
  Point.coords output =
    CompElliptic.CurveForms.ShortWeierstrass.add
      (0 : Fp) (Point.coords input.p) (Point.coords input.q)

theorem outputValue_polys {input : Input Fp} (hx : input.p.x ≠ input.q.x) :
    poly1 input (outputValue input) = 0 ∧ poly2 input (outputValue input) = 0 := by
  unfold poly1 poly2 outputValue lambda
  have hden : input.q.x - input.p.x ≠ 0 := by
    intro h
    apply hx
    exact (sub_eq_zero.mp h).symm
  constructor <;> field_simp [hden] <;> ring

theorem polys_eq_outputValue {input : Input Fp}
    {output : Point Fp}
    (hx : input.p.x ≠ input.q.x)
    (h : poly1 input output = 0 ∧ poly2 input output = 0) :
    output = outputValue input := by
  rcases input with ⟨⟨px, py⟩, ⟨qx, qy⟩⟩
  rcases output with ⟨rx, ry⟩
  unfold poly1 poly2 at h
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

namespace Gate

def Assumptions (row : Row Fp) : Prop :=
  row.p.x ≠ row.q.x

def Spec (row : Row Fp) : Prop :=
  row.r = outputValue ({ p := row.p, q := row.q } : Input Fp)

def main (row : Var Row Fp) : Circuit Fp Unit := do
  assertZero (poly1 { p := row.p, q := row.q } row.r)
  assertZero (poly2 { p := row.p, q := row.q } row.r)

def circuit : FormalAssertion Fp Row where
  name := "GATE incomplete addition"
  main
  Assumptions
  Spec
  soundness := by
    circuit_proof_start [main, Assumptions, Spec, poly1, poly2]
    have hpolys : poly1 { p := input_p, q := input_q } input_r = 0 ∧
        poly2 { p := input_p, q := input_q } input_r = 0 := by
      rw [← h_input.1, ← h_input.2.1, ← h_input.2.2]
      simpa [poly1, poly2, sub_eq_add_neg] using h_holds
    exact polys_eq_outputValue h_assumptions hpolys
  completeness := by
    circuit_proof_start [main, Assumptions, Spec, poly1, poly2]
    have hpolys := outputValue_polys (input := { p := input_p, q := input_q }) h_assumptions
    rw [← h_spec] at hpolys
    rw [← h_input.1, ← h_input.2.1, ← h_input.2.2] at hpolys
    simpa [poly1, poly2, sub_eq_add_neg] using hpolys

end Gate

def main (input : Var Input Fp) :
    Circuit Fp (Var Point Fp) := do
  let p <== input.p
  let q <== input.q
  let r ← witness fun env => outputValue ({ p := eval env p, q := eval env q } : Input Fp)
  Gate.circuit ({ p, q, r } : Var Row Fp)
  return r

instance elaborated : ElaboratedCircuit Fp Input Point main := by
  elaborate_circuit

theorem soundness : Soundness Fp main Assumptions Spec := by
  circuit_proof_start [main, Assumptions, Spec, Gate.circuit, Gate.Spec,
    outputValue_eq_swAdd]
  rcases h_assumptions with ⟨hp, hq, hx⟩
  rcases h_holds with ⟨hpCopyEq, hqCopyEq, hrow⟩
  have hgateAssumptions :
      Gate.Assumptions {
        p := {
          x := Expression.eval env (varFromOffset Point i₀).x
          y := Expression.eval env (varFromOffset Point i₀).y
        }
        q := {
          x := Expression.eval env (varFromOffset Point (i₀ + 2)).x
          y := Expression.eval env (varFromOffset Point (i₀ + 2)).y
        }
        r := {
          x := Expression.eval env (varFromOffset Point (i₀ + 2 + 2)).x
          y := Expression.eval env (varFromOffset Point (i₀ + 2 + 2)).y
        }
      } := by
    simp [Gate.Assumptions]
    intro h
    apply hx
    have hpx := congrArg Point.x hpCopyEq
    have hqx := congrArg Point.x hqCopyEq
    rw [← hpx, ← hqx]
    exact h
  have hrowEq := hrow hgateAssumptions
  rw [hrowEq]
  simpa [hpCopyEq, hqCopyEq] using outputValue_eq_swAdd hp hq hx

theorem completeness : Completeness Fp main Assumptions := by
  circuit_proof_start [main, Assumptions, Gate.circuit, Gate.Assumptions, Gate.Spec]
  rcases h_assumptions with ⟨hp, hq, hx⟩
  simp_all [circuit_norm, explicit_provable_type]

def circuit : FormalCircuit Fp Input Point where
  main
  elaborated
  Assumptions
  Spec
  soundness
  completeness

end IncompleteAdd

end Ecc
end Orchard
