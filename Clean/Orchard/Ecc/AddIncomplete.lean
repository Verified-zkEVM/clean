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

def Assumptions (input : Input Fp) : Prop :=
  ¬ Point.isIdentityEncoding input.p ∧
    ¬ Point.isIdentityEncoding input.q ∧
    input.p.x ≠ input.q.x

def Spec (input : Input Fp) (output : Point Fp) : Prop :=
  Point.coords output =
    CompElliptic.CurveForms.ShortWeierstrass.add
      (0 : Fp) (Point.coords input.p) (Point.coords input.q)

namespace Gate

structure Row (F : Type) where
  x_p : F
  y_p : F
  x_qr : CurrentNext F
  y_qr : CurrentNext F
deriving ProvableStruct

namespace Row

def p {K : Type} (row : Row K) : Point K where
  x := row.x_p
  y := row.y_p

def q {K : Type} (row : Row K) : Point K where
  x := row.x_qr.curr
  y := row.y_qr.curr

def r {K : Type} (row : Row K) : Point K where
  x := row.x_qr.next
  y := row.y_qr.next

def fromPoints {K : Type} (p q r : Point K) : Row K where
  x_p := p.x
  y_p := p.y
  x_qr := { curr := q.x, next := r.x }
  y_qr := { curr := q.y, next := r.y }

end Row

def poly1 {K : Type} [Add K] [Sub K] [Mul K] (row : Row K) : K :=
  (row.x_qr.next + row.x_qr.curr + row.x_p) *
      (row.x_p - row.x_qr.curr) *
      (row.x_p - row.x_qr.curr) -
    (row.y_p - row.y_qr.curr) * (row.y_p - row.y_qr.curr)

def poly2 {K : Type} [Add K] [Sub K] [Mul K] (row : Row K) : K :=
  (row.y_qr.next + row.y_qr.curr) * (row.x_p - row.x_qr.curr) -
    (row.y_p - row.y_qr.curr) * (row.x_qr.curr - row.x_qr.next)

theorem outputValue_polys {input : Input Fp} (hx : input.p.x ≠ input.q.x) :
    poly1 (Row.fromPoints input.p input.q (outputValue input)) = 0 ∧
      poly2 (Row.fromPoints input.p input.q (outputValue input)) = 0 := by
  unfold poly1 poly2 Row.fromPoints outputValue lambda
  have hden : input.q.x - input.p.x ≠ 0 := by
    intro h
    apply hx
    exact (sub_eq_zero.mp h).symm
  constructor <;> field_simp [hden] <;> ring

theorem polys_eq_outputValue {input : Input Fp}
    {output : Point Fp}
    (hx : input.p.x ≠ input.q.x)
    (h : poly1 (Row.fromPoints input.p input.q output) = 0 ∧
      poly2 (Row.fromPoints input.p input.q output) = 0) :
    output = outputValue input := by
  rcases input with ⟨⟨px, py⟩, ⟨qx, qy⟩⟩
  rcases output with ⟨rx, ry⟩
  unfold poly1 poly2 Row.fromPoints at h
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

def Assumptions (row : Row Fp) : Prop :=
  row.p.x ≠ row.q.x

def Spec (row : Row Fp) : Prop :=
  row.r = outputValue ({ p := row.p, q := row.q } : Input Fp)

def main (row : Var Row Fp) : Circuit Fp Unit := do
  assertZero (poly1 row)
  assertZero (poly2 row)

def circuit : FormalAssertion Fp Row where
  name := "GATE incomplete addition"
  main
  Assumptions
  Spec
  soundness := by
    circuit_proof_start [main, Assumptions, Spec, poly1, poly2]
    change ({ x := input_x_qr_next, y := input_y_qr_next } : Point Fp) =
      outputValue ({
        p := { x := input_x_p, y := input_y_p }
        q := { x := input_x_qr_curr, y := input_y_qr_curr }
      } : Input Fp)
    apply polys_eq_outputValue h_assumptions
    simpa [poly1, poly2, Row.fromPoints, sub_eq_add_neg] using h_holds
  completeness := by
    circuit_proof_start [main, Assumptions, Spec, poly1, poly2]
    have hpolys := outputValue_polys (input := {
      p := { x := input_x_p, y := input_y_p }
      q := { x := input_x_qr_curr, y := input_y_qr_curr }
    }) h_assumptions
    change ({ x := input_x_qr_next, y := input_y_qr_next } : Point Fp) =
      outputValue ({
        p := { x := input_x_p, y := input_y_p }
        q := { x := input_x_qr_curr, y := input_y_qr_curr }
      } : Input Fp) at h_spec
    rw [← h_spec] at hpolys
    simpa [poly1, poly2, Row.fromPoints, Row.p, Row.q, Row.r, sub_eq_add_neg] using hpolys

end Gate

def main (input : Var Input Fp) :
    Circuit Fp (Var Point Fp) := do
  let p <== input.p
  let q <== input.q
  let r ← witness fun env => outputValue ({ p := eval env p, q := eval env q } : Input Fp)
  Gate.circuit ({
    x_p := p.x
    y_p := p.y
    x_qr := { curr := q.x, next := r.x }
    y_qr := { curr := q.y, next := r.y }
  } : Var Gate.Row Fp)
  return r

instance elaborated : ElaboratedCircuit Fp Input Point main := by
  elaborate_circuit

theorem soundness : Soundness Fp main Assumptions Spec := by
  circuit_proof_start [main, Assumptions, Spec, Gate.circuit, Gate.Spec,
    outputValue_eq_swAdd]
  rcases h_assumptions with ⟨hp, hq, hx⟩
  rcases h_holds with ⟨hpCopyEq, hqCopyEq, hrow⟩
  let row : Gate.Row Fp := {
        x_p := Expression.eval env (varFromOffset Point i₀).x
        y_p := Expression.eval env (varFromOffset Point i₀).y
        x_qr := {
          curr := Expression.eval env (varFromOffset Point (i₀ + 2)).x
          next := Expression.eval env (varFromOffset Point (i₀ + 2 + 2)).x
        }
        y_qr := {
          curr := Expression.eval env (varFromOffset Point (i₀ + 2)).y
          next := Expression.eval env (varFromOffset Point (i₀ + 2 + 2)).y
        }
      }
  have hgateAssumptions : Gate.Assumptions row := by
    dsimp [row, Gate.Assumptions, Gate.Row.p, Gate.Row.q]
    intro h
    apply hx
    have hpx := congrArg Point.x hpCopyEq
    have hqx := congrArg Point.x hqCopyEq
    rw [← hpx, ← hqx]
    exact h
  have hrowEq := hrow hgateAssumptions
  change Point.coords (Gate.Row.r row) =
    CompElliptic.CurveForms.ShortWeierstrass.add 0 input_p.coords input_q.coords
  rw [hrowEq]
  simpa [row, Gate.Row.p, Gate.Row.q, hpCopyEq, hqCopyEq] using
    outputValue_eq_swAdd (input := { p := input_p, q := input_q }) hp hq hx

theorem completeness : Completeness Fp main Assumptions := by
  circuit_proof_start [main, Assumptions, Gate.circuit, Gate.Assumptions, Gate.Spec]
  rcases h_assumptions with ⟨_hp, _hq, hx⟩
  simp_all [circuit_norm, explicit_provable_type, Gate.Row.p, Gate.Row.q, Gate.Row.r]

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
