import Clean.Orchard.Ecc.Theorems
import Clean.Utils.Tactics
import Mathlib.Tactic

namespace Orchard.Ecc

open CompElliptic.Curves.Pasta

/-!
Reference:
`halo2@halo2_gadgets-0.5.0/halo2_gadgets/src/ecc/chip/add_incomplete.rs`
- `incomplete addition`

The Rust assignment takes non-identity input points, rejects `x_p = x_q`, and assigns the
next-row output as their incomplete short-Weierstrass sum.
-/

namespace AddIncomplete

structure Input (F : Type) where
  p : Point F
  q : Point F
deriving ProvableStruct

def outputValue (input : Input Fp) : Point Fp :=
  let slope := (input.q.y - input.p.y) * (input.q.x - input.p.x)⁻¹
  let xR := slope * slope - input.p.x - input.q.x
  let yR := slope * (input.p.x - xR) - input.p.y
  { x := xR, y := yR }

theorem outputValue_eq_add {input : Input Fp}
    (hp : input.p ≠ Point.zero) (hq : input.q ≠ Point.zero)
    (hx : input.p.x ≠ input.q.x) :
    (outputValue input).coords = Pallas.add input.p.coords input.q.coords := by
  rcases input with ⟨⟨px, py⟩, ⟨qx, qy⟩⟩
  simp only [outputValue, Point.coords, Pallas.add, Point.zero, CompElliptic.CurveForms.ShortWeierstrass.add] at *
  have hp0 : ¬(px, py) = (0, 0) := by grind
  have hq0 : ¬(qx, qy) = (0, 0) := by grind
  rw [if_neg hp0, if_neg hq0]
  rw [if_neg hx, Prod.mk.injEq]
  constructor <;> ring

namespace Gate

structure Input (F : Type) where
  x_p : F
  y_p : F
  x_qr : CurrentNext F
  y_qr : CurrentNext F
deriving ProvableStruct

namespace Input

variable {K : Type}

def p (input : Input K) : Point K where
  x := input.x_p
  y := input.y_p

def q (input : Input K) : Point K where
  x := input.x_qr.curr
  y := input.y_qr.curr

def r (input : Input K) : Point K where
  x := input.x_qr.next
  y := input.y_qr.next

def fromPoints (p q r : Point K) : Input K where
  x_p := p.x
  y_p := p.y
  x_qr := { curr := q.x, next := r.x }
  y_qr := { curr := q.y, next := r.y }

end Input

def poly1 {K : Type} [Add K] [Sub K] [Mul K] (input : Input K) : K :=
  (input.x_qr.next + input.x_qr.curr + input.x_p) *
      (input.x_p - input.x_qr.curr) *
      (input.x_p - input.x_qr.curr) -
    (input.y_p - input.y_qr.curr) * (input.y_p - input.y_qr.curr)

def poly2 {K : Type} [Add K] [Sub K] [Mul K] (input : Input K) : K :=
  (input.y_qr.next + input.y_qr.curr) * (input.x_p - input.x_qr.curr) -
    (input.y_p - input.y_qr.curr) * (input.x_qr.curr - input.x_qr.next)

theorem polys_zero_of_outputValue {input : AddIncomplete.Input Fp}
    (hx : input.p.x ≠ input.q.x) :
    poly1 (Input.fromPoints input.p input.q (outputValue input)) = 0 ∧
      poly2 (Input.fromPoints input.p input.q (outputValue input)) = 0 := by
  unfold poly1 poly2 Input.fromPoints outputValue
  have hden : input.q.x - input.p.x ≠ 0 := by
    intro h
    apply hx
    exact (sub_eq_zero.mp h).symm
  constructor <;> field_simp [hden] <;> ring

theorem eq_outputValue_of_polys_zero {input : AddIncomplete.Input Fp}
    {output : Point Fp}
    (hx : input.p.x ≠ input.q.x)
    (h : poly1 (Input.fromPoints input.p input.q output) = 0 ∧
      poly2 (Input.fromPoints input.p input.q output) = 0) :
    output = outputValue input := by
  rcases input with ⟨⟨px, py⟩, ⟨qx, qy⟩⟩
  rcases output with ⟨rx, ry⟩
  unfold poly1 poly2 Input.fromPoints at h
  unfold outputValue
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

def main (input : Var Input Fp) : Circuit Fp Unit := do
  assertZero (poly1 input)
  assertZero (poly2 input)

def Assumptions (input : Input Fp) : Prop :=
  input.p.x ≠ input.q.x

def Spec (input : Input Fp) : Prop :=
  input.r = outputValue { p := input.p, q := input.q }

def circuit : FormalAssertion Fp Input where
  name := "GATE incomplete addition"
  main
  Assumptions
  Spec
  soundness := by
    circuit_proof_start [main, Assumptions, Spec, poly1, poly2, Input.r]
    apply eq_outputValue_of_polys_zero h_assumptions
    simpa [poly1, poly2, Input.fromPoints, sub_eq_add_neg] using h_holds
  completeness := by
    circuit_proof_start [main, Assumptions, Spec, poly1, poly2, Input.r, Input.p, Input.q]
    have hpolys := polys_zero_of_outputValue (input := {
      p := { x := input_x_p, y := input_y_p }
      q := { x := input_x_qr_curr, y := input_y_qr_curr }
    }) h_assumptions
    rw [← h_spec] at hpolys
    simpa [poly1, poly2, Input.fromPoints, Input.p, Input.q, Input.r, sub_eq_add_neg] using hpolys

end Gate

def main (input : Var Input Fp) :
    Circuit Fp (Var Point Fp) := do
  let p <== input.p
  let q <== input.q
  let r ← witness fun env => outputValue { p := eval env p, q := eval env q }
  Gate.circuit {
    x_p := p.x
    y_p := p.y
    x_qr := { curr := q.x, next := r.x }
    y_qr := { curr := q.y, next := r.y }
  }
  return r

def Assumptions (input : Input Fp) : Prop :=
  input.p.OnCurve ∧
    input.q.OnCurve ∧
    input.p.x ≠ input.q.x

def Spec (input : Input Fp) (output : Point Fp) : Prop :=
  output.OnCurve ∧
    output = input.p + input.q

theorem outputValue_onCurve {input : Input Fp}
    (hp : input.p.OnCurve)
    (hq : input.q.OnCurve)
    (hx : input.p.x ≠ input.q.x) :
    (outputValue input).OnCurve := by
  have hpNonId : input.p ≠ Point.zero := Point.ne_zero_of_onCurve hp
  have hqNonId : input.q ≠ Point.zero := Point.ne_zero_of_onCurve hq
  have hcoords := outputValue_eq_add hpNonId hqNonId hx
  replace hp := (Point.onCurve_iff input.p).mp hp
  replace hq := (Point.onCurve_iff input.q).mp hq
  rcases input with ⟨⟨px, py⟩, ⟨qx, qy⟩⟩
  have hp0 : (px, py) ≠ ((0 : Fp), 0) := by
    intro h
    have hx0 : px = 0 := (Prod.ext_iff.mp h).1
    exact CompElliptic.Curves.Pasta.Pallas.no_onCurve_x_zero py (by
      rw [hx0] at hp
      exact hp)
  have hq0 : (qx, qy) ≠ ((0 : Fp), 0) := by
    intro h
    have hx0 : qx = 0 := (Prod.ext_iff.mp h).1
    exact CompElliptic.Curves.Pasta.Pallas.no_onCurve_x_zero qy (by
      rw [hx0] at hq
      exact hq)
  have hxy : ¬(px = qx ∧ py + qy = 0) := by
    intro h
    exact hx h.1
  rw [Point.onCurve_iff]
  rw [hcoords]
  simp only [Pallas.add, Pallas.OnCurve, Point.coords]
  rw [CompElliptic.CurveForms.ShortWeierstrass.add_eq_addXY hp0 hq0 hxy]
  have hxy' :
      ¬(px = qx ∧ py =
        WeierstrassCurve.Affine.negY
          (CompElliptic.CurveForms.ShortWeierstrass.toW
            CompElliptic.Curves.Pasta.Pallas.a
            CompElliptic.Curves.Pasta.Pallas.b) qx qy) := by
    rintro ⟨hxeq, _⟩
    exact hx hxeq
  have hns := WeierstrassCurve.Affine.nonsingular_add
    (CompElliptic.CurveForms.ShortWeierstrass.nonsingular_toW hp)
    (CompElliptic.CurveForms.ShortWeierstrass.nonsingular_toW hq)
    hxy'
  exact CompElliptic.CurveForms.ShortWeierstrass.equation_toW.mp hns.left

instance elaborated : ElaboratedCircuit Fp Input Point main := by
  elaborate_circuit

theorem soundness : Soundness Fp main Assumptions Spec := by
  circuit_proof_start [main, Assumptions, Spec, Gate.circuit, Gate.Spec,
    outputValue_eq_add, outputValue_onCurve, Gate.Input.r, Gate.Input.p, Gate.Input.q,
    Gate.Assumptions]
  rcases h_assumptions with ⟨hpCurve, hqCurve, hx⟩
  have hp : input_p ≠ Point.zero := Point.ne_zero_of_onCurve hpCurve
  have hq : input_q ≠ Point.zero := Point.ne_zero_of_onCurve hqCurve
  set x_p := Expression.eval env (varFromOffset Point i₀).x
  set x_q := Expression.eval env (varFromOffset Point (i₀ + 2)).x
  rcases h_holds with ⟨hpCopyEq, hqCopyEq, hrow⟩
  have hgateAssumptions : x_p ≠ x_q := by
    convert hx
    rw [← hpCopyEq]
    rw [← hqCopyEq]
  specialize hrow hgateAssumptions
  simp only [hrow, hpCopyEq, hqCopyEq]
  constructor
  · exact outputValue_onCurve hpCurve hqCurve hx
  · exact Point.ext_coords (outputValue_eq_add (input := { p := input_p, q := input_q }) hp hq hx)

theorem completeness : Completeness Fp main Assumptions := by
  circuit_proof_start [main, Assumptions, Gate.circuit, Gate.Assumptions, Gate.Spec]
  rcases h_assumptions with ⟨_hp, _hq, hx⟩
  simp_all [circuit_norm, explicit_provable_type, Gate.Input.p, Gate.Input.q, Gate.Input.r]

def circuit : FormalCircuit Fp Input Point where
  main
  elaborated
  Assumptions
  Spec
  soundness
  completeness

end Orchard.Ecc.AddIncomplete
