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

theorem outputValue_eq_swAdd {input : Input Fp}
    (hp : ¬ input.p.isIdentityEncoding) (hq : ¬ input.q.isIdentityEncoding)
    (hx : input.p.x ≠ input.q.x) :
    (outputValue input).coords = Pallas.add input.p.coords input.q.coords := by
  rcases input with ⟨⟨px, py⟩, ⟨qx, qy⟩⟩
  unfold Point.coords outputValue Pallas.add
    CompElliptic.CurveForms.ShortWeierstrass.add
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
    circuit_proof_start [main, Assumptions, Spec, poly1, poly2]
    change ({ x := input_x_qr_next, y := input_y_qr_next } : Point Fp) =
      outputValue ({
        p := { x := input_x_p, y := input_y_p }
        q := { x := input_x_qr_curr, y := input_y_qr_curr }
      } : AddIncomplete.Input Fp)
    apply eq_outputValue_of_polys_zero h_assumptions
    simpa [poly1, poly2, Input.fromPoints, sub_eq_add_neg] using h_holds
  completeness := by
    circuit_proof_start [main, Assumptions, Spec, poly1, poly2]
    have hpolys := polys_zero_of_outputValue (input := {
      p := { x := input_x_p, y := input_y_p }
      q := { x := input_x_qr_curr, y := input_y_qr_curr }
    }) h_assumptions
    change ({ x := input_x_qr_next, y := input_y_qr_next } : Point Fp) =
      outputValue ({
        p := { x := input_x_p, y := input_y_p }
        q := { x := input_x_qr_curr, y := input_y_qr_curr }
      } : AddIncomplete.Input Fp) at h_spec
    rw [← h_spec] at hpolys
    simpa [poly1, poly2, Input.fromPoints, Input.p, Input.q, Input.r, sub_eq_add_neg] using hpolys

end Gate

def main (input : Var Input Fp) :
    Circuit Fp (Var Point Fp) := do
  let p <== input.p
  let q <== input.q
  let r ← witness fun env => outputValue { p := eval env p, q := eval env q }
  Gate.circuit ({
    x_p := p.x
    y_p := p.y
    x_qr := { curr := q.x, next := r.x }
    y_qr := { curr := q.y, next := r.y }
  })
  return r

def Assumptions (input : Input Fp) : Prop :=
  Pallas.OnCurve input.p.coords ∧
    Pallas.OnCurve input.q.coords ∧
    input.p.x ≠ input.q.x

def Spec (input : Input Fp) (output : Point Fp) : Prop :=
  Pallas.OnCurve output.coords ∧
    output.coords = Pallas.add input.p.coords input.q.coords

theorem not_isIdentityEncoding_of_pallas_onCurve {point : Point Fp}
    (hPoint : Pallas.OnCurve point.coords) :
    ¬ point.isIdentityEncoding := by
  rcases point with ⟨x, y⟩
  intro hIdentity
  change x = 0 ∧ y = 0 at hIdentity
  apply CompElliptic.Curves.Pasta.Pallas.no_onCurve_x_zero y
  change CompElliptic.CurveForms.ShortWeierstrass.OnCurve
    CompElliptic.Curves.Pasta.Pallas.a CompElliptic.Curves.Pasta.Pallas.b (x, y) at hPoint
  rw [hIdentity.1] at hPoint
  exact hPoint

theorem outputValue_onCurve {input : Input Fp}
    (hp : Pallas.OnCurve input.p.coords)
    (hq : Pallas.OnCurve input.q.coords)
    (hx : input.p.x ≠ input.q.x) :
    Pallas.OnCurve (outputValue input).coords := by
  have hpNonId : ¬ input.p.isIdentityEncoding :=
    not_isIdentityEncoding_of_pallas_onCurve hp
  have hqNonId : ¬ input.q.isIdentityEncoding :=
    not_isIdentityEncoding_of_pallas_onCurve hq
  have hcoords := outputValue_eq_swAdd (input := input) hpNonId hqNonId hx
  rcases input with ⟨⟨px, py⟩, ⟨qx, qy⟩⟩
  change CompElliptic.CurveForms.ShortWeierstrass.OnCurve
    CompElliptic.Curves.Pasta.Pallas.a CompElliptic.Curves.Pasta.Pallas.b (px, py) at hp
  change CompElliptic.CurveForms.ShortWeierstrass.OnCurve
    CompElliptic.Curves.Pasta.Pallas.a CompElliptic.Curves.Pasta.Pallas.b (qx, qy) at hq
  change (outputValue { p := { x := px, y := py }, q := { x := qx, y := qy } }).coords =
    Pallas.add (px, py) (qx, qy) at hcoords
  change CompElliptic.CurveForms.ShortWeierstrass.OnCurve
    CompElliptic.Curves.Pasta.Pallas.a CompElliptic.Curves.Pasta.Pallas.b
    (outputValue { p := { x := px, y := py }, q := { x := qx, y := qy } }).coords
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
  rw [hcoords]
  change CompElliptic.CurveForms.ShortWeierstrass.OnCurve
    CompElliptic.Curves.Pasta.Pallas.a CompElliptic.Curves.Pasta.Pallas.b
    (CompElliptic.CurveForms.ShortWeierstrass.add
      CompElliptic.Curves.Pasta.Pallas.a (px, py) (qx, qy))
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
    outputValue_eq_swAdd, outputValue_onCurve]
  rcases h_assumptions with ⟨hpCurve, hqCurve, hx⟩
  have hp : ¬ input_p.isIdentityEncoding :=
    not_isIdentityEncoding_of_pallas_onCurve hpCurve
  have hq : ¬ input_q.isIdentityEncoding :=
    not_isIdentityEncoding_of_pallas_onCurve hqCurve
  rcases h_holds with ⟨hpCopyEq, hqCopyEq, hrow⟩
  let gateInput : Gate.Input Fp := {
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
  have hgateAssumptions : Gate.Assumptions gateInput := by
    dsimp [gateInput, Gate.Assumptions, Gate.Input.p, Gate.Input.q]
    intro h
    apply hx
    have hpx := congrArg Point.x hpCopyEq
    have hqx := congrArg Point.x hqCopyEq
    rw [← hpx, ← hqx]
    exact h
  have hrowEq := hrow hgateAssumptions
  constructor
  · change Pallas.OnCurve (Gate.Input.r gateInput).coords
    rw [hrowEq]
    simpa [gateInput, Gate.Input.p, Gate.Input.q, hpCopyEq, hqCopyEq] using
      outputValue_onCurve (input := { p := input_p, q := input_q }) hpCurve hqCurve hx
  · change (Gate.Input.r gateInput).coords =
      Pallas.add input_p.coords input_q.coords
    rw [hrowEq]
    simpa [gateInput, Gate.Input.p, Gate.Input.q, hpCopyEq, hqCopyEq] using
      outputValue_eq_swAdd (input := { p := input_p, q := input_q }) hp hq hx

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
