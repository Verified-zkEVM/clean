import Clean.Orchard.Ecc.Defs
import Clean.Utils.Tactics
import Mathlib.Tactic

namespace Orchard
namespace Ecc

variable {F : Type} [Field F]

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

def poly1 (input : Input Fp) (output : Point Fp) :
    Fp :=
  (output.x + input.q.x + input.p.x) *
      (input.p.x - input.q.x) *
      (input.p.x - input.q.x) -
    (input.p.y - input.q.y) * (input.p.y - input.q.y)

def poly2 (input : Input Fp) (output : Point Fp) :
    Fp :=
  (output.y + input.q.y) * (input.p.x - input.q.x) -
    (input.p.y - input.q.y) * (input.q.x - output.x)

def main (input : Var Input Fp) :
    Circuit Fp (Var Point Fp) := do
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

def Assumptions (input : Input Fp) : Prop :=
  ¬ Point.isIdentityEncoding input.p ∧
    ¬ Point.isIdentityEncoding input.q ∧
    input.p.x ≠ input.q.x

def Spec (input : Input Fp) (output : Point Fp) : Prop :=
  Point.coords output =
    CompElliptic.CurveForms.ShortWeierstrass.add
      (0 : Fp) (Point.coords input.p) (Point.coords input.q)

instance elaborated : ElaboratedCircuit Fp Input Point main := by
  elaborate_circuit

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

theorem soundness : Soundness Fp main Assumptions Spec := by
  circuit_proof_start [main, Assumptions, Spec, poly1, poly2]
  rcases input_p with ⟨px, py⟩
  rcases input_q with ⟨qx, qy⟩
  have hc :
      poly1 { p := { x := px, y := py }, q := { x := qx, y := qy } }
          { x := env.get i₀, y := env.get (i₀ + 1) } = 0 ∧
        poly2 { p := { x := px, y := py }, q := { x := qx, y := qy } }
          { x := env.get i₀, y := env.get (i₀ + 1) } = 0 := by
    simp_all [poly1, poly2, sub_eq_add_neg]
  have hout := polys_eq_outputValue h_assumptions.2.2 hc
  rw [hout]
  exact outputValue_eq_swAdd h_assumptions.1 h_assumptions.2.1 h_assumptions.2.2

theorem completeness : Completeness Fp main Assumptions := by
  circuit_proof_start [main, Assumptions, outputValue, lambda, poly1, poly2]
  have hc := outputValue_polys (input := { p := input_p, q := input_q }) h_assumptions.2.2
  rcases input_p with ⟨px, py⟩
  rcases input_q with ⟨qx, qy⟩
  simp_all [outputValue, lambda, poly1, poly2, sub_eq_add_neg]

def circuit : FormalCircuit Fp Input Point where
  -- TODO: factor the source `incomplete addition` custom gate into a named
  -- `FormalAssertion`, then compose it here instead of naming this entry circuit as a gate.
  main
  elaborated
  Assumptions
  Spec
  soundness
  completeness

end IncompleteAdd

end Ecc
end Orchard
