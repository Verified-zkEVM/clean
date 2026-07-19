import Clean.Ironwood.Specs.Pallas
import Clean.Ironwood.Ecc.Defs
import Clean.Utils.Tactics
import Mathlib.Tactic

namespace Halo2.Ironwood.Ecc

open CompElliptic.CurveForms

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

def Assumptions (input : Input Fp) : Prop :=
  input.p.x ≠ input.q.x

def Spec (input : Input Fp) : Prop :=
  input.r = input.p.nondegenerateAdd input.q

theorem polys_zero_of_nondegenerateAdd {input : AddIncomplete.Input Fp}
    (hx : input.p.x ≠ input.q.x) :
    poly1 (Input.fromPoints input.p input.q (input.p.nondegenerateAdd input.q)) = 0 ∧
      poly2 (Input.fromPoints input.p input.q (input.p.nondegenerateAdd input.q)) = 0 := by
  unfold poly1 poly2 Input.fromPoints Point.nondegenerateAdd
  have hden : input.q.x - input.p.x ≠ 0 := by
    intro h
    apply hx
    exact (sub_eq_zero.mp h).symm
  constructor <;> field_simp [hden] <;> ring

theorem eq_nondegenerateAdd_of_polys_zero {p q r : Point Fp}
    (hx : p.x ≠ q.x)
    (h : poly1 (Input.fromPoints p q r) = 0 ∧
      poly2 (Input.fromPoints p q r) = 0) :
    r = p.nondegenerateAdd q := by
  rcases p with ⟨px, py⟩
  rcases q with ⟨qx, qy⟩
  rcases r with ⟨rx, ry⟩
  unfold poly1 poly2 Input.fromPoints at h
  unfold Point.nondegenerateAdd
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

end Gate

def Assumptions (input : Input Fp) : Prop :=
  input.p.OnCurve ∧
    input.q.OnCurve ∧
    input.p.x ≠ input.q.x

def Spec (input : Input Fp) (output : Point Fp) : Prop :=
  output.OnCurve ∧ output = input.p + input.q

end Halo2.Ironwood.Ecc.AddIncomplete
