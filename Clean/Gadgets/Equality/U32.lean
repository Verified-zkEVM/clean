import Mathlib.Algebra.Field.Basic
import Mathlib.Data.ZMod.Basic
import Clean.Utils.Primes
import Clean.Utils.Vector
import Clean.Circuit.Expression
import Clean.Circuit.Provable
import Clean.Circuit.Basic
import Clean.Utils.Field
import Clean.Types.U32

section
variable {p : ℕ} [Fact p.Prime]


namespace Gadgets.Equality.U32
structure Inputs (F : Type) where
  x: U32 F
  y: U32 F

instance : ProvableType Inputs where
  size := 8
  to_vars s := vec [s.x.x0, s.x.x1, s.x.x2, s.x.x3, s.y.x0, s.y.x1, s.y.x2, s.y.x3]
  from_vars v :=
    let ⟨ [x0, x1, x2, x3, y0, y1, y2, y3], _ ⟩ := v
    ⟨ ⟨x0, x1, x2, x3⟩, ⟨y0, y1, y2, y3⟩ ⟩
  to_values s := vec [s.x.x0, s.x.x1, s.x.x2, s.x.x3, s.y.x0, s.y.x1, s.y.x2, s.y.x3]
  from_values v :=
    let ⟨ [x0, x1, x2, x3, y0, y1, y2, y3], _ ⟩ := v
    ⟨ ⟨x0, x1, x2, x3⟩, ⟨y0, y1, y2, y3⟩ ⟩


def assert_eq (input : Var Inputs (F p)) := do
  let ⟨x, y⟩ := input
  assert_zero (x.x0 - y.x0)
  assert_zero (x.x1 - y.x1)
  assert_zero (x.x2 - y.x2)
  assert_zero (x.x3 - y.x3)

def spec (input: Inputs (F p)) :=
  let ⟨x, y⟩ := input
  x = y


def circuit : FormalAssertion (F p) Inputs where
  main := assert_eq
  assumptions _ := true
  spec := spec

  soundness := by
    intro ctx env vars input h_inputs _ h_holds
    let ⟨⟨x0, x1, x2, x3⟩, ⟨y0, y1, y2, y3⟩⟩ := input
    let ⟨⟨x0_var, x1_var, x2_var, x3_var⟩, ⟨y0_var, y1_var, y2_var, y3_var⟩⟩ := vars

    dsimp [circuit_norm] at h_holds

    have hx0 : x0_var.eval env = x0 := by injections
    have hx1 : x1_var.eval env = x1 := by injections
    have hx2 : x2_var.eval env = x2 := by injections
    have hx3 : x3_var.eval env = x3 := by injections
    have hy0 : y0_var.eval env = y0 := by injections
    have hy1 : y1_var.eval env = y1 := by injections
    have hy2 : y2_var.eval env = y2 := by injections
    have hy3 : y3_var.eval env = y3 := by injections

    rw [hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3] at h_holds

    dsimp [spec]
    ring_nf at h_holds
    repeat rw [sub_eq_zero] at h_holds
    rcases h_holds with ⟨⟨⟨eq0, eq1⟩, eq2⟩, eq3⟩
    rw [eq0, eq1, eq2, eq3]

  completeness := by
    -- introductions
    intro n env inputs_var henv inputs h_inputs _ spec
    let ⟨⟨x0, x1, x2, x3⟩, ⟨y0, y1, y2, y3⟩⟩ := inputs
    let ⟨⟨x0_var, x1_var, x2_var, x3_var⟩, ⟨y0_var, y1_var, y2_var, y3_var⟩⟩ := inputs_var

    -- characterize inputs
    have hx0 : x0_var.eval env = x0 := by injection h_inputs; injections
    have hx1 : x1_var.eval env = x1 := by injection h_inputs; injections
    have hx2 : x2_var.eval env = x2 := by injection h_inputs; injections
    have hx3 : x3_var.eval env = x3 := by injection h_inputs; injections
    have hy0 : y0_var.eval env = y0 := by injection h_inputs; injections
    have hy1 : y1_var.eval env = y1 := by injection h_inputs; injections
    have hy2 : y2_var.eval env = y2 := by injection h_inputs; injections
    have hy3 : y3_var.eval env = y3 := by injection h_inputs; injections

    have spec0 : x0 = y0 := by injection spec
    have spec1 : x1 = y1 := by injection spec
    have spec2 : x2 = y2 := by injection spec
    have spec3 : x3 = y3 := by injection spec

    simp only [Circuit.constraints_hold.completeness, Expression.eval, neg_mul, one_mul]
    rw [hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3]
    rw [spec0, spec1, spec2, spec3]
    simp only [add_neg_cancel, and_self]

end Gadgets.Equality.U32
