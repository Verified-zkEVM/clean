import Mathlib.Algebra.Field.Basic
import Mathlib.Data.ZMod.Basic
import Clean.Utils.Primes
import Clean.Utils.Vector
import Clean.Circuit.Expression
import Clean.Circuit.Provable
import Clean.Circuit.Basic
import Clean.Utils.Field

section
variable {p : ℕ} [Fact p.Prime]


namespace Gadgets.Equality
structure InputStruct (F : Type) where
  x: F
  y: F

def Inputs (p : ℕ) : TypePair := ⟨
  InputStruct (Expression (F p)),
  InputStruct (F p)
⟩

instance : ProvableType (F p) (Inputs p) where
  size := 2
  to_vars s := vec [s.x, s.y]
  from_vars v :=
    let ⟨ [x, y], _ ⟩ := v
    ⟨ x, y ⟩
  to_values s := vec [s.x, s.y]
  from_values v :=
    let ⟨ [x, y], _ ⟩ := v
    ⟨ x, y ⟩


def assert_eq (input : (Inputs p).var) := do
  let ⟨x, y⟩ := input
  assert_zero (x - y)

def spec (input: (Inputs p).value) :=
  let ⟨x, y⟩ := input
  x = y


def circuit : FormalAssertion (F p) (Inputs p) where
  main := assert_eq
  assumptions _ := true
  spec := spec

  soundness := by
    intro ctx env input vars h_inputs _ h_holds
    let ⟨x, y⟩ := input
    let ⟨x_var, y_var⟩ := vars

    dsimp at h_holds
    have hx : x_var.eval env = x := by injection h_inputs
    have hy : y_var.eval env = y := by injection h_inputs
    rw [hx, hy] at h_holds

    dsimp [spec]
    ring_nf at h_holds
    rw [sub_eq_zero] at h_holds
    assumption

  completeness := by
    -- introductions
    intro n env inputs_var henv inputs h_inputs _ spec
    let ⟨x, y⟩ := inputs
    let ⟨x_var, y_var⟩ := inputs_var

    -- characterize inputs
    have hx : x_var.eval env = x := by injection h_inputs
    have hy : y_var.eval env = y := by injection h_inputs

    simp [spec]
    rw [hx, hy, spec]
    ring
end Gadgets.Equality
