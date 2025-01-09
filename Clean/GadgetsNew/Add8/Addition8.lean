import Mathlib.Algebra.Field.Basic
import Mathlib.Data.ZMod.Basic
import Clean.Utils.Primes
import Clean.Utils.Vector
import Clean.Circuit.Expression
import Clean.Circuit.Provable
import Clean.Circuit.Basic
import Clean.Utils.Field
import Clean.GadgetsNew.ByteLookup
import Clean.GadgetsNew.Boolean
import Clean.GadgetsNew.Add8.Addition8Full

namespace Add8
variable {p : ℕ} [Fact (p ≠ 0)] [Fact p.Prime]
variable [p_large_enough: Fact (p > 512)]

open Provable (field field2 fields)
open ByteLookup

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


def add8 (input : (Inputs p).var) := do
  let ⟨x, y⟩ := input
  let z ← subcircuit Add8Full.circuit { x, y, carry_in := const 0 }
  return z

def spec (input : (Inputs p).value) (z: F p) :=
  let ⟨x, y⟩ := input
  z.val = (x.val + y.val) % 256

def assumptions (input : (Inputs p).value) :=
  let ⟨x, y⟩ := input
  x.val < 256 ∧ y.val < 256

/--
  Compute the 8-bit addition of two numbers.
  Returns the sum.
-/
def circuit : FormalCircuit (F p) (Inputs p) (field (F p)) where
  main := add8
  assumptions := assumptions
  spec := spec
  soundness := by
    -- introductions
    rintro ctx env inputs inputs_var h_inputs as
    let ⟨x, y⟩ := inputs
    let ⟨x_var, y_var⟩ := inputs_var
    intro h_holds z

    -- characterize inputs
    have hx : x_var.eval_env env = x := by injection h_inputs
    have hy : y_var.eval_env env = y := by injection h_inputs

    -- simplify constraints hypothesis
    -- it's just the `subcircuit_soundness` of `Add8Full.circuit`
    dsimp at h_holds

    -- rewrite input and ouput values
    rw [hx, hy] at h_holds
    rw [←(by rfl : z = env ctx.offset)] at h_holds

    -- satisfy `Add8Full.assumptions` by using our own assumptions
    let ⟨ asx, asy ⟩ := as
    have as': Add8Full.assumptions { x, y, carry_in := 0 } := ⟨asx, asy, by tauto⟩
    specialize h_holds as'
    dsimp [ProvableType.from_values] at h_holds

    guard_hyp h_holds : Add8Full.circuit.spec { x, y, carry_in := 0 } z

    -- unfold `Add8Full` statements to show what the hypothesis is in our context
    dsimp [Add8Full.circuit, Add8Full.spec] at h_holds
    guard_hyp h_holds : z.val = (x.val + y.val + (0 : F p).val) % 256

    simp at h_holds
    exact h_holds

  completeness := by
    -- introductions
    rintro ctx inputs inputs_var h_inputs
    let ⟨x, y⟩ := inputs
    let ⟨x_var, y_var⟩ := inputs_var
    rintro as

    -- characterize inputs
    have hx : x_var.eval = x := by injection h_inputs
    have hy : y_var.eval = y := by injection h_inputs

    -- simplify assumptions and goal
    dsimp [assumptions] at as
    dsimp
    rw [hx, hy]

    -- the goal is just the `subcircuit_completeness` of `Add8Full.circuit`, i.e. the assumptions must hold
    -- simplify `Add8Full.assumptions` and prove them easily by using our own assumptions
    dsimp [Add8Full.circuit, Add8Full.assumptions]
    show x.val < 256 ∧ y.val < 256 ∧ (0 = 0 ∨ 0 = 1)
    have ⟨ asx, asy ⟩ := as
    exact ⟨ asx, asy, by tauto ⟩

end Add8
