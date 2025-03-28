import Clean.Circuit.Basic
import Clean.Utils.Field

section
variable {p : ℕ} [Fact p.Prime]

def assert_bool (x: Expression (F p)) := do
  assert_zero (x * (x - 1))

inductive Boolean (F: Type) where
  | private mk : (Variable F) → Boolean F

namespace Boolean
def var (b: Boolean (F p)) := Expression.var b.1

def witness (compute : Environment (F p) → F p) := do
  let x ← witness_var compute
  assert_bool x
  return Boolean.mk x

instance : Coe (Boolean (F p)) (Expression (F p)) where
  coe x := x.var

def spec (x: F p) := x = 0 ∨ x = 1

theorem equiv : ∀ {x: F p},
  x * (x + -1 * 1) = 0 ↔ x = 0 ∨ x = 1 :=
by
  intro x
  simp
  show x = 0 ∨ x + -1 = 0 ↔ x = 0 ∨ x = 1
  suffices x + -1 = 0 ↔ x = 1 by tauto
  constructor
  · intro (h : x + -1 = 0)
    show x = 1
    calc x
    _ = (x + -1) + 1 := by ring
    _ = 1 := by simp only [h, zero_add]
  · intro (h : x = 1)
    show x + -1 = 0
    simp only [h, add_neg_cancel]

open Provable (field)

/--
Asserts that x = 0 ∨ x = 1 by adding the constraint x * (x - 1) = 0
-/
def circuit : FormalAssertion (F p) field where
  main := assert_bool
  assumptions _ := True
  spec := spec

  soundness := by
    intro _ env x_var x hx _ h_holds
    change x_var.eval env = x at hx
    dsimp only [circuit_norm, assert_bool] at h_holds
    rw [hx] at h_holds
    apply equiv.mp h_holds

  completeness := by
    intro n env x_var _ x hx _ spec
    change x_var.eval env = x at hx
    dsimp only [circuit_norm, assert_bool]
    rw [hx]
    apply equiv.mpr spec
end Boolean
