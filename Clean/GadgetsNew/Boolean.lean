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

def assert_bool (x: Expression (F p)) := do
  assert_zero (x * (x - 1))

inductive Boolean (F: Type) where
  | private mk : (Variable F) → Boolean F

namespace Boolean
def var (b: Boolean (F p)) := Expression.var b.1

def witness (compute : Unit → F p) := do
  let x ← witness_var compute
  assert_bool x
  return Boolean.mk x

instance : Coe (Boolean (F p)) (Expression (F p)) where
  coe x := x.var

def spec (x: F p) := x = 0 ∨ x = 1

theorem equiv : ∀ x: F p,
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
    _ = 1 := by simp [h]
  · intro (h : x = 1)
    show x + -1 = 0
    simp [h]

open Provable (field)

def circuit : FormalAssertion (F p) (field (F p)) where
  main := assert_bool
  assumptions _ := True
  spec := spec

  soundness := by
    intro ctx env x x_var hx _ h_holds
    change x_var.eval_env env = x at hx
    dsimp at h_holds
    rw [hx] at h_holds
    apply (equiv x).mp h_holds

  completeness := by
    intro ctx x x_var hx _ spec
    change x_var.eval = x at hx
    dsimp
    rw [hx]
    apply (equiv x).mpr spec
end Boolean
