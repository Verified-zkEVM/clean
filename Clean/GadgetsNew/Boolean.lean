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

open Circuit
open Expression

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

theorem dsimp_equiv : ∀ x: F p,
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

theorem equiv : ∀ x: F p,
  constraints_hold_default (assert_bool (const x)) ↔ spec x
:= by
  -- simplify
  dsimp
  show ∀ (x : F p), x * (x + -1 * 1) = 0 ↔ spec x

  -- proof
  exact dsimp_equiv
end Boolean
