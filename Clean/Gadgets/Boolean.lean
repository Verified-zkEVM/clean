import Clean.Circuit.Basic
import Clean.Utils.Field

section
variable {p : ℕ} [Fact p.Prime]

def assert_bool (x: Expression (F p)) := do
  assertZero (x * (x - 1))

inductive Boolean (F: Type) where
  | private mk : Variable F → Boolean F

namespace Boolean
def var (b: Boolean (F p)) := Expression.var b.1

def witness (compute : Environment (F p) → F p) := do
  let x ← witnessVar compute
  assert_bool (Expression.var x)
  return Boolean.mk x

instance : Coe (Boolean (F p)) (Expression (F p)) where
  coe x := x.var

def spec (x: F p) := x = 0 ∨ x = 1

theorem equiv : ∀ {x: F p},
    x * (x + -1) = 0 ↔ x = 0 ∨ x = 1 := by
  intro x; rw [mul_eq_zero, add_neg_eq_zero]

/--
Asserts that x = 0 ∨ x = 1 by adding the constraint x * (x - 1) = 0
-/
def circuit : FormalAssertion (F p) field where
  main (x : Expression (F p)) := assertZero (x * (x - 1))
  assumptions _ := True
  spec (x : F p) := x = 0 ∨ x = 1

  soundness := by simp_all only [circuit_norm, equiv]
  completeness := by simp_all only [circuit_norm, equiv]
end Boolean
