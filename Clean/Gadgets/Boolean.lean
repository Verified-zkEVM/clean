import Clean.Circuit.Basic
import Clean.Utils.Field

section
variable {p : ℕ} [Fact p.Prime]

inductive Boolean (F: Type) where
  | private mk : Variable F → Boolean F

namespace Boolean
def witness (compute : Environment (F p) → F p) := do
  let x ← witnessVar compute
  assertZero (var x * (var x - 1))
  return Boolean.mk x

def var (b: Boolean (F p)) := Expression.var b.1

instance : Coe (Boolean (F p)) (Expression (F p)) where
  coe x := x.var

theorem equiv : ∀ {x: F p},
    x * (x + -1) = 0 ↔ x = 0 ∨ x = 1 := by
  intro x; rw [mul_eq_zero, add_neg_eq_zero]

/--
Asserts that x = 0 ∨ x = 1 by adding the constraint x * (x - 1) = 0
-/
@[circuit_norm]
def assertBool : FormalAssertion (F p) field where
  main (x : Expression (F p)) := assertZero (x * (x - 1))
  Assumptions _ := True
  Spec (x : F p) := x = 0 ∨ x = 1

  soundness := by simp_all only [circuit_norm, equiv]
  completeness := by simp_all only [circuit_norm, equiv]
end Boolean

export Boolean (assertBool)
