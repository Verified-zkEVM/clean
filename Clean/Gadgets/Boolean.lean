import Clean.Circuit.Basic
import Clean.Utils.Field

section
variable {p : ℕ} [Fact p.Prime]

def assertBool (x: Expression (F p)) := do
  assertZero (x * (x - 1))

inductive Boolean (F: Type) where
  | private mk : Variable F → Boolean F

namespace Boolean
def var (b: Boolean (F p)) := Expression.var b.1

def witness (compute : Environment (F p) → F p) := do
  let x ← witnessVar compute
  assertBool (Expression.var x)
  return Boolean.mk x

instance : Coe (Boolean (F p)) (Expression (F p)) where
  coe x := x.var

/--
Asserts that x = 0 ∨ x = 1 by adding the constraint x * (x - 1) = 0
-/
def circuit : FormalAssertion (F p) field where
  main x := assertZero (x * (x - 1))

  Assumptions _ := True
  Spec x := x = 0 ∨ x = 1

  soundness := by simp_all [circuit_norm, mul_eq_zero, add_neg_eq_zero]
  completeness := by simp_all [circuit_norm, mul_eq_zero, add_neg_eq_zero]

end Boolean
