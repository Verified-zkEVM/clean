import Clean.Circuit.Basic
import Clean.Utils.Field
import Clean.Utils.Bool

open Clean

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

/--
Asserts that x is boolean by adding the constraint x * (x - 1) = 0
-/
@[circuit_norm]
def assertBool : FormalAssertion (F p) field where
  main (x : Expression (F p)) := assertZero (x * (x - 1))
  Assumptions _ := True
  Spec (x : F p) := IsBinary x

  soundness := by 
    simp_all only [circuit_norm]
    intro env input_var input h_eval h_constraint
    -- h_constraint : input * (input + -1) = 0
    rw [mul_eq_zero, add_neg_eq_zero] at h_constraint
    exact h_constraint
  completeness := by 
    simp_all only [circuit_norm]
    intro env input_var input h_eval h_spec
    -- h_spec : input = 0 ∨ input = 1
    rw [mul_eq_zero, add_neg_eq_zero]
    exact h_spec
end Boolean

export Boolean (assertBool)
