import Clean.Circuit.Basic
import Clean.Utils.Field

namespace Clean

variable {p : ℕ} [Fact p.Prime]

/-- A predicate stating that a field element is binary (0 or 1) -/
def IsBinary (x : F p) : Prop := x = 0 ∨ x = 1

/-- IsBinary is decidable -/
instance {x : F p} : Decidable (IsBinary x) := inferInstanceAs (Decidable (x = 0 ∨ x = 1))

namespace IsBinary

@[simp]
theorem zero : IsBinary (0 : F p) := Or.inl rfl

@[simp]
theorem one : IsBinary (1 : F p) := Or.inr rfl

/-- If x is binary, then x.val < 2 -/
theorem val_lt_two {x : F p} (h : IsBinary x) : x.val < 2 := by
  rcases h with h0 | h1
  · rw [h0]; simp only [ZMod.val_zero]; norm_num
  · rw [h1]; simp only [ZMod.val_one, Nat.one_lt_ofNat]

/-- If x is binary, then x * x = x -/
theorem mul_self {x : F p} (h : IsBinary x) : x * x = x := by
  rcases h with h0 | h1
  · rw [h0]; simp only [zero_mul, mul_zero]
  · rw [h1]; simp only [one_mul, mul_one]

/-- If x is binary, then x * (x - 1) = 0 -/
theorem mul_sub_one {x : F p} (h : IsBinary x) : x * (x - 1) = 0 := by
  rcases h with h0 | h1
  · rw [h0]; simp only [zero_mul, zero_sub]
  · rw [h1]; simp only [one_mul, sub_self]

/-- x is binary iff x * (x - 1) = 0 -/
theorem iff_mul_sub_one {x : F p} : IsBinary x ↔ x * (x - 1) = 0 := by
  constructor
  · exact mul_sub_one
  · intro h
    have : x = 0 ∨ x - 1 = 0 := by
      rw [mul_eq_zero] at h
      exact h
    rcases this with h0 | h1
    · left; exact h0
    · right
      exact sub_eq_zero.mp h1

/-- If x and y are binary, then x XOR y is binary -/
theorem xor_is_binary {x y : F p} (hx : IsBinary x) (hy : IsBinary y) :
    IsBinary (x + y - 2 * x * y) := by
  rcases hx with hx0 | hx1
  · simp only [hx0, zero_mul, mul_zero, sub_zero, zero_add, add_zero]
    exact hy
  · rcases hy with hy0 | hy1
    · simp_all
    · left
      simp only [hx1, hy1, one_mul, mul_one, one_add_one_eq_two]
      ring

/-- If x and y are binary, then x AND y is binary -/
theorem and_is_binary {x y : F p} (hx : IsBinary x) (hy : IsBinary y) :
    IsBinary (x * y) := by
  rcases hx with hx0 | hx1
  · simp_all
  · simp_all

/-- If x and y are binary, then x OR y is binary -/
theorem or_is_binary {x y : F p} (hx : IsBinary x) (hy : IsBinary y) :
    IsBinary (x + y - x * y) := by
  rcases hx with hx0 | hx1
  · simp only [hx0, zero_mul, zero_add, sub_zero]
    exact hy
  · rcases hy with hy0 | hy1
    · simp_all
    · simp_all

/-- If x is binary, then NOT x is binary -/
theorem not_is_binary {x : F p} (hx : IsBinary x) :
    IsBinary (1 + x - 2 * x) := by
  rcases hx with hx0 | hx1
  · simp_all
  · simp only [hx1]; norm_num

/-- If x and y are binary, then NAND(x,y) is binary -/
theorem nand_is_binary {x y : F p} (hx : IsBinary x) (hy : IsBinary y) :
    IsBinary (1 - x * y) := by
  rcases hx with hx0 | hx1
  · simp [hx0, zero_mul, sub_zero]
  · simp only [hx1, one_mul]
    rcases hy with hy0 | hy1
    · simp_all
    · simp_all

/-- If x and y are binary, then NOR(x,y) is binary -/
theorem nor_is_binary {x y : F p} (hx : IsBinary x) (hy : IsBinary y) :
    IsBinary (x * y + 1 - x - y) := by
  rcases hx with hx0 | hx1
  · rcases hy with hy0 | hy1
    · simp_all
    · simp_all
  · rcases hy with hy0 | hy1
    · simp_all
    · simp_all

end IsBinary

end Clean

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

  soundness := by simp_all only [circuit_norm, IsBinary.iff_mul_sub_one, sub_eq_add_neg]
  completeness := by simp_all only [circuit_norm, IsBinary.iff_mul_sub_one, sub_eq_add_neg]
end Boolean

export Boolean (assertBool)
