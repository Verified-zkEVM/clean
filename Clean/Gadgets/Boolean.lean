import Clean.Circuit.Basic
import Clean.Utils.Field

/-- A predicate stating that an element is boolean (0 or 1) for any type with 0 and 1 -/
def IsBool {α : Type*} [Zero α] [One α] (x : α) : Prop := x = 0 ∨ x = 1

/-- IsBool is decidable for types with decidable equality -/
instance {α : Type*} [Zero α] [One α] [DecidableEq α] {x : α} : Decidable (IsBool x) :=
  inferInstanceAs (Decidable (x = 0 ∨ x = 1))

namespace IsBool

@[circuit_norm]
theorem zero {α : Type*} [Zero α] [One α] : IsBool (0 : α) := Or.inl rfl

@[circuit_norm]
theorem one {α : Type*} [Zero α] [One α] : IsBool (1 : α) := Or.inr rfl

/-- If x is boolean in a type with a < relation, then x < 2 (when 2 exists) -/
theorem lt_two {α : Type*} [Zero α] [One α] [Preorder α] [OfNat α 2]
    {x : α} (h : IsBool x) (h0 : (0 : α) < 2) (h1 : (1 : α) < 2) : x < 2 := by
  rcases h with h0' | h1'
  · rw [h0']; exact h0
  · rw [h1']; exact h1

/-- If x is boolean, then x * x = x -/
theorem mul_self {α : Type*} [MulZeroOneClass α] {x : α} (h : IsBool x) : x * x = x := by
  rcases h with h0 | h1
  · rw [h0]; simp only [mul_zero]
  · rw [h1]; simp only [mul_one]

/-- x is boolean iff x * (x - 1) = 0 -/
theorem iff_mul_sub_one {α : Type*} [Ring α] [NoZeroDivisors α] {x : α} :
    IsBool x ↔ x * (x - 1) = 0 := by
  rw [mul_eq_zero, sub_eq_zero, IsBool]

/-- For natural numbers, if x is boolean then x < 2 -/
theorem nat_lt_two {x : ℕ} (h : IsBool x) : x < 2 := by
  rcases h with h0 | h1
  · rw [h0]; norm_num
  · rw [h1]; norm_num

/-- For field elements, if x is boolean then x.val < 2 -/
theorem val_lt_two {p : ℕ} [Fact p.Prime] {x : F p} (h : IsBool x) : x.val < 2 := by
  rcases h with h0 | h1
  · rw [h0]; simp only [ZMod.val_zero]; norm_num
  · rw [h1]; simp only [ZMod.val_one, Nat.one_lt_ofNat]

/-- If x and y are boolean, then x AND y is boolean -/
theorem and_is_bool {α : Type*} [MulZeroOneClass α] {x y : α} (hx : IsBool x) (hy : IsBool y) :
    IsBool (x * y) := by
  rcases hx with hx0 | hx1
  · simp [hx0, mul_zero, zero]
  · simp [hx1, one_mul, hy]

/-- If x and y are boolean, then x OR y is boolean -/
theorem or_is_bool {α : Type*} [Ring α] {x y : α} (hx : IsBool x) (hy : IsBool y) :
    IsBool (x + y - x * y) := by
  rcases hx with hx0 | hx1
  · simp [hx0, zero_add, zero_mul, sub_zero, hy]
  · rcases hy with hy0 | hy1
    · simp [hx1, hy0, one_mul, mul_zero, add_zero, sub_zero, one]
    · simp [hx1, hy1, one_mul, mul_one, sub_self, one]

/-- If x is boolean, then NOT x is boolean -/
theorem not_is_bool {α : Type*} [Ring α] {x : α} (hx : IsBool x) :
    IsBool (1 + x - 2 * x) := by
  rcases hx with hx0 | hx1
  · simp [hx0, add_zero, zero_mul, sub_zero, one]
  · simp only [hx1]
    norm_num
    exact zero

/-- If x and y are boolean, then x XOR y is boolean -/
theorem xor_is_bool {α : Type*} [Ring α] {x y : α} (hx : IsBool x) (hy : IsBool y) :
    IsBool (x + y - 2 * x * y) := by
  rcases hx with hx0 | hx1
  · simp [hx0, zero_add, zero_mul, mul_zero, sub_zero, hy]
  · rcases hy with hy0 | hy1
    · simp [hx1, hy0, add_zero, one_mul, mul_zero, sub_zero, one]
    · simp only [hx1, hy1, one_mul, mul_one]
      norm_num
      exact zero

/-- If x and y are boolean, then NAND(x,y) is boolean -/
theorem nand_is_bool {α : Type*} [Ring α] {x y : α} (hx : IsBool x) (hy : IsBool y) :
    IsBool (1 - x * y) := by
  rcases hx with hx0 | hx1
  · simp [hx0, mul_zero, sub_zero, one]
  · rcases hy with hy0 | hy1
    · simp [hx1, hy0, one_mul, sub_zero, one]
    · simp [hx1, hy1, one_mul, sub_self, zero]

/-- If x and y are boolean, then NOR(x,y) is boolean -/
theorem nor_is_bool {α : Type*} [Ring α] {x y : α} (hx : IsBool x) (hy : IsBool y) :
    IsBool (x * y + 1 - x - y) := by
  rcases hx with hx0 | hx1
  · rcases hy with hy0 | hy1
    · simp [hx0, hy0, zero_mul, zero_add, sub_zero, one]
    · simp [hx0, hy1, zero_mul, zero_add, sub_self, zero]
  · rcases hy with hy0 | hy1
    · simp [hx1, hy0, one_mul, mul_zero, add_sub_cancel, sub_self, zero]
    · simp [hx1, hy1, one_mul]
      exact zero


end IsBool

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
  Spec (x : F p) := IsBool x

  soundness := by simp_all only [circuit_norm, IsBool.iff_mul_sub_one, sub_eq_add_neg]
  completeness := by simp_all only [circuit_norm, IsBool.iff_mul_sub_one, sub_eq_add_neg]
end Boolean

export Boolean (assertBool)
