import Clean.Circuit.Basic
import Clean.Utils.Field

variable {p : ℕ} [Fact p.Prime]

/-- A predicate stating that a field element is boolean (0 or 1) -/
def IsBool (x : F p) : Prop := x = 0 ∨ x = 1

/-- IsBool is decidable -/
instance {x : F p} : Decidable (IsBool x) := inferInstanceAs (Decidable (x = 0 ∨ x = 1))

namespace IsBool

@[simp]
theorem zero : IsBool (0 : F p) := Or.inl rfl

@[simp]
theorem one : IsBool (1 : F p) := Or.inr rfl

/-- If x is boolean, then x.val < 2 -/
theorem val_lt_two {x : F p} (h : IsBool x) : x.val < 2 := by
  rcases h with h0 | h1
  · rw [h0]; simp only [ZMod.val_zero]; norm_num
  · rw [h1]; simp only [ZMod.val_one, Nat.one_lt_ofNat]

/-- If x is boolean, then x * x = x -/
theorem mul_self {x : F p} (h : IsBool x) : x * x = x := by
  rcases h with h0 | h1
  · rw [h0]; simp only [zero_mul, mul_zero]
  · rw [h1]; simp only [one_mul, mul_one]

/-- If x is boolean, then x * (x - 1) = 0 -/
theorem mul_sub_one {x : F p} (h : IsBool x) : x * (x - 1) = 0 := by
  rcases h with h0 | h1
  · rw [h0]; simp only [zero_mul, zero_sub]
  · rw [h1]; simp only [one_mul, sub_self]

/-- x is boolean iff x * (x - 1) = 0 -/
theorem iff_mul_sub_one {x : F p} : IsBool x ↔ x * (x - 1) = 0 := by
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

/-- If x and y are boolean, then x XOR y is boolean -/
theorem xor_is_bool {x y : F p} (hx : IsBool x) (hy : IsBool y) :
    IsBool (x + y - 2 * x * y) := by
  rcases hx with hx0 | hx1
  · simp only [hx0, zero_mul, mul_zero, sub_zero, zero_add, add_zero]
    exact hy
  · rcases hy with hy0 | hy1
    · simp_all
    · left
      simp only [hx1, hy1, one_mul, mul_one, one_add_one_eq_two]
      ring

/-- If x and y are boolean, then x AND y is boolean -/
theorem and_is_bool {x y : F p} (hx : IsBool x) (hy : IsBool y) :
    IsBool (x * y) := by
  rcases hx with hx0 | hx1
  · simp_all
  · simp_all

/-- If x and y are boolean, then x OR y is boolean -/
theorem or_is_bool {x y : F p} (hx : IsBool x) (hy : IsBool y) :
    IsBool (x + y - x * y) := by
  rcases hx with hx0 | hx1
  · simp only [hx0, zero_mul, zero_add, sub_zero]
    exact hy
  · rcases hy with hy0 | hy1
    · simp_all
    · simp_all

/-- If x is boolean, then NOT x is boolean -/
theorem not_is_bool {x : F p} (hx : IsBool x) :
    IsBool (1 + x - 2 * x) := by
  rcases hx with hx0 | hx1
  · simp_all
  · simp only [hx1]; norm_num

/-- If x and y are boolean, then NAND(x,y) is boolean -/
theorem nand_is_bool {x y : F p} (hx : IsBool x) (hy : IsBool y) :
    IsBool (1 - x * y) := by
  rcases hx with hx0 | hx1
  · simp [hx0, zero_mul, sub_zero]
  · simp only [hx1, one_mul]
    rcases hy with hy0 | hy1
    · simp_all
    · simp_all

/-- If x and y are boolean, then NOR(x,y) is boolean -/
theorem nor_is_bool {x y : F p} (hx : IsBool x) (hy : IsBool y) :
    IsBool (x * y + 1 - x - y) := by
  rcases hx with hx0 | hx1
  · rcases hy with hy0 | hy1
    · simp_all
    · simp_all
  · rcases hy with hy0 | hy1
    · simp_all
    · simp_all

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
