import Clean.Utils.Tactics
import Clean.Circuit.Provable

-- Test structures with ProvableStruct instances
structure TestInputs (F : Type) where
  x : F
  y : F
  z : F

instance : ProvableStruct TestInputs where
  components := [field, field, field]
  toComponents := fun { x, y, z } => .cons x (.cons y (.cons z .nil))
  fromComponents := fun (.cons x (.cons y (.cons z .nil))) => { x, y, z }

-- Test 1: Split struct equality
theorem test_split_equality {F : Type} [Field F]
    (h : TestInputs.mk 1 2 3 = TestInputs.mk (4 : F) 5 6) :
    (1 : F) = 4 := by
  provable_struct_simp
  exact h.1

-- Test 2: Decompose struct variable
theorem test_decompose_variable {F : Type} [Field F] (input : TestInputs F) :
    input.x + input.y = input.y + input.x := by
  provable_struct_simp
  ring

-- Test 3: Combined - split equality with struct variable
theorem test_split_with_variable {F : Type} [Field F] (input : TestInputs F)
    (h : TestInputs.mk 1 2 3 = input) :
    input.x = 1 := by
  provable_struct_simp
  -- First split_provable_struct_eq applies cases and splits h
  -- Then decompose is not needed since cases already happened
  exact h.1.symm

-- Test 4: Conjunction with struct equality
theorem test_conjunction {F : Type} [Field F] (input : TestInputs F) (w : F)
    (h : TestInputs.mk 1 2 3 = input ∧ w = 7) :
    input.x + w = 8 := by
  provable_struct_simp
  -- split_provable_struct_eq finds the equality in the conjunction
  simp only [h.1.1.symm, h.2]
  norm_num

-- Test 5: Multiple struct equalities in conjunctions
theorem test_multiple_equalities {F : Type} [Field F] (a b : TestInputs F)
    (h : a = TestInputs.mk 1 2 3 ∧ b = TestInputs.mk 4 5 6) :
    a.x + b.y = 6 := by
  provable_struct_simp
  -- Both equalities are found and split, a and b are decomposed
  simp only [h.1.1, h.2.2]
  norm_num

-- Test 6: Nested structure
structure NestedInputs (F : Type) where
  first : TestInputs F
  second : TestInputs F

instance : ProvableStruct NestedInputs where
  components := [TestInputs, TestInputs]
  toComponents := fun { first, second } => .cons first (.cons second .nil)
  fromComponents := fun (.cons first (.cons second .nil)) => { first := first, second := second }

theorem test_nested {F : Type} [Field F] (nested : NestedInputs F)
    (h : nested.first = TestInputs.mk 1 2 3) :
    nested.first.x = 1 := by
  provable_struct_simp
  -- decompose finds nested.first projection and decomposes nested
  -- split finds and splits the equality
  exact h.1

-- Test 7: Already normalized case (should do nothing)
theorem test_already_normal {F : Type} [Field F] (x y z : F)
    (h : x = 1 ∧ y = 2 ∧ z = 3) :
    x + y + z = 6 := by
  try provable_struct_simp  -- This does nothing, which is fine
  simp only [h.1, h.2.1, h.2.2]
  norm_num