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

structure NestedInputs (F : Type) where
  first : TestInputs F
  second : TestInputs F

instance : ProvableStruct NestedInputs where
  components := [TestInputs, TestInputs]
  toComponents := fun { first, second } => .cons first (.cons second .nil)
  fromComponents := fun (.cons first (.cons second .nil)) => { first := first, second := second }

-- Test 1: Basic split - struct literal equality
theorem test_split_equality {F : Type} [Field F]
    (h : TestInputs.mk 1 2 3 = TestInputs.mk (4 : F) 5 6) :
    (1 : F) = 4 := by
  provable_struct_simp
  exact h.1

-- Test 2: Basic decompose - struct variable with projections
theorem test_decompose_variable {F : Type} [Field F] (input : TestInputs F) :
    input.x + input.y = input.y + input.x := by
  provable_struct_simp
  ring

-- Test 3: Combined - struct literal = variable (requires automatic cases)
theorem test_split_with_variable {F : Type} [Field F] (input : TestInputs F)
    (h : TestInputs.mk 1 2 3 = input) :
    input.x = 1 := by
  provable_struct_simp
  exact h.1.symm

-- Test 4: Struct equality inside conjunction
theorem test_conjunction {F : Type} [Field F] (input : TestInputs F) (w : F)
    (h : TestInputs.mk 1 2 3 = input ∧ w = 7) :
    input.x + w = 8 := by
  provable_struct_simp
  simp only [h.1.1.symm, h.2]
  norm_num

-- Test 5: Multiple struct equalities in nested conjunctions
theorem test_complex_conjunction {F : Type} [Field F] (a b : TestInputs F) (x : F)
    (h : (a = TestInputs.mk 1 2 3 ∧ x = 7) ∧ b = TestInputs.mk 4 5 6) :
    a.x + b.y + x = 13 := by
  provable_struct_simp
  simp only [h.1.1.1, h.2.2.1, h.1.2]
  norm_num

-- Test 6: Variable = variable equality
theorem test_variable_equality {F : Type} [Field F] (a b : TestInputs F)
    (h : a = b) :
    a.x = b.x := by
  provable_struct_simp
  exact h.1

-- Test 7: Nested structures
theorem test_nested_structures {F : Type} [Field F] (nested : NestedInputs F)
    (h : nested.first = TestInputs.mk 1 2 3 ∧ nested.second.x = 4) :
    nested.first.x + nested.second.x = 5 := by
  provable_struct_simp
  simp only [h.1.1, h.2]
  norm_num

-- Test 8: Complex scenario with multiple operations needed
theorem test_kitchen_sink {F : Type} [Field F]
    (a : TestInputs F) (nested : NestedInputs F) (c : TestInputs F)
    (h1 : a = TestInputs.mk 1 2 3)
    (h2 : nested.first.x = 4 ∧ nested.second = c)
    (h3 : c.y = 5) :
    a.x + nested.first.x + c.y = 10 := by
  provable_struct_simp
  simp only [h1.1, h2.1, h3]
  norm_num

-- Test 9: Already normalized - tactic should do nothing harmful
set_option linter.unusedTactic false in
theorem test_already_normalized {F : Type} [Field F] (x y z : F)
    (h : x = 1 ∧ y = 2 ∧ z = 3) :
    x + y + z = 6 := by
  provable_struct_simp
  simp only [h.1, h.2.1, h.2.2]
  norm_num

-- Test 10: Verify termination (no infinite loop)
theorem test_termination {F : Type} [Field F] (a b : TestInputs F)
    (h : a = b) :
    a.x = b.x := by
  provable_struct_simp
  exact h.1
