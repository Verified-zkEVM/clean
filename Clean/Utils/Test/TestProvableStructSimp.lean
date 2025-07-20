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

-- Test 1: Both split and decompose needed
theorem test_split_and_decompose {F : Type} [Field F] (input : TestInputs F)
    (h : TestInputs.mk 1 2 3 = input) :
    input.x = 1 := by
  provable_struct_simp
  -- Should apply split_provable_struct_eq (with automatic cases) then be done
  exact h.1.symm

-- Test 2: Multiple equalities and projections
theorem test_multiple_operations {F : Type} [Field F] (a b : TestInputs F)
    (h1 : a = TestInputs.mk 1 2 3)
    (h2 : b = TestInputs.mk 4 5 6) :
    a.x + b.y = 6 := by
  provable_struct_simp
  -- Should decompose both a and b, and split both equalities
  simp only [h1.1, h2.2]
  norm_num

-- Test 3: Nested structures
theorem test_nested_structures {F : Type} [Field F] (nested : NestedInputs F)
    (h : nested.first = TestInputs.mk 1 2 3 ∧ nested.second.x = 4) :
    nested.first.x + nested.second.x = 5 := by
  provable_struct_simp
  -- Should decompose nested, then split the equality in h.1
  -- After decomposition, h becomes about the decomposed components
  simp only [h.1.1, h.2]
  norm_num

-- Test 4: Conjunction with multiple struct equalities
theorem test_complex_conjunction {F : Type} [Field F] (a b : TestInputs F) (x : F)
    (h : (a = TestInputs.mk 1 2 3 ∧ x = 7) ∧ b = TestInputs.mk 4 5 6) :
    a.x + b.y + x = 13 := by
  provable_struct_simp
  -- Should find and split both struct equalities, decompose a and b
  -- After decomposition and splitting, we have the field values
  simp only [h.1.1.1, h.2.2.1, h.1.2]
  norm_num

-- Test 5: Already normalized - tactic should do nothing harmful
theorem test_already_normalized {F : Type} [Field F] (x y z : F)
    (h : x = 1 ∧ y = 2 ∧ z = 3) :
    x + y + z = 6 := by
  provable_struct_simp
  -- Nothing to do, should leave everything as is
  simp only [h.1, h.2.1, h.2.2]
  norm_num

-- Test 6: Mix of everything
theorem test_kitchen_sink {F : Type} [Field F]
    (a : TestInputs F) (nested : NestedInputs F) (c : TestInputs F)
    (h1 : a = TestInputs.mk 1 2 3)
    (h2 : nested.first.x = 4 ∧ nested.second = c)
    (h3 : c.y = 5) :
    a.x + nested.first.x + c.y = 10 := by
  provable_struct_simp
  -- Should:
  -- 1. Decompose a (from h1), nested (from h2), and c (from h3)
  -- 2. Split h1 into field equalities
  -- 3. Split h2.2 into field equalities
  simp only [h1.1, h2.1, h3]
  norm_num

-- Test 7: Verify the tactic terminates (no infinite loop)
theorem test_termination {F : Type} [Field F] (a b : TestInputs F)
    (h : a = b) :
    a.x = b.x := by
  provable_struct_simp
  -- Should decompose both a and b, split h, then stop
  exact h.1
