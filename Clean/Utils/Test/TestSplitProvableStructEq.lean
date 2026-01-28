import Clean.Circuit
import Clean.Utils.Tactics

namespace TestSplitProvableStructEq

-- Test structure with ProvableStruct instance
structure TestInputs (F : Type) where
  x : F
  y : F
  z : F
deriving ProvableStruct

-- Structure without ProvableStruct instance
structure NonProvableStruct (F : Type) where
  a : F
  b : F

-- Test basic struct literal = struct literal
theorem test_struct_literal_eq_literal {F : Type} [Field F]
    (h : (TestInputs.mk 1 2 3 : TestInputs F) = TestInputs.mk 4 5 6) :
    (1 : F) = 4 := by
  split_provable_struct_eq
  -- Now h should be: 1 = 4 ∧ 2 = 5 ∧ 3 = 6
  exact h.1

-- Test struct literal = struct variable
theorem test_struct_literal_eq_variable {F : Type} [Field F] (input : TestInputs F)
    (h : TestInputs.mk 1 2 3 = input) :
    input.x = 1 := by
  split_provable_struct_eq
  -- The tactic should apply cases on input and then split the equality
  -- Now we should have h : 1 = x ∧ 2 = y ∧ 3 = z
  exact h.1.symm

-- Test struct variable = struct literal
theorem test_struct_variable_eq_literal {F : Type} [Field F] (input : TestInputs F)
    (h : input = TestInputs.mk 1 2 3) :
    input.x = 1 := by
  split_provable_struct_eq
  -- The tactic should apply cases on input and then split the equality
  -- Now we should have h : x = 1 ∧ y = 2 ∧ z = 3
  exact h.1

-- Test multiple struct equalities
theorem test_multiple_equalities {F : Type} [Field F] (input1 input2 : TestInputs F)
    (h1 : TestInputs.mk 1 2 3 = input1)
    (h2 : input2 = TestInputs.mk 4 5 6) :
    input1.x = 1 ∧ input2.y = 5 := by
  split_provable_struct_eq
  -- Both input1 and input2 should be destructured via cases
  -- h1 becomes: 1 = x₁ ∧ 2 = y₁ ∧ 3 = z₁
  -- h2 becomes: x₂ = 4 ∧ y₂ = 5 ∧ z₂ = 6
  constructor
  · exact h1.1.symm
  · exact h2.2.1

-- Test with conjunctions containing struct equalities
theorem test_conjunction_with_struct_eq {F : Type} [Field F] (input : TestInputs F) (x : F)
    (h : TestInputs.mk 1 2 3 = input ∧ x = 7) :
    input.x = 1 ∧ x = 7 := by
  split_provable_struct_eq
  -- The struct equality inside the conjunction should now be handled
  -- After cases on input and splitting, h.1 should be: 1 = x₁ ∧ 2 = y₁ ∧ 3 = z₁
  -- and h.2 should remain: x = 7
  constructor
  · exact h.1.1.symm
  · exact h.2

-- Test with nested conjunctions and multiple struct equalities
theorem test_nested_conjunctions {F : Type} [Field F] (input1 input2 : TestInputs F) (x : F)
    (h : (TestInputs.mk 1 2 3 = input1 ∧ x = 7) ∧ input2 = TestInputs.mk 4 5 6) :
    input1.x = 1 ∧ input2.y = 5 := by
  split_provable_struct_eq
  -- Both struct equalities should be found and handled
  constructor
  · exact h.1.1.1.symm
  · exact h.2.2.1

-- Test with some equation to be split and some not to be split
theorem test_with_base_and_non_base {F : Type} [Field F] (input1 input2 input3 : TestInputs F) (x : F)
    (h : (TestInputs.mk 1 2 3 = input1 ∧ x = 7) ∧ input2 = input3) :
    input1.x = 1 := by
  split_provable_struct_eq
  -- input2 = input3 should be intact
  have : input2 = input3 := h.2
  exact h.1.1.1.symm

end TestSplitProvableStructEq
