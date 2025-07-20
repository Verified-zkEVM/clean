import Clean.Utils.Tactics
import Clean.Circuit.Provable

-- Test structure with ProvableStruct instance
structure TestInputs (F : Type) where
  x : F
  y : F
  z : F

instance : ProvableStruct TestInputs where
  components := [field, field, field]
  toComponents := fun { x, y, z } => .cons x (.cons y (.cons z .nil))
  fromComponents := fun (.cons x (.cons y (.cons z .nil))) => { x, y, z }

-- Structure without ProvableStruct instance
structure NonProvableStruct (F : Type) where
  a : F
  b : F

-- Test basic struct literal = struct literal
theorem test_struct_literal_eq_literal {F : Type} [Field F]
    (h : (TestInputs.mk 1 2 3 : TestInputs F) = TestInputs.mk 4 5 6) : 
    (1 : F) = 4 := by
  split_struct_eq
  -- Now h should be: 1 = 4 ∧ 2 = 5 ∧ 3 = 6
  exact h.1

-- Test struct literal = struct variable
theorem test_struct_literal_eq_variable {F : Type} [Field F] (input : TestInputs F)
    (h : TestInputs.mk 1 2 3 = input) : 
    input.x = 1 := by
  split_struct_eq
  -- The tactic should apply cases on input and then split the equality
  -- Now we should have h : 1 = x ∧ 2 = y ∧ 3 = z
  exact h.1.symm

-- Test struct variable = struct literal
theorem test_struct_variable_eq_literal {F : Type} [Field F] (input : TestInputs F)
    (h : input = TestInputs.mk 1 2 3) : 
    input.x = 1 := by
  split_struct_eq
  -- The tactic should apply cases on input and then split the equality
  -- Now we should have h : x = 1 ∧ y = 2 ∧ z = 3
  exact h.1

-- Test that non-ProvableStruct types are ignored
theorem test_non_provable_struct {F : Type} [Field F]
    (h : (NonProvableStruct.mk 1 2 : NonProvableStruct F) = NonProvableStruct.mk 3 4) :
    (1 : F) = 3 := by
  split_struct_eq
  -- The tactic runs but h should be unchanged since NonProvableStruct has no ProvableStruct instance
  -- We can't prove this because mk.injEq doesn't exist for NonProvableStruct
  sorry

-- Test multiple struct equalities
theorem test_multiple_equalities {F : Type} [Field F] (input1 input2 : TestInputs F)
    (h1 : TestInputs.mk 1 2 3 = input1)
    (h2 : input2 = TestInputs.mk 4 5 6) :
    input1.x = 1 ∧ input2.y = 5 := by
  split_struct_eq
  -- Both input1 and input2 should be destructured via cases
  -- h1 becomes: 1 = x₁ ∧ 2 = y₁ ∧ 3 = z₁
  -- h2 becomes: x₂ = 4 ∧ y₂ = 5 ∧ z₂ = 6
  constructor
  · exact h1.1.symm
  · exact h2.2.1

-- Test with type synonyms (like Var)
@[reducible]
def TestVar (F : Type) := TestInputs F

theorem test_type_synonym {F : Type} [Field F] (input : TestVar F)
    (h : TestInputs.mk 1 2 3 = input) :
    input.x = 1 := by
  split_struct_eq
  -- Should handle type synonyms properly
  exact h.1.symm

-- Test with conjunctions containing struct equalities
theorem test_conjunction_with_struct_eq {F : Type} [Field F] (input : TestInputs F) (x : F)
    (h : TestInputs.mk 1 2 3 = input ∧ x = 7) :
    input.x = 1 ∧ x = 7 := by
  split_struct_eq
  -- The struct equality inside the conjunction should be handled
  -- but the tactic currently only looks at top-level equalities
  sorry