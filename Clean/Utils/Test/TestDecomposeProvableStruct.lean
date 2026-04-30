import Clean.Circuit
import Clean.Utils.Tactics

namespace TestDecomposeProvableStruct

-- Test structure with ProvableStruct instance
structure TestInputs (F : Type) where
  x : F
  y : F
  z : F
deriving ProvableStruct

-- Test theorem using the new tactic
theorem test_decompose_simple {F : Type} [Field F] (input : TestInputs F) :
    input.x + input.y + input.z = input.z + input.y + input.x := by
  decompose_provable_struct
  -- After decomposition, we should have input_x, input_y, input_z in context
  -- input should no longer exist
  fail_if_success (exact input)
  -- Field-based names should exist
  have : F := input_x
  have : F := input_y
  have : F := input_z
  ring

-- Test with nested structures
structure NestedInputs (F : Type) where
  first : TestInputs F
  second : TestInputs F
deriving ProvableStruct

theorem test_decompose_nested {F : Type} [Field F] (input : NestedInputs F) :
    input.first.x + input.second.y = input.second.y + input.first.x := by
  decompose_provable_struct
  -- This should decompose input into input_first and input_second
  -- input should no longer exist
  fail_if_success (exact input)
  -- Field-based names should exist
  have : TestInputs F := input_first
  have : TestInputs F := input_second
  ring

-- Test with multiple variables using automatic version
theorem test_decompose_multiple {F : Type} [Field F] (a : TestInputs F) (b : TestInputs F) :
    a.x + b.y = b.y + a.x := by
  decompose_provable_struct  -- This should decompose both a and b at once
  -- Now we should have 6 variables (3 from a, 3 from b)
  -- a and b should no longer exist
  fail_if_success (exact a)
  fail_if_success (exact b)
  -- All components should exist with field-based names
  have : F := a_x
  have : F := a_y
  have : F := a_z
  have : F := b_x
  have : F := b_y
  have : F := b_z
  ring

-- Test automatic decomposition with mixed types
theorem test_decompose_mixed_auto {F : Type} [Field F] (a : TestInputs F) (b : NestedInputs F) :
    a.x + b.first.y = b.first.y + a.x := by
  decompose_provable_struct  -- This should decompose both a and b
  -- Now we should have a_x, a_y, a_z from a and b_first, b_second from b
  -- a and b should no longer exist
  fail_if_success (exact a)
  fail_if_success (exact b)
  -- Components should exist with correct types
  have : F := a_x
  have : TestInputs F := b_first
  ring

-- Test decomposition finding variables through projections in hypotheses
theorem test_decompose_from_hypothesis {F : Type} [Field F] (input : TestInputs F)
    (h : input.x = 5) : input.y + input.z = input.z + input.y := by
  decompose_provable_struct  -- This should find and decompose input via the projection in h
  -- Now we should have input_x, input_y, input_z in context with h : input_x = 5
  -- input should no longer exist
  fail_if_success (exact input)
  -- h should now be about input_x, not input.x
  have : input_x = 5 := h
  ring

-- Test decomposition with projections in multiple hypotheses
theorem test_decompose_multiple_hypotheses {F : Type} [Field F] (a : TestInputs F) (b : TestInputs F)
    (h1 : a.x = b.y) (h2 : b.z = 10) : a.x = a.x := by
  decompose_provable_struct  -- This should find and decompose both a and b
  -- a and b should no longer exist
  fail_if_success (exact a)
  fail_if_success (exact b)
  -- h1 and h2 should be updated with field-based names
  have : a_x = b_y := h1
  have : b_z = 10 := h2
  ring

-- Test decomposition with nested projections in hypothesis
theorem test_decompose_nested_hypothesis {F : Type} [Field F] (input : NestedInputs F)
    (h : input.first.x = 7) : input.second.y = input.second.y := by
  decompose_provable_struct  -- This should find and decompose input
  -- input should no longer exist
  fail_if_success (exact input)
  -- Field-based names should exist
  have : TestInputs F := input_first
  have : TestInputs F := input_second
  -- h should be updated to use input_first.x
  have : input_first.x = 7 := h
  rfl

-- Test that variables without projections are not decomposed
theorem test_no_decompose_without_projection {F : Type} [Field F] (input : TestInputs F) :
    input = input := by
  fail_if_success decompose_provable_struct  -- This should fail because input doesn't appear in any projections
  -- input should still be intact, not decomposed
  have : TestInputs F := input  -- Verify input still exists
  rfl

-- Test selective decomposition: only variables with projections are decomposed
set_option linter.unusedVariables false in
theorem test_selective_decompose {F : Type} [Field F] (a : TestInputs F) (b : TestInputs F) (c : TestInputs F) :
    a.x + b.y = b.y + a.x := by
  -- Only a and b appear in projections, so only they should be decomposed
  -- c should remain intact
  decompose_provable_struct
  -- a and b should no longer exist
  fail_if_success (exact a)
  fail_if_success (exact b)
  -- But c should still exist!
  have : TestInputs F := c
  -- Field-based names should exist
  have : F := a_x
  have : F := b_y
  ring

section NoProjectionTests
-- Test cases where the tactic errors because projections are never used
-- decompose_provable_struct throws an error when no variables need decomposition

-- Test struct variable with no projections used
theorem test_no_projection_struct {F : Type} [Field F] (input : TestInputs F)
    (h : input = ⟨5, 3, 1⟩) :
    input = ⟨5, 3, 1⟩ := by
  fail_if_success decompose_provable_struct
  -- input should NOT be decomposed because no projections are used
  assumption

-- Test with multiple struct variables, none with projections
theorem test_multiple_no_projection {F : Type} [Field F]
    (a : TestInputs F) (b : TestInputs F) (c : TestInputs F)
    (ha : a = ⟨1, 2, 3⟩) (hb : b = ⟨4, 5, 6⟩) (hc : c = ⟨7, 8, 9⟩) :
    a = ⟨1, 2, 3⟩ ∧ b = ⟨4, 5, 6⟩ ∧ c = ⟨7, 8, 9⟩ := by
  fail_if_success decompose_provable_struct
  -- None should be decomposed
  exact ⟨ha, hb, hc⟩

-- Test where only the whole struct is used in operations
theorem test_whole_struct_equality {F : Type} [Field F]
    (x : TestInputs F) (y : TestInputs F) (h : x = y) :
    x = y := by
  fail_if_success decompose_provable_struct
  -- No decomposition should happen
  assumption

-- Test with struct used in function application (not projection)
def processStruct {F : Type} [Field F] (input : TestInputs F) : F :=
  input.x + input.y + input.z

theorem test_struct_in_function {F : Type} [Field F]
    (input : TestInputs F) (h : processStruct input = 10) :
    processStruct input = 10 := by
  fail_if_success decompose_provable_struct
  -- input should NOT be decomposed because it's used as a whole in processStruct
  assumption

-- Test with struct comparison
theorem test_struct_comparison {F : Type} [Field F]
    (a : TestInputs F) (b : TestInputs F) :
    a = b ↔ a = b := by
  fail_if_success decompose_provable_struct
  -- No decomposition should happen
  rfl

-- Test with struct comparison
theorem test_equality_not_triggar {F : Type} [Field F]
    (a : TestInputs F) (_ : a = {x := 1, y := 2, z := 4}) :
    a = a := by
  fail_if_success decompose_provable_struct
  rfl

end NoProjectionTests

end TestDecomposeProvableStruct
