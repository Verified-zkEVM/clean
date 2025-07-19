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

-- Test theorem using the new tactic
theorem test_decompose_simple {F : Type} [Field F] (input : TestInputs F) :
    input.x + input.y + input.z = input.z + input.y + input.x := by
  decompose_provable_struct
  -- After decomposition, we should have x, y, z in context
  rename_i x y z
  -- input should no longer exist
  fail_if_success (exact input)
  -- x, y, z should exist
  have : F := x
  have : F := y
  have : F := z
  ring

-- Test with nested structures
structure NestedInputs (F : Type) where
  first : TestInputs F
  second : TestInputs F

instance : ProvableStruct NestedInputs where
  components := [TestInputs, TestInputs]
  toComponents := fun { first, second } => .cons first (.cons second .nil)
  fromComponents := fun (.cons first (.cons second .nil)) => { first, second }

theorem test_decompose_nested {F : Type} [Field F] (input : NestedInputs F) :
    input.first.x + input.second.y = input.second.y + input.first.x := by
  decompose_provable_struct
  -- This should decompose input into first and second
  rename_i first second
  -- input should no longer exist
  fail_if_success (exact input)
  -- first and second should exist
  have : TestInputs F := first
  have : TestInputs F := second
  ring

-- Test with multiple variables using automatic version
theorem test_decompose_multiple {F : Type} [Field F] (a : TestInputs F) (b : TestInputs F) :
    a.x + b.y = b.y + a.x := by
  decompose_provable_struct  -- This should decompose both a and b at once
  -- Now we should have 6 variables (3 from a, 3 from b)
  rename_i ax ay az bx b_y bz
  -- a and b should no longer exist
  fail_if_success (exact a)
  fail_if_success (exact b)
  -- All components should exist
  have : F := ax
  have : F := bx
  ring

-- Test with multiple variables using automatic version
theorem test_decompose_multiple_auto {F : Type} [Field F] (a : TestInputs F) (b : TestInputs F) :
    a.x + b.y = b.y + a.x := by
  decompose_provable_struct  -- This should decompose both a and b at once
  -- Now we should have x_1, y_1, z_1 from a and x, y, z from b
  rename_i ax ay az bx b_y bz
  -- a and b should no longer exist
  fail_if_success (exact a)
  fail_if_success (exact b)
  ring
-- Test automatic decomposition with mixed types
theorem test_decompose_mixed_auto {F : Type} [Field F] (a : TestInputs F) (b : NestedInputs F) :
    a.x + b.first.y = b.first.y + a.x := by
  decompose_provable_struct  -- This should decompose both a and b
  -- Now we should have x, y, z from a and first, second from b
  rename_i ax ay az bfirst bsecond
  -- a and b should no longer exist
  fail_if_success (exact a)
  fail_if_success (exact b)
  -- Components should exist with correct types
  have : F := ax
  have : TestInputs F := bfirst
  ring

-- Test decomposition finding variables through projections in hypotheses
theorem test_decompose_from_hypothesis {F : Type} [Field F] (input : TestInputs F)
    (h : input.x = 5) : input.y + input.z = input.z + input.y := by
  decompose_provable_struct  -- This should find and decompose input via the projection in h
  -- Now we should have x, y, z in context with h : x = 5
  rename_i x y z
  -- input should no longer exist
  fail_if_success (exact input)
  -- h should now be about x, not input.x
  have : x = 5 := h
  ring

-- Test decomposition with projections in multiple hypotheses
theorem test_decompose_multiple_hypotheses {F : Type} [Field F] (a : TestInputs F) (b : TestInputs F)
    (h1 : a.x = b.y) (h2 : b.z = 10) : a.x = a.x := by
  decompose_provable_struct  -- This should find and decompose both a and b
  rename_i bx b_y bz ax ay az
  -- a and b should no longer exist
  fail_if_success (exact a)
  fail_if_success (exact b)
  -- h1 and h2 should be updated
  have : ax = b_y := h1
  have : bz = 10 := h2
  ring

-- Test decomposition with nested projections in hypothesis
theorem test_decompose_nested_hypothesis {F : Type} [Field F] (input : NestedInputs F)
    (h : input.first.x = 7) : input.second.y = input.second.y := by
  decompose_provable_struct  -- This should find and decompose input
  rename_i first second
  -- input should no longer exist
  fail_if_success (exact input)
  -- first and second should exist
  have : TestInputs F := first
  have : TestInputs F := second
  -- h should be updated to use first.x
  have : first.x = 7 := h
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
  rename_i ax ay az bx b_y bz
  -- a and b should no longer exist
  fail_if_success (exact a)
  fail_if_success (exact b)
  -- But c should still exist!
  have : TestInputs F := c
  ring
