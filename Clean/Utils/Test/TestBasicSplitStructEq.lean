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

-- Test basic struct literal = struct literal (should work)
theorem test_struct_literal_eq_literal {F : Type} [Field F]
    (h : TestInputs.mk 1 2 3 = TestInputs.mk (4 : F) 5 6) : 
    (1 : F) = 4 := by
  split_struct_eq
  -- Now h should be: 1 = 4 ∧ 2 = 5 ∧ 3 = 6
  exact h.1

-- Test with anonymous constructor syntax
theorem test_anonymous_constructor {F : Type} [Field F]
    (h : { x := 1, y := 2, z := 3 : TestInputs F } = { x := 4, y := 5, z := 6 }) : 
    (1 : F) = 4 := by
  split_struct_eq
  -- The tactic should still work because anonymous syntax desugars to TestInputs.mk
  exact h.1

-- Test struct literal = struct variable (with manual cases)
theorem test_struct_literal_eq_variable {F : Type} [Field F] (input : TestInputs F)
    (h : TestInputs.mk 1 2 3 = input) : 
    input.x = 1 := by
  cases input with
  | mk x y z =>
    split_struct_eq
    -- Now h should be: 1 = x ∧ 2 = y ∧ 3 = z
    exact h.1.symm