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

-- Test struct literal = struct variable with manual cases
theorem test_manual_cases_works {F : Type} [Field F] (input : TestInputs F)
    (h : TestInputs.mk 1 2 3 = input) : 
    input.x = 1 := by
  cases input with
  | mk x y z =>
    -- Now h is: TestInputs.mk 1 2 3 = TestInputs.mk x y z
    split_struct_eq
    -- h should be: 1 = x ∧ 2 = y ∧ 3 = z
    exact h.1.symm

-- Test if automatic cases works
theorem test_automatic_cases {F : Type} [Field F] (input : TestInputs F)
    (h : TestInputs.mk 1 2 3 = input) : 
    input.x = 1 := by
  split_struct_eq
  -- The tactic should apply cases on input automatically
  -- After cases and simp, h should be: 1 = x ∧ 2 = y ∧ 3 = z
  exact h.1.symm