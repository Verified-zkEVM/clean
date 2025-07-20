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

-- Test what happens step by step
theorem test_manual_steps {F : Type} [Field F]
    (h : { x := 1, y := 2, z := 3 : TestInputs F } = { x := 4, y := 5, z := 6 }) : 
    (1 : F) = 4 := by
  -- Step 1: Check if TestInputs.mk.injEq exists and can be applied
  have lem := @TestInputs.mk.injEq F 1 2 3 4 5 6
  -- Step 2: Apply it to h
  rw [lem] at h
  -- Now h should be: 1 = 4 ∧ 2 = 5 ∧ 3 = 6
  exact h.1

-- Test with our tactic
theorem test_with_tactic {F : Type} [Field F]
    (h : { x := 1, y := 2, z := 3 : TestInputs F } = { x := 4, y := 5, z := 6 }) : 
    (1 : F) = 4 := by
  split_struct_eq
  -- Let's see what happened to h
  trace "{h}"
  -- Try manual simp to see if it works
  simp only [TestInputs.mk.injEq] at h
  trace "After manual simp: {h}"
  exact h.1