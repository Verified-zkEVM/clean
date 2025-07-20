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

-- Debug test to see what happens with anonymous constructor syntax
theorem debug_anonymous_constructor {F : Type} [Field F]
    (h : { x := 1, y := 2, z := 3 : TestInputs F } = { x := 4, y := 5, z := 6 }) : 
    (1 : F) = 4 := by
  -- Let's see what simp does with TestInputs.mk.injEq
  simp only [TestInputs.mk.injEq] at h
  -- Now h should be: 1 = 4 ∧ 2 = 5 ∧ 3 = 6
  exact h.1

-- Test with explicit constructor syntax
theorem debug_explicit_constructor {F : Type} [Field F]
    (h : TestInputs.mk 1 2 3 = TestInputs.mk (4 : F) 5 6) : 
    (1 : F) = 4 := by
  simp only [TestInputs.mk.injEq] at h
  exact h.1