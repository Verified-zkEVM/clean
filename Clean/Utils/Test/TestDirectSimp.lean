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

-- Test that simp with mk.injEq works directly
theorem test_direct_simp {F : Type} [Field F]
    (h : { x := 1, y := 2, z := 3 : TestInputs F } = { x := 4, y := 5, z := 6 }) : 
    (1 : F) = 4 := by
  -- Direct simp should work
  simp only [TestInputs.mk.injEq] at h
  exact h.1