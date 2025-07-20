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

-- Simple test: just split
theorem test_just_split {F : Type} [Field F]
    (h : TestInputs.mk 1 2 3 = TestInputs.mk (4 : F) 5 6) :
    (1 : F) = 4 := by
  provable_struct_simp
  exact h.1

-- Simple test: just decompose
theorem test_just_decompose {F : Type} [Field F] (input : TestInputs F) :
    input.x + input.y = input.y + input.x := by
  provable_struct_simp
  ring

-- Combined test: split and decompose
theorem test_split_and_decompose {F : Type} [Field F] (input : TestInputs F)
    (h : TestInputs.mk 1 2 3 = input) :
    input.x = 1 := by
  provable_struct_simp
  -- input is decomposed to x, y, z
  -- h is split to 1 = x ∧ 2 = y ∧ 3 = z
  exact h.1.symm

-- Test with conjunction
theorem test_conjunction {F : Type} [Field F] (input : TestInputs F) (w : F)
    (h : TestInputs.mk 1 2 3 = input ∧ w = 7) :
    input.x + w = 8 := by
  provable_struct_simp
  -- input is decomposed, h.1 is split
  simp only [h.1.1.symm, h.2]
  norm_num

-- Test multiple variables with equality
theorem test_multiple_vars_eq {F : Type} [Field F] (a b : TestInputs F)
    (h : a = b) :
    a.x = b.x := by
  provable_struct_simp
  -- After decomposition and splitting, h should be split into field equalities
  exact h.1

-- Test multiple variables with projections
theorem test_multiple_vars_proj {F : Type} [Field F] (a b : TestInputs F)
    (h : a.x = b.x ∧ a.y = b.y) :
    a.x + a.y = b.x + b.y := by
  provable_struct_simp
  -- This decomposes both a and b
  simp only [h.1, h.2]

-- Test that already-normalized case doesn't break
theorem test_already_normal {F : Type} [Field F] (x y z : F)
    (h : x = 1 ∧ y = 2 ∧ z = 3) :
    x + y + z = 6 := by
  provable_struct_simp
  simp only [h.1, h.2.1, h.2.2]
  norm_num