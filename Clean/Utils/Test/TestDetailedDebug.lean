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

-- Test to understand anonymous constructor syntax
theorem test_anonymous_syntax {F : Type} [Field F] : 
    { x := 1, y := 2, z := 3 : TestInputs F } = TestInputs.mk 1 2 3 := by
  rfl

-- Test the lemma directly
theorem test_lemma_direct {F : Type} [Field F] : 
    (TestInputs.mk 1 2 3 = TestInputs.mk (4 : F) 5 6) ↔ (1 = 4 ∧ 2 = 5 ∧ 3 = 6) := by
  exact TestInputs.mk.injEq

-- Test if simp knows about the lemma
theorem test_simp_knows_lemma {F : Type} [Field F]
    (h : TestInputs.mk 1 2 3 = TestInputs.mk (4 : F) 5 6) : 
    (1 : F) = 4 := by
  simp only [TestInputs.mk.injEq] at h
  exact h.1

-- Now test why it doesn't work with anonymous syntax
theorem test_why_not_working {F : Type} [Field F]
    (h : { x := 1, y := 2, z := 3 : TestInputs F } = { x := 4, y := 5, z := 6 }) : 
    (1 : F) = 4 := by
  -- First, let's check what h actually is
  have h' : TestInputs.mk 1 2 3 = TestInputs.mk 4 5 6 := h
  -- Now apply the lemma to h'
  simp only [TestInputs.mk.injEq] at h'
  exact h'.1