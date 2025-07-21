import Clean.Utils.Tactics.DecomposeProvablePair
import Clean.Circuit.Provable
import Clean.Utils.Field

namespace TestDecomposeProvablePair

variable {p : ℕ} [Fact p.Prime]

-- Test basic pair decomposition
example (input : F p × F p) (h : input.1 = 5) : input.2 + 5 = input.1 + input.2 := by
  decompose_provable_pair
  -- Now we should have input_fst and input_snd instead of input
  -- h is updated to: (input_fst, input_snd).1 = 5
  simp at h ⊢
  -- Now h : input_fst = 5
  rw [h]
  ring

-- Test with fieldPair
example (input : fieldPair (F p)) (h1 : input.1 ≠ 0) (h2 : input.2 ≠ 0) : input.1 * input.2 ≠ 0 := by
  decompose_provable_pair
  -- After decomposition, h1 and h2 reference the components
  simp at h1 h2 ⊢
  -- Now h1 : input_fst ≠ 0 and h2 : input_snd ≠ 0
  exact ⟨h1, h2⟩

-- Test with Prod.fst and Prod.snd
example (input : F p × F p) (h1 : Prod.fst input = 1) (h2 : Prod.snd input = 2) :
    input.1 + input.2 = 3 := by
  decompose_provable_pair
  simp at h1 h2 ⊢
  rw [h1, h2]
  norm_num

-- Test multiple pairs
example (a b : F p × F p) (h : a.1 = b.1) : a.2 = b.2 → a = b := by
  decompose_provable_pair
  simp at h ⊢
  intro h2
  constructor <;> assumption

-- Test nested pairs - currently not supported
example (input : (F p × F p) × F p) (h : input.1.1 = 5) :
    input.1.2 + input.2 = input.1.1 + input.1.2 + input.2 - 5 := by
  decompose_provable_pair
  sorry

-- Test that pairs without projections are not decomposed
example (input : F p × F p) (other : F p × F p) (h : input = other) :
    input = other := by
  decompose_provable_pair
  -- Since input and other don't appear in projections, they should still exist
  exact h

-- Test interaction with goal
example (input : F p × F p) : input.1 + input.2 = input.2 + input.1 := by
  decompose_provable_pair
  -- input appears in projections in the goal, so should be decomposed
  simp
  ring

-- Test selective decomposition
example (used unused : F p × F p) (h : used.1 = 5) : used.2 = unused.2 → used.1 + used.2 = 5 + unused.2 := by
  decompose_provable_pair
  -- Both 'used' and 'unused' appear in projections, so both get decomposed
  simp at h ⊢
  intro h2
  rw [← h2, h]

-- For now, skip ProvableStruct tests as they require more setup

-- Test that non-ProvableType pairs are not decomposed
section NonProvableTypeTests

-- Define a simple non-ProvableType pair
def SimplePair (α : Type) : Type := α × α

example (input : SimplePair ℕ) (h : input.1 = 5) : input.2 = input.1 → input = (5, 5) := by
  decompose_provable_pair
  -- SimplePair ℕ expands to ℕ × ℕ, but ℕ is not a Field type
  -- So the tactic won't decompose it
  intro heq
  cases input with | mk a b =>
  simp at h heq ⊢
  rw [h, heq, h]

-- Test with regular Prod that's not a field pair
example (input : ℕ × String) (h : input.1 = 5) : input.2 = "hello" → input = (5, "hello") := by
  decompose_provable_pair
  -- This is not decomposed since ℕ and String are different types
  intro heq
  cases input with | mk a b =>
  simp at h heq ⊢
  constructor <;> assumption

end NonProvableTypeTests

end TestDecomposeProvablePair
