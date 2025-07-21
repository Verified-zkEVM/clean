import Clean.Utils.Tactics.DecomposeProvablePair
import Clean.Circuit.Provable
import Clean.Utils.Field

namespace TestDecomposeProvablePair

variable {p : ℕ} [Fact p.Prime]

-- Test basic pair decomposition
example (input : F p × F p) (h : input.1 = 5) : input.2 + 5 = input.1 + input.2 := by
  decompose_provable_pair
  -- Now we should have input_fst and input_snd instead of input
  -- input should no longer exist
  fail_if_success (exact input)
  -- input_fst and input_snd should exist
  have : F p := input_fst
  have : F p := input_snd
  -- h should now reference input_fst
  have : input_fst = 5 := h
  sorry

-- Test with fieldPair
example (input : fieldPair (F p)) (h : input.2 ≠ 0) : input.1 * input.2 ≠ 0 := by
  decompose_provable_pair
  -- input should no longer exist
  fail_if_success (exact input)
  -- input_fst and input_snd should exist
  have : F p := input_fst
  have : F p := input_snd
  -- h should now reference input_snd
  have : input_snd ≠ 0 := h
  sorry

-- Test with Prod.fst and Prod.snd
example (input : F p × F p) (h1 : Prod.fst input = 1) (h2 : Prod.snd input = 2) : 
    input.1 + input.2 = 3 := by
  decompose_provable_pair
  -- input should no longer exist
  fail_if_success (exact input)
  -- input_fst and input_snd should exist
  have : F p := input_fst
  have : F p := input_snd
  -- h1 and h2 should now reference input_fst and input_snd
  have : input_fst = 1 := h1
  have : input_snd = 2 := h2
  sorry

-- Test multiple pairs
example (a b : F p × F p) (h : a.1 = b.1) : a.2 = b.2 → a = b := by
  decompose_provable_pair
  -- Both a and b should be decomposed
  -- Original pairs should no longer exist
  fail_if_success (exact a)
  fail_if_success (exact b)
  -- All components should exist
  have : F p := a_fst
  have : F p := a_snd
  have : F p := b_fst
  have : F p := b_snd
  -- h should reference the new variables
  have : a_fst = b_fst := h
  sorry

-- Test nested pairs
example (input : (F p × F p) × F p) (h : input.1.1 = 5) : 
    input.1.2 + input.2 = input.1.1 + input.1.2 + input.2 - 5 := by
  decompose_provable_pair
  -- First decomposition should split outer pair
  fail_if_success (exact input)
  -- input_fst is a pair, input_snd is not
  have : F p × F p := input_fst
  have : F p := input_snd
  -- The tactic only decomposes variables that appear directly in projections
  -- After decomposition, input_fst doesn't appear in projections like input_fst.1
  -- It appears inside (input_fst, input_snd).1.1 which is different
  sorry

-- Test that pairs without projections are not decomposed
example (input : F p × F p) (other : F p × F p) (h : input = other) :
    input = other := by
  decompose_provable_pair
  -- Since input and other don't appear in projections, they should still exist
  have : F p × F p := input
  have : F p × F p := other
  exact h

-- Test interaction with goal
example (input : F p × F p) : input.1 + input.2 = input.2 + input.1 := by
  decompose_provable_pair
  -- input appears in projections in the goal, so should be decomposed
  fail_if_success (exact input)
  have : F p := input_fst
  have : F p := input_snd
  ring

-- Test selective decomposition
example (used unused : F p × F p) (h : used.1 = 5) : used.2 = unused.2 → used.1 + used.2 = 5 + unused.2 := by
  decompose_provable_pair
  -- Both 'used' and 'unused' appear in projections, so both get decomposed
  fail_if_success (exact used)
  fail_if_success (exact unused)
  -- All components should exist
  have : F p := used_fst
  have : F p := used_snd
  have : F p := unused_fst
  have : F p := unused_snd
  sorry

end TestDecomposeProvablePair