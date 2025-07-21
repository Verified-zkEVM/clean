import Clean.Utils.Tactics.DecomposeProvablePair
import Clean.Circuit.Provable
import Clean.Utils.Field

namespace TestDecomposeProvablePair

variable {p : ℕ} [Fact p.Prime]

-- Test basic pair decomposition
example (input : F p × F p) (h : input.1 = 5) : input.2 + 5 = input.1 + input.2 := by
  decompose_provable_pair
  -- Now we should have input_fst and input_snd instead of input
  sorry

-- Test with fieldPair
example (input : fieldPair (F p)) (h : input.2 ≠ 0) : input.1 * input.2 ≠ 0 := by
  decompose_provable_pair
  sorry

-- Test with Prod.fst and Prod.snd
example (input : F p × F p) (h1 : Prod.fst input = 1) (h2 : Prod.snd input = 2) : 
    input.1 + input.2 = 3 := by
  decompose_provable_pair
  sorry

-- Test multiple pairs
example (a b : F p × F p) (h : a.1 = b.1) : a.2 = b.2 → a = b := by
  decompose_provable_pair
  sorry


-- Test nested pairs
example (input : (F p × F p) × F p) (h : input.1.1 = 5) : 
    input.1.2 + input.2 = input.1.1 + input.1.2 + input.2 - 5 := by
  decompose_provable_pair
  sorry

-- Test that pairs without projections are not decomposed
example (input : F p × F p) (other : F p × F p) (h : input = other) :
    input = other := by
  decompose_provable_pair
  exact h

-- Test interaction with goal
example (input : F p × F p) : input.1 + input.2 = input.2 + input.1 := by
  decompose_provable_pair
  ring

end TestDecomposeProvablePair