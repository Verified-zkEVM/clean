import Clean.Utils.Tactics.SplitPairEq
import Clean.Utils.Tactics.ProvableSimp
import Clean.Circuit.Provable
import Clean.Utils.Field

set_option linter.unusedTactic false

namespace TestSplitPairEq

variable {p : ℕ} [Fact p.Prime]

-- Test basic pair literal = pair literal
example (h : ((5 : F p), (3 : F p)) = (4, 6)) : (5 : F p) = 4 := by
  split_pair_eq
  -- Now h should be: 5 = 4 ∧ 3 = 6
  exact h.1

-- Test pair literal = pair variable
example (x : F p × F p) (h : (5, 3) = x) : x.1 = 5 := by
  split_pair_eq
  -- x is destructured via rcases and h becomes: 5 = x_fst ∧ 3 = x_snd
  exact h.1.symm

-- Test pair variable = pair literal
example (x : F p × F p) (h : x = (5, 3)) : x.1 = 5 := by
  split_pair_eq
  -- x is destructured via rcases and h becomes: x_fst = 5 ∧ x_snd = 3
  exact h.1

-- Test with fieldPair
example (x : fieldPair (F p)) (h : (5, 3) = x) : x.1 = 5 := by
  split_pair_eq
  -- x is destructured and equality is split
  exact h.1.symm

-- Test with Var fieldPair
example (x : Var fieldPair (F p)) (h : (Expression.const 5, Expression.const 3) = x) :
    x.1 = Expression.const 5 := by
  split_pair_eq
  -- x is destructured and equality is split
  exact h.1.symm

-- Test multiple pair equalities
example (x y : F p × F p) (h1 : (1, 2) = x) (h2 : y = (3, 4)) :
    x.1 = 1 ∧ y.2 = 4 := by
  split_pair_eq
  -- Both x and y should be destructured
  exact ⟨h1.1.symm, h2.2⟩

-- Test pair equalities inside conjunctions
example (x : F p × F p) (h : (5, 3) = x ∧ x.1 + x.2 = 8) : x.1 = 5 := by
  split_pair_eq
  -- The pair equality inside the conjunction should be found and split
  exact h.1.1.symm

-- Test nested conjunctions
example (x y : F p × F p)
    (h : ((1, 2) = x ∧ x.1 ≠ 0) ∧ (y = (3, 4) ∧ y.2 ≠ 0)) :
    x.1 = 1 ∧ y.2 = 4 := by
  split_pair_eq
  -- Both pair equalities in nested conjunctions should be found
  exact ⟨h.1.1.1.symm, h.2.1.2⟩

-- Test with Expression pairs (should work due to isProvableTypeOrStructOrExpression)
example (x : Expression (F p) × Expression (F p))
    (h : (Expression.const 5, Expression.const 3) = x) :
    x.1 = Expression.const 5 := by
  split_pair_eq
  exact h.1.symm

-- Test nested pairs
example (x : (F p × F p) × F p) (h : ((1, 2), 3) = x) : x.1.1 = 1 := by
  split_pair_eq
  -- Only the outer pair should be split initially
  split_pair_eq
  -- Now the inner pair should be split
  exact h.1.1.symm

-- Test that non-provable pairs are NOT split
section NonProvableTests

example (x : ℕ × String) (h : (5, "hello") = x) : x = (5, "hello") := by
  split_pair_eq
  -- This should not split since ℕ and String don't have Field instances
  -- So we just have the original hypothesis
  exact h.symm

end NonProvableTests

-- Test interaction with provable_simp
example (x : F p × F p) (y : F p) (h : (5, 3) = x ∧ x.1 + y = 8) :
    x.2 + 5 = x.1 + x.2 := by
  provable_simp
  -- provable_simp should apply split_pair_eq among other tactics
  -- Now h.1 is split into component equalities
  rw [h.1.1.symm, h.1.2.symm]
  ring

end TestSplitPairEq
