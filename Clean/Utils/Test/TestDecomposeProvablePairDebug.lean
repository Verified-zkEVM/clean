import Clean.Utils.Tactics.DecomposeProvablePair
import Clean.Circuit.Provable
import Clean.Utils.Field

variable {p : ℕ} [Fact p.Prime]

-- Test nested pairs debug
example (input : (F p × F p) × F p) (h : input.1.1 = 5) : 
    input.1.2 + input.2 = input.1.1 + input.1.2 + input.2 - 5 := by
  show_pair_vars  -- Show what pairs are detected
  decompose_provable_pair
  trace_state  -- Show the state after first decomposition
  show_pair_vars  -- Show what pairs can be detected now
  decompose_provable_pair
  trace_state  -- Show the state after second decomposition
  sorry