import Clean.Utils.Tactics.SimplifyPairEval
import Clean.Utils.Tactics.ProvableSimp
import Clean.Circuit.Provable
import Clean.Circuit.Expression
import Clean.Utils.Field

namespace TestSimplifyPairEval

open ProvableType

variable {p : ℕ} [Fact p.Prime]

-- Basic test that the tactic modifies hypotheses with ProvableType.eval
example (env : Environment (F p)) (x : Var fieldPair (F p))
    (h : ProvableType.eval env x = (5, 3)) :
    Expression.eval env x.1 = 5 := by
  -- The tactic should simplify h using eval_fieldPair and Prod.mk.injEq
  simplify_pair_eval
  -- Now h should be decomposed: Expression.eval env x.1 = 5 ∧ Expression.eval env x.2 = 3
  exact h.1

-- Test with conjunction containing eval
example (env : Environment (F p)) (x : Var fieldPair (F p)) (y : F p)
    (h : ProvableType.eval env x = (5, 3) ∧ Expression.eval env x.1 + y = 8) :
    Expression.eval env x.2 = 3 := by
  simplify_pair_eval
  -- h.1 should now be decomposed
  exact h.1.2

-- Test that provable_simp works with eval expressions
example (env : Environment (F p)) (x : Var fieldPair (F p))
    (h : ProvableType.eval env x = (5, 3)) :
    Expression.eval env x.1 + Expression.eval env x.2 = 8 := by
  -- provable_simp should apply simplify_pair_eval among other tactics
  provable_simp
  -- Now h should be fully decomposed
  rw [h.1, h.2]
  norm_num

end TestSimplifyPairEval
