import Lean.Elab.Tactic
import Clean.Halo2.QueryCorrect

/-!
# Query-declaration tactic

`query_correct` proves the routine local law that `queriedCells` contains valid query
atoms and covers every ordinary query used by the resulting gate or lookup expressions.
Extra declarations remain permitted because Halo 2 closures may issue a query whose
result is not used in the final expression.
-/

namespace Halo2

/-- Prove concrete query-declaration goals from expression and list structure. -/
macro "query_correct" : tactic =>
  `(tactic| simp_all! +zetaDelta [query_correct])

end Halo2
