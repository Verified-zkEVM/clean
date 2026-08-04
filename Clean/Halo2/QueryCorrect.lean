import Clean.Halo2.Expression
import Clean.Halo2.QueryCorrectAttr

namespace Halo2

variable {F : Type}

attribute [query_correct] Expression.mulConstant

/-- A declaration accepted by Halo 2's query-registration interface. -/
@[query_correct]
def Expression.QueryAtom : Expression F Query → Prop
  | .var (.advice _ _) => True
  | .var (.fixed _ rotation) => rotation = 0
  | .var (.instance _ _) => True
  | _ => False

/-- Every ordinary query used by an expression was issued by its configure closure.
Selectors are registered by selector allocation rather than `queriedCells`. -/
@[query_correct]
def Expression.QueriesDeclared
    (declared : List (Expression F Query)) : Expression F Query → Prop
  | .var (.selector _) => True
  | .var query => .var query ∈ declared
  | .const _ => True
  | .add left right =>
      left.QueriesDeclared declared ∧ right.QueriesDeclared declared
  | .mul left right =>
      left.QueriesDeclared declared ∧ right.QueriesDeclared declared

/-- Query coverage of a product fold is local to its seed and factors. -/
@[query_correct]
theorem Expression.queriesDeclared_foldl_mul
    {F α : Type}
    (declared : List (Expression F Query))
    (xs : List α) (factor : α → Expression F Query)
    (acc : Expression F Query) :
    (xs.foldl (fun product x => product * factor x) acc).QueriesDeclared declared ↔
      acc.QueriesDeclared declared ∧
        ∀ x ∈ xs, (factor x).QueriesDeclared declared := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih =>
      simp [List.foldl_cons, ih, Expression.QueriesDeclared, and_assoc]

end Halo2
