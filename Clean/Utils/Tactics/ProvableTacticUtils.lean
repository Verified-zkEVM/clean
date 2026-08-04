import Lean
import Clean.Circuit.CircuitType
import Clean.Circuit.Provable

open Lean Meta Elab Tactic

/-- Check if an expression is a constructor application (ends with .mk).

This intentionally does not unfold the expression. The struct tactics use this as
a cheap syntactic guard before splitting constructor equalities; unfolding here
can expand `eval` terms appearing in unrelated hypotheses and make the tactic
far too expensive.
-/
def isMkConstructor (e : Expr) : MetaM Bool := do
  match e.consumeMData.getAppFn with
  | .const name _ =>
    -- Check if it's a constructor (ends with .mk)
    return name.components.getLast? == some `mk
  | _ => return false

/-- Extract all equalities from an expression (including inside conjunctions) -/
partial def extractEqualities (e : Expr) : MetaM (List (Expr × Expr × Expr)) := do
  -- Returns list of (equality_expr, lhs, rhs) triples
  match e with
  | .app (.app (.const ``And _) left) right =>
    -- Handle conjunction
    let leftEqs ← extractEqualities left
    let rightEqs ← extractEqualities right
    return leftEqs ++ rightEqs
  | _ =>
    -- Check if it's an equality
    if e.isAppOf `Eq then
      if let (some lhs, some rhs) := (e.getArg? 1, e.getArg? 2) then
        return [(e, lhs, rhs)]
    return []
