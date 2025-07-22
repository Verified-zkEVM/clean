import Lean
import Clean.Circuit.Provable
import Clean.Utils.Tactics.DecomposeProvablePair

open Lean Meta Elab Tactic

namespace ProvenZK

/-- Helper function to check if an expression is a pair constructor or pair variable -/
private def isPairLiteral (e : Expr) : MetaM Bool := do
  -- First check the type to see if it's a provable pair
  try
    let type ← inferType e
    if ← isProdTypeWithProvableType type then
      -- Also check if it's a constructor explicitly
      let e' ← withTransparency .all (whnf e)
      match e'.getAppFn with
      | .const name _ =>
        -- Check if it's Prod.mk
        return name == ``Prod.mk
      | _ => return false
    else
      return false
  catch _ => return false

/-- Check if an expression contains a pair eval equality pattern, including inside conjunctions -/
private partial def containsPairEvalPattern (e : Expr) : MetaM Bool := do
  match e with
  | .app (.app (.const ``And _) left) right =>
    -- Check both sides of conjunction
    let leftHas ← containsPairEvalPattern left
    let rightHas ← containsPairEvalPattern right
    return leftHas || rightHas
  | _ =>
    -- Check if it's an equality with eval
    if e.isAppOf `Eq then
      if let (some lhs, some rhs) := (e.getArg? 1, e.getArg? 2) then
        let lhsIsProvableEval := lhs.isAppOf ``ProvableType.eval
        let rhsIsProvableEval := rhs.isAppOf ``ProvableType.eval
        let lhsIsExprEval := lhs.isAppOf ``Expression.eval
        let rhsIsExprEval := rhs.isAppOf ``Expression.eval

        let lhsIsEval := lhsIsProvableEval || lhsIsExprEval
        let rhsIsEval := rhsIsProvableEval || rhsIsExprEval

        if lhsIsEval || rhsIsEval then
          let evalSide := if lhsIsEval then lhs else rhs
          let otherSide := if lhsIsEval then rhs else lhs

          -- Check if other side is a pair literal
          let otherIsLiteral ← isPairLiteral otherSide
          if otherIsLiteral then
            return true

          -- Check if other side is a pair variable with provable type
          let otherType ← inferType otherSide
          if ← isProdTypeWithProvableType otherType then
            -- If other side is just a variable, check if eval side has a pair literal
            -- Extract the argument of eval (the pair being evaluated)
            if let some evalArg := evalSide.getArg? 1 then
              isPairLiteral evalArg
            else
              return false
          else
            return false
        else
          return false
      else
        return false
    else
      return false

/-- Simplifies `eval env` expressions in equalities with pair literals or pair variables.
    When we have `eval env (a, b) = pair_var` or `eval env pair_var = (c, d)`,
    this applies the necessary simp lemmas to unfold the eval on those specific hypotheses.
    Also looks inside conjunctions. -/
elab "simplify_pair_eval" : tactic => do
  let ctx ← getLCtx
  let mut anyModified := false

  -- Helper to apply the simp lemmas to a specific hypothesis
  let applySimpToHyp (declName : Lean.Name) : Lean.Elab.Tactic.TacticM Unit := do
    let tac ← `(tactic| simp only [
      ProvableType.eval_fieldPair,
      ProvableType.eval_fieldTriple,
      eval_pair,
      eval_pair_left_expr,
      eval_pair_right_expr,
      eval_pair_both_expr,
      eval_pair_left_vector_expr,
      eval_pair_right_vector_expr,
      eval_pair_both_vector_expr,
      Prod.fst,
      Prod.snd,
      Prod.mk.injEq
    ] at $(mkIdent declName):ident)
    evalTactic tac

  -- Process each hypothesis
  for decl in ctx do
    if decl.isImplementationDetail then continue

    let type ← instantiateMVars decl.type

    -- First check if it's a direct equality
    if type.isAppOf `Eq then
      if let (some lhs, some rhs) := (type.getArg? 1, type.getArg? 2) then
        let lhsIsProvableEval := lhs.isAppOf ``ProvableType.eval
        let rhsIsProvableEval := rhs.isAppOf ``ProvableType.eval
        let lhsIsExprEval := lhs.isAppOf ``Expression.eval
        let rhsIsExprEval := rhs.isAppOf ``Expression.eval

        let lhsIsEval := lhsIsProvableEval || lhsIsExprEval
        let rhsIsEval := rhsIsProvableEval || rhsIsExprEval

        if lhsIsEval || rhsIsEval then
          let evalSide := if lhsIsEval then lhs else rhs
          let otherSide := if lhsIsEval then rhs else lhs

          -- Check if other side is a pair literal
          let otherIsLiteral ← isPairLiteral otherSide

          -- Check if other side has provable pair type
          let otherType ← inferType otherSide
          let otherIsProvablePair ← isProdTypeWithProvableType otherType

          if otherIsLiteral || otherIsProvablePair then
            -- Apply simp lemmas to this hypothesis
            try
              applySimpToHyp decl.userName
              anyModified := true
            catch e =>
              trace[Meta.Tactic] "Failed to apply simp to hypothesis {decl.userName}: {e.toMessageData}"
              continue
          else
            -- If other side is a variable, check if eval side has a pair literal
            if let some evalArg := evalSide.getArg? 1 then
              if ← isPairLiteral evalArg then
                try
                  applySimpToHyp decl.userName
                  anyModified := true
                catch e =>
                  trace[Meta.Tactic] "Failed to apply simp to hypothesis {decl.userName}: {e.toMessageData}"
                  continue

    -- Also check if the hypothesis contains pair eval patterns inside conjunctions
    else if ← containsPairEvalPattern type then
      try
        applySimpToHyp decl.userName
        anyModified := true
      catch e =>
        trace[Meta.Tactic] "Failed to apply simp to hypothesis {decl.userName}: {e.toMessageData}"
        continue

  -- Ensure the tactic made progress
  if !anyModified then
    throwError "simplify_pair_eval made no progress"

end ProvenZK
