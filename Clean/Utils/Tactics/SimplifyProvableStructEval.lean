import Lean
import Clean.Circuit.Provable
import Clean.Utils.Tactics.ProvableTacticUtils

open Lean Meta Elab Tactic

/-- Helper function to check if an expression is a struct constructor or struct variable -/
private def isStructLiteral (e : Expr) : MetaM Bool := do
  -- First check the type to see if it's a ProvableStruct
  try
    let type ← inferType e
    if ← hasProvableStructInstance type then
      -- Also check if it's a constructor explicitly
      isMkConstructor e
    else
      return false
  catch _ => return false

/-- Check if an expression contains a struct eval equality pattern, including inside conjunctions -/
private partial def containsStructEvalPattern (e : Expr) : MetaM Bool := do
  match e with
  | .app (.app (.const ``And _) left) right =>
    -- Check both sides of conjunction
    let leftHas ← containsStructEvalPattern left
    let rightHas ← containsStructEvalPattern right
    return leftHas || rightHas
  | _ =>
    -- Check if it's an equality with eval
    if e.isAppOf `Eq then
      if let (some lhs, some rhs) := (e.getArg? 1, e.getArg? 2) then
        let lhsIsEval := hasEvalPattern lhs
        let rhsIsEval := hasEvalPattern rhs

        if lhsIsEval || rhsIsEval then
          let evalSide := if lhsIsEval then lhs else rhs
          let otherSide := if lhsIsEval then rhs else lhs

          -- Check if other side is a struct literal
          let otherIsLiteral ← isStructLiteral otherSide
          if otherIsLiteral then
            return true

          -- If other side is just a variable, check if eval side has a struct literal
          -- Extract the argument of eval (the struct being evaluated)
          if let some evalArg := evalSide.getArg? 1 then
            isStructLiteral evalArg
          else
            return false
        else
          return false
      else
        return false
    else
      return false

/-- Simplifies `eval env` expressions in equalities with struct literals or struct variables.
    When we have `eval env struct_var = struct_literal` or `eval env struct_var = struct_variable`,
    this applies the necessary simp lemmas to unfold the eval on those specific hypotheses.
    Also looks inside conjunctions. -/
elab "simplify_provable_struct_eval" : tactic => do
  let ctx ← getLCtx
  let mut anyModified := false

  -- Helper to apply the simp lemmas to a specific hypothesis
  let applySimpToHyp (declName : Lean.Name) : Lean.Elab.Tactic.TacticM Unit := do
    let tac ← `(tactic| simp only [
      ProvableStruct.eval_eq_eval,
      ProvableStruct.eval,
      ProvableStruct.fromComponents,
      ProvableStruct.eval.go,
      ProvableType.eval_field
    ] at $(mkIdent declName):ident)
    evalTactic tac

  -- Process each hypothesis
  for decl in ctx do
    if decl.isImplementationDetail then continue

    let type ← instantiateMVars decl.type

    -- First check if it's a direct equality
    if type.isAppOf `Eq then
      if let (some lhs, some rhs) := (type.getArg? 1, type.getArg? 2) then
        let lhsIsEval := hasEvalPattern lhs
        let rhsIsEval := hasEvalPattern rhs

        if lhsIsEval || rhsIsEval then
          let evalSide := if lhsIsEval then lhs else rhs
          let otherSide := if lhsIsEval then rhs else lhs

          -- Check if we should apply simplification
          let shouldSimplify ← do
            -- Check if other side is a struct literal
            let otherIsLiteral ← isStructLiteral otherSide
            if otherIsLiteral then
              pure true
            else
              -- If other side is just a variable, check if eval side has a struct literal
              -- Extract the argument of eval (the struct being evaluated)
              if let some evalArg := evalSide.getArg? 1 then
                isStructLiteral evalArg
              else
                pure false

          if shouldSimplify then
            -- Apply simp to this specific hypothesis only
            try
              applySimpToHyp decl.userName
              anyModified := true
            catch e =>
              trace[Meta.Tactic] "Failed to apply simp to hypothesis {decl.userName}: {e.toMessageData}"
              continue

    -- Also check if it contains conjunctions with struct eval equalities
    else if type.isAppOf ``And then
      -- Apply simp to hypotheses that contain the pattern inside conjunctions
      let hasPattern ← containsStructEvalPattern type
      if hasPattern then
        try
          applySimpToHyp decl.userName
          anyModified := true
        catch e =>
          trace[Meta.Tactic] "Failed to apply simp to hypothesis {decl.userName}: {e.toMessageData}"
          continue

  if !anyModified then
    throwError "simplify_provable_struct_eval made no progress"
