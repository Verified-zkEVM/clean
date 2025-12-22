import Lean
import Clean.Circuit.Provable
import Clean.Utils.Tactics.ProvableTacticUtils
import Lean.PrettyPrinter.Delaborator.Basic

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

/-- Check if an expression contains a struct eval equality pattern, including inside conjunctions.
    Returns the struct expression being evaluated if a pattern is found. -/
private partial def collectStructEvalPattern (e : Expr) : MetaM (List Expr) := do
  match e with
  | .app (.app (.const ``And _) left) right =>
    -- Check both sides of conjunction
    let leftStruct ← collectStructEvalPattern left
    let rightStruct ← collectStructEvalPattern right
    return leftStruct ++ rightStruct
  | _ =>
    -- Check if it's an equality with eval
    if e.isAppOf `Eq then
      if let (some lhs, some rhs) := (e.getArg? 1, e.getArg? 2) then
        let lhsIsEval := hasEvalPattern lhs
        let rhsIsEval := hasEvalPattern rhs

        if lhsIsEval || rhsIsEval then
          let evalSide := if lhsIsEval then lhs else rhs
          let otherSide := if lhsIsEval then rhs else lhs
          let otherSideIsEval := if lhsIsEval then rhsIsEval else lhsIsEval

          -- Check if other side is a struct literal
          let otherIsLiteral ← if otherSideIsEval then
              if let some otherExpr := otherSide.getArg? 5 then
                isStructLiteral otherExpr
              else
                pure false
            else
              isStructLiteral otherSide
          if otherIsLiteral then
            -- Extract the struct expression being evaluated (last argument of ProvableType.eval)
            if let some structExpr := evalSide.getArg? 5 then
              return [structExpr]
            else
              return []

          -- If other side is just a variable, check if eval side has a struct literal
          -- Extract the argument of eval (the struct being evaluated)
          if let some evalArg := evalSide.getArg? 5 /- very specific to ProvableType.eval -/ then
            let isLit ← isStructLiteral evalArg
            if isLit then
              return [evalArg]
            else
              return []
          else
            return []
        else
          return []
      else
        return []
    else
      return []

/-- Simplifies `eval env` expressions in equalities with struct literals or struct variables.
    When we have `eval env struct_var = struct_literal` or `eval env struct_var = struct_variable`,
    this applies the necessary simp lemmas to unfold the eval on those specific hypotheses.
    Also looks inside conjunctions. -/
elab "simplify_provable_struct_eval" : tactic => do
  let ctx ← getLCtx
  let mut allStructExprs : List (Lean.Name × Expr) := []

  -- First pass: collect all struct expressions from all hypotheses
  for decl in ctx do
    if decl.isImplementationDetail then continue
    let type ← instantiateMVars decl.type
    let structExprs ← collectStructEvalPattern type
    for expr in structExprs do
      allStructExprs := allStructExprs ++ [(decl.userName, expr)]

  if allStructExprs.isEmpty then
    throwError "simplify_provable_struct_eval made no progress"

  -- Get all unique hypothesis names
  let hypNames := allStructExprs.map (·.1) |>.eraseDups

  -- Apply simp to each hypothesis
  for hypName in hypNames do
    -- Collect struct expressions for this hypothesis
    let structExprsForHyp := allStructExprs.filter (fun (name, _) => name == hypName) |>.map (·.2)

    -- Build simp lemmas for this hypothesis
    let mut simpArgs : Array (TSyntax `Lean.Parser.Tactic.simpLemma) := #[]

    -- Add eval_eq_eval for each struct expression
    for structExpr in structExprsForHyp do
      let structType ← inferType structExpr
      let structSyntax ← Lean.PrettyPrinter.delab structExpr
      let typeSyntax ← Lean.PrettyPrinter.delab structType
      let castStructSyntax ← `(($structSyntax : $typeSyntax))
      let evalLemma ← `(Lean.Parser.Tactic.simpLemma| ProvableStruct.eval_eq_eval (x := $castStructSyntax))
      simpArgs := simpArgs.push evalLemma

    -- Add the other simp lemmas
    simpArgs := simpArgs.push (← `(Lean.Parser.Tactic.simpLemma| ProvableStruct.eval))
    simpArgs := simpArgs.push (← `(Lean.Parser.Tactic.simpLemma| ProvableStruct.fromComponents))
    simpArgs := simpArgs.push (← `(Lean.Parser.Tactic.simpLemma| ProvableStruct.components))
    simpArgs := simpArgs.push (← `(Lean.Parser.Tactic.simpLemma| ProvableStruct.toComponents))
    simpArgs := simpArgs.push (← `(Lean.Parser.Tactic.simpLemma| ProvableStruct.eval.go))
    simpArgs := simpArgs.push (← `(Lean.Parser.Tactic.simpLemma| ProvableType.eval_field))

    -- Apply simp to this hypothesis
    let hypIdent := mkIdent hypName
    let tac ← `(tactic| simp only [$[$simpArgs],*] at $hypIdent:ident)
    evalTactic tac
