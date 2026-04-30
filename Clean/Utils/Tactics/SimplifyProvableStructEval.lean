import Lean
import Clean.Circuit.Provable
import Clean.Utils.Tactics.ProvableTacticUtils
import Lean.PrettyPrinter.Delaborator.Basic

open Lean Meta Elab Tactic

/-- If `name` is a generated view structure name like `Input.Var`, return `Input`. -/
private def baseNameOfVarView? (name : Name) : Option Name :=
  match name with
  | .str base "Var" => some base
  | _ => none

/-- Extract the underlying circuit type from a type like `Var Input F`, if present. -/
private def circuitTypeOfVarProjection? (type : Expr) : Option Name :=
  if type.getAppFn.isConstOf ``CircuitType.Var then
    match type.getAppArgs[0]? with
    | some e =>
      match e with
      | Expr.const name _ => some name
      | _ => none
    | _ => none
  else
    none

/-- Find the derived record `CircuitType` behind an expression being evaluated. -/
private def baseCircuitTypeNameOfVar? (e : Expr) : MetaM (Option Name) := do
  let type ← inferType e
  let type' ← withTransparency .reducible (whnf type)
  return circuitTypeOfVarProjection? type' <|>
      (type'.getAppFn.constName?.bind baseNameOfVarView?)

private def generatedCircuitTypeLemmas (e : Expr) (suffixes : Array Name) : MetaM (Array Name) := do
  let env ← getEnv
  let some baseName ← baseCircuitTypeNameOfVar? e
    | return #[]
  let candidates := suffixes.map (baseName ++ ·)
  return candidates.filter env.contains

/--
Generated eval lemmas for derived record `CircuitType`s.

These lemmas are generated only for derived record `CircuitType`s; hand-written
`CircuitType`s keep control over whether their eval behavior is exposed.
-/
private def generatedCircuitTypeEvalLemmas (e : Expr) : MetaM (Array Name) :=
  generatedCircuitTypeLemmas e #[`eval_verifier, `eval_prover]

/-- Generated view reduction lemmas for derived record `CircuitType`s. -/
private def generatedCircuitTypeViewLemmas (e : Expr) : MetaM (Array Name) :=
  generatedCircuitTypeLemmas e #[`value_eq, `proverValue_eq]

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

/-- Check whether an expression has a type backed by `ProvableStruct`. -/
private def hasProvableStructType (e : Expr) : MetaM Bool := do
  try
    let type ← inferType e
    hasProvableStructInstance type
  catch _ => return false

/-- Extract the value being evaluated from supported `eval` forms. -/
private def evalArg? (e : Expr) : Option Expr :=
  if e.isAppOf ``eval || e.isAppOf ``ProvableType.eval then
    e.getAppArgs.back?
  else
    none

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
              if let some otherExpr := evalArg? otherSide then
                isStructLiteral otherExpr
              else
                pure false
            else
              isStructLiteral otherSide
          if otherIsLiteral then
            -- Extract the struct expression being evaluated.
            if let some structExpr := evalArg? evalSide then
              return [structExpr]
            else
              return []

          -- Derived record `CircuitType`s expose eval through generated lemmas.
          -- They are not necessarily `ProvableStruct`s on the variable side, but
          -- their verifier/prover values should still be split field-wise.
          if let some structExpr := evalArg? evalSide then
            if !(← generatedCircuitTypeEvalLemmas structExpr).isEmpty then
              return [structExpr]

          -- If the other side is a plain struct variable, unfold the eval side
          -- so that `split_provable_struct_eq` can turn the resulting
          -- constructor equality into field-wise equalities.
          if !otherSideIsEval then
            if ← hasProvableStructType otherSide then
              if let some structExpr := evalArg? evalSide then
                return [structExpr]
              else
                return []

          -- If other side is just a variable, check if eval side has a struct literal
          -- Extract the argument of eval (the struct being evaluated)
          if let some evalArg := evalArg? evalSide then
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
    let mut preSimpArgs : Array (TSyntax `Lean.Parser.Tactic.simpLemma) := #[]
    let mut simpArgs : Array (TSyntax `Lean.Parser.Tactic.simpLemma) := #[]

    -- Add eval_eq_eval for each struct expression
    for structExpr in structExprsForHyp do
      let generatedEvalLemmaNames ← generatedCircuitTypeEvalLemmas structExpr
      if generatedEvalLemmaNames.isEmpty then
        let structType ← inferType structExpr
        let structSyntax ← Lean.PrettyPrinter.delab structExpr
        let typeSyntax ← Lean.PrettyPrinter.delab structType
        let castStructSyntax ← `(($structSyntax : $typeSyntax))
        let evalLemma ← `(Lean.Parser.Tactic.simpLemma| ProvableStruct.eval_eq_eval (x := $castStructSyntax))
        simpArgs := simpArgs.push evalLemma
        let evalProverLemma ← `(Lean.Parser.Tactic.simpLemma| ProvableStruct.eval_eq_eval_prover (x := $castStructSyntax))
        simpArgs := simpArgs.push evalProverLemma
      for lemmaName in generatedEvalLemmaNames do
        let lemmaIdent := mkIdent lemmaName
        let simpLemmaSyntax ← `(Lean.Parser.Tactic.simpLemma| $lemmaIdent:ident)
        preSimpArgs := preSimpArgs.push simpLemmaSyntax
      for lemmaName in (← generatedCircuitTypeViewLemmas structExpr) do
        let lemmaIdent := mkIdent lemmaName
        let simpLemmaSyntax ← `(Lean.Parser.Tactic.simpLemma| $lemmaIdent:ident)
        simpArgs := simpArgs.push simpLemmaSyntax

    -- Add the other simp lemmas
    simpArgs := simpArgs.push (← `(Lean.Parser.Tactic.simpLemma| ProvableStruct.eval))
    simpArgs := simpArgs.push (← `(Lean.Parser.Tactic.simpLemma| ProvableStruct.fromComponents))
    simpArgs := simpArgs.push (← `(Lean.Parser.Tactic.simpLemma| ProvableStruct.components))
    simpArgs := simpArgs.push (← `(Lean.Parser.Tactic.simpLemma| ProvableStruct.toComponents))
    simpArgs := simpArgs.push (← `(Lean.Parser.Tactic.simpLemma| ProvableStruct.eval.go))
    simpArgs := simpArgs.push (← `(Lean.Parser.Tactic.simpLemma| ProvableType.eval_field))
    simpArgs := simpArgs.push (← `(Lean.Parser.Tactic.simpLemma| CircuitType.eval_var_prover_to_verifier))
    simpArgs := simpArgs.push (← `(Lean.Parser.Tactic.simpLemma| CircuitType.eval_var_field))
    simpArgs := simpArgs.push (← `(Lean.Parser.Tactic.simpLemma| CircuitType.eval_var_field_prover))
    simpArgs := simpArgs.push (← `(Lean.Parser.Tactic.simpLemma| CircuitType.eval_expr))
    simpArgs := simpArgs.push (← `(Lean.Parser.Tactic.simpLemma| CircuitType.eval_expr_prover))

    -- For generated record `CircuitType`s, expose `eval env input_var` before
    -- reducing `Value Input F` / `ProverValue Input F` to the generated view
    -- structures. If the view type is reduced first, the generated eval lemma no
    -- longer matches the `eval` expression reliably.
    if !preSimpArgs.isEmpty then
      preSimpArgs := preSimpArgs.push (← `(Lean.Parser.Tactic.simpLemma| circuit_norm))
      try
        let hypIdent := mkIdent hypName
        let tac ← `(tactic| simp only [$[$preSimpArgs],*] at $hypIdent:ident)
        evalTactic tac
      catch _ =>
        pure ()

    -- Apply the targeted eval simplification throughout the local context. A
    -- struct eval equality often feeds other hypotheses containing projections
    -- of the same `eval env struct`, so simplifying only the equality itself is
    -- not enough.
    withMainContext do
      let ctx ← getLCtx
      for localDecl in ctx do
        if localDecl.isImplementationDetail then
          continue
        try
          let hypIdent := mkIdent localDecl.userName
          let tac ← `(tactic| simp only [$[$simpArgs],*] at $hypIdent:ident)
          evalTactic tac
        catch _ =>
          continue
      try
        let tac ← `(tactic| simp only [$[$simpArgs],*])
        evalTactic tac
      catch _ =>
        pure ()
