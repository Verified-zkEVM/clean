import Lean.Elab.Tactic
import Lean.Elab.Exception
import Clean.Circuit.Provable

open Lean.Elab.Tactic
open Lean.Meta
open Lean

partial def getMaxMatchingHyp (e : Lean.Expr) : Lean.Elab.Tactic.TacticM (List Lean.Expr) := do
  -- it suffices to reduce to whnf to look at the outer structure
  let e ← whnf e
  match e with
  | (.forallE _ typ body _) => do
    -- dependent function type, search the context for a matching hypothesis
    let ctx ← Lean.MonadLCtx.getLCtx
    let option_matching_expr ← ctx.findDeclM? fun decl: Lean.LocalDecl => do
      let declExpr := decl.toExpr
      let declType ← Lean.Meta.inferType declExpr
      if ← Lean.Meta.isExprDefEq declType typ
        then return Option.some declExpr
        else return Option.none

    -- if we found one, keep it and recurse on the body
    match option_matching_expr with
    | some res => do
      let other_hyps ← getMaxMatchingHyp body
      return [res] ++ other_hyps
    | none => do return []
  | _ => return []

partial def SpecializeAuto (e_term : Lean.Term): Lean.Elab.Tactic.TacticM Unit := do
  let (e, mvarIds') ← elabTermWithHoles e_term none `specialize_auto (allowNaturalHoles := true)

  -- e must be a free variable in the local context
  if e.isFVar then
    let localDecl ← e.fvarId!.getDecl
    let declType ← Lean.Meta.inferType localDecl.toExpr

    -- get the maximum number of matching hypotheses
    let matching ← getMaxMatchingHyp declType

    -- construct an application expr `t e1 e2 ... en` where `t` is the term we want to specialize
    let h' := Lean.mkAppN e matching.toArray

    -- replace the term with the specialized term
    let goal ← getMainGoal
    let mvarId ← goal.assert (← e.fvarId!.getDecl).userName (← inferType h').headBeta h'
    let (_, mvarId) ← mvarId.intro1P
    let mvarId ← mvarId.tryClear e.fvarId!
    replaceMainGoal (mvarIds' ++ [mvarId])
  else
    throwError "'specialize_auto' requires a term that appears in the local context"

/--
  Takes in input a term `t` which must be present in the context. If `t` is of the form
  `h1 -> h2 -> ... -> hn -> t'`, it searches in the context for `h1`, `h2`, ..., `hn` and
  specializess it with them.
-/
elab "specialize_auto" e:term : tactic => withMainContext do SpecializeAuto e

/--
  Find field projections in an expression and return the base variable if it's a structure
-/
partial def findStructVars (e : Lean.Expr) : Lean.MetaM (List Lean.FVarId) := do
  let e' ← whnf e
  let rec go (e : Lean.Expr) (acc : List Lean.FVarId) : Lean.MetaM (List Lean.FVarId) := do
    match e with
    | .proj _ _ base => 
      -- Found a projection, check if base is a variable
      match base with
      | .fvar fvarId => 
        return fvarId :: acc
      | _ => go base acc
    | .app f a => 
      -- Check if this is a structure field access function
      match f with
      | .const name _ =>
        -- Check if it's a structure field accessor
        let env ← getEnv
        if let some _ := env.getProjectionFnInfo? name then
          -- This is a projection function, check the argument
          match a with
          | .fvar fvarId =>
            return fvarId :: acc
          | _ => go a acc
        else
          -- Regular application
          let acc' ← go f acc
          go a acc'
      | _ =>
        -- Regular application
        let acc' ← go f acc
        go a acc'
    | .lam _ _ body _ | .forallE _ _ body _ => 
      -- For binders, check the body
      go body acc
    | .letE _ _ val body _ =>
      -- For let expressions, check both value and body
      let acc' ← go val acc
      go body acc'
    | .mdata _ expr => go expr acc
    | _ => return acc
  
  go e' []

/--
  Find all variables in the context that have structure types,
  including those that appear in field projections in hypotheses
-/
def findAllStructVars : Lean.Elab.Tactic.TacticM (List Lean.FVarId) := do
  withMainContext do
    let ctx ← Lean.MonadLCtx.getLCtx
    let mut result := []
    
    -- First, find all variables that have structure types
    for localDecl in ctx do
      if localDecl.isImplementationDetail then
        continue
      
      let type ← inferType localDecl.toExpr
      -- Reduce the type to handle type synonyms like Var (using transparency mode that unfolds reducible definitions)
      let type' ← withTransparency .reducible (whnf type)
      let typeCtor := type'.getAppFn
      
      -- Check if it's a structure type
      match typeCtor with
      | .const name _ =>
        let env ← getEnv
        -- Check if it has structure info (i.e., it's a structure)
        if (getStructureInfo? env name).isSome then
          result := localDecl.fvarId :: result
      | _ => continue
    
    -- Also search for projections in the types of hypotheses
    for localDecl in ctx do
      if localDecl.isImplementationDetail then
        continue
      
      -- Search in the type of each hypothesis
      let varsInType ← findStructVars localDecl.type
      result := result ++ varsInType
    
    -- Remove duplicates and return
    return result.eraseDups

/--
  Decompose all variables with structure types in the context
-/
def decomposeStruct : Lean.Elab.Tactic.TacticM Unit := do
  withMainContext do
    let goal ← getMainGoal
    let target ← goal.getType
    
    -- Find all variables with structure types in the context
    let mut fvarIds ← findAllStructVars
    
    -- Also search for projections in the goal
    let varsInGoal ← findStructVars target
    fvarIds := (fvarIds ++ varsInGoal).eraseDups
    
    if fvarIds.isEmpty then
      throwError "No variables with structure types found in the context or goal"
    
    -- Apply cases on each variable
    let mut currentGoal := goal
    let mut decomposed := false
    
    for fvarId in fvarIds do
      let localDecl ← fvarId.getDecl
      let userName := localDecl.userName
      let type ← inferType localDecl.toExpr
      
      try
        -- Use cases tactic on the variable
        let casesResult ← currentGoal.cases fvarId
        
        -- Get the new goal from the cases result
        match casesResult.toList with
        | [subgoal] => 
          currentGoal := subgoal.mvarId
          decomposed := true
        | _ => 
          throwError s!"Unexpected result from cases on {userName}"
      catch _ =>
        -- Skip variables that can't be decomposed (like Var types)
        continue
    
    replaceMainGoal [currentGoal]


/--
  Automatically decompose ALL variables with structure types that either:
  1. Are in the context as variables with structure types
  2. Appear in field projections in hypotheses (e.g., h : input.x = 5)
  3. Appear in field projections in the goal
  
  Example:
  ```lean
  theorem example_theorem (input : Inputs (F p)) (h : input.x = 5) : 
    input.y + input.z = someValue := by
    decompose_struct  -- This will destruct `input` (found via projections)
    -- Now we have x, y, z in context with h : x = 5
    sorry
  ```
-/
elab "decompose_struct" : tactic => decomposeStruct


/--
  Print all structure variables found in the context and goal
  (useful for debugging decompose_struct)
-/
elab "show_struct_vars" : tactic => do
  withMainContext do
    let goal ← getMainGoal
    let target ← goal.getType
    
    -- Find all variables with structure types in the context
    let mut fvarIds ← findAllStructVars
    
    -- Also search for projections in the goal
    let varsInGoal ← findStructVars target
    fvarIds := (fvarIds ++ varsInGoal).eraseDups
    
    if fvarIds.isEmpty then
      logInfo "No structure variables found in context or goal"
    else
      logInfo "Found structure variables:"
      for fvarId in fvarIds do
        let localDecl ← fvarId.getDecl
        let type ← inferType localDecl.toExpr
        logInfo m!"  {localDecl.userName} : {type}"
