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
  Find all variables in the context that have ProvableStruct instances,
  including those that appear in field projections in hypotheses
-/
def findProvableStructVars : Lean.Elab.Tactic.TacticM (List Lean.FVarId) := do
  withMainContext do
    let ctx ← Lean.MonadLCtx.getLCtx
    let mut result := []
    
    -- First, find all variables that have ProvableStruct instances
    for localDecl in ctx do
      if localDecl.isImplementationDetail then
        continue
      
      let type ← inferType localDecl.toExpr
      -- Reduce the type to handle type synonyms like Var (using transparency mode that unfolds reducible definitions)
      let type' ← withTransparency .reducible (whnf type)
      let typeCtor := type'.getAppFn
      
      -- Check if it's a structure type with ProvableStruct instance
      match typeCtor with
      | .const name _ =>
        let env ← getEnv
        -- Check if it has structure info AND ProvableStruct instance
        if (getStructureInfo? env name).isSome then
          -- Check for ProvableStruct instance on the type constructor
          try
            let instType ← mkAppM ``ProvableStruct #[.const name []]
            if let .some _ ← trySynthInstance instType then
              result := localDecl.fvarId :: result
          catch _ => continue
      | _ => continue
    
    -- Also search for projections in the types of hypotheses
    for localDecl in ctx do
      if localDecl.isImplementationDetail then
        continue
      
      -- Search in the type of each hypothesis
      let varsInType ← findStructVars localDecl.type
      -- Filter to only include those with ProvableStruct instances
      for fvarId in varsInType do
        let type ← inferType (.fvar fvarId)
        let type' ← withTransparency .reducible (whnf type)
        let typeCtor := type'.getAppFn
        match typeCtor with
        | .const name _ =>
          try
            let instType ← mkAppM ``ProvableStruct #[.const name []]
            if let .some _ ← trySynthInstance instType then
              result := result ++ [fvarId]
          catch _ => continue
        | _ => continue
    
    -- Remove duplicates and return
    return result.eraseDups

/--
  Decompose all variables with ProvableStruct instances in the context
-/
def decomposeProvableStruct : Lean.Elab.Tactic.TacticM Unit := do
  withMainContext do
    let goal ← getMainGoal
    let target ← goal.getType
    
    -- Find all variables with ProvableStruct instances in the context
    let mut fvarIds ← findProvableStructVars
    
    -- Also search for projections in the goal
    let varsInGoal ← findStructVars target
    -- Filter to only include those with ProvableStruct instances
    let mut filteredVarsInGoal := []
    for fvarId in varsInGoal do
      let type ← inferType (.fvar fvarId)
      let type' ← withTransparency .reducible (whnf type)
      let typeCtor := type'.getAppFn
      match typeCtor with
      | .const name _ =>
        try
          let instType ← mkAppM ``ProvableStruct #[.const name []]
          if let .some _ ← trySynthInstance instType then
            filteredVarsInGoal := fvarId :: filteredVarsInGoal
        catch _ => continue
      | _ => continue
    
    fvarIds := (fvarIds ++ filteredVarsInGoal).eraseDups
    
    if fvarIds.isEmpty then
      throwError "No variables with ProvableStruct instances found in the context or goal"
    
    -- Apply cases on each variable
    let mut currentGoal := goal
    let mut decomposed := false
    
    for fvarId in fvarIds do
      let localDecl ← fvarId.getDecl
      let userName := localDecl.userName
      
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
        -- Skip variables that can't be decomposed
        -- This can happen with type synonyms or other non-destructurable types
        continue
    
    if not decomposed then
      throwError "Failed to decompose any variables with ProvableStruct instances"
    
    replaceMainGoal [currentGoal]


/--
  Automatically decompose ALL variables with ProvableStruct instances that either:
  1. Are in the context as variables with ProvableStruct instances
  2. Appear in field projections in hypotheses (e.g., h : input.x = 5)
  3. Appear in field projections in the goal
  
  Example:
  ```lean
  theorem example_theorem (input : Inputs (F p)) (h : input.x = 5) : 
    input.y + input.z = someValue := by
    decompose_provable_struct  -- This will destruct `input` (found via projections)
    -- Now we have x, y, z in context with h : x = 5
    sorry
  ```
-/
elab "decompose_provable_struct" : tactic => decomposeProvableStruct


/--
  Print all ProvableStruct variables found in the context and goal
  (useful for debugging decompose_provable_struct)
-/
elab "show_provable_struct_vars" : tactic => do
  withMainContext do
    let goal ← getMainGoal
    let target ← goal.getType
    
    -- Find all variables with ProvableStruct instances in the context
    let mut fvarIds ← findProvableStructVars
    
    -- Also search for projections in the goal
    let varsInGoal ← findStructVars target
    -- Filter to only include those with ProvableStruct instances
    for fvarId in varsInGoal do
      let type ← inferType (.fvar fvarId)
      let type' ← withTransparency .reducible (whnf type)
      let typeCtor := type'.getAppFn
      match typeCtor with
      | .const name _ =>
        try
          let instType ← mkAppM ``ProvableStruct #[.const name []]
          if let .some _ ← trySynthInstance instType then
            fvarIds := fvarId :: fvarIds
        catch _ => continue
      | _ => continue
    
    fvarIds := fvarIds.eraseDups
    
    if fvarIds.isEmpty then
      logInfo "No ProvableStruct variables found in context or goal"
    else
      logInfo "Found ProvableStruct variables:"
      for fvarId in fvarIds do
        let localDecl ← fvarId.getDecl
        let type ← inferType localDecl.toExpr
        logInfo m!"  {localDecl.userName} : {type}"
