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
  Find field projections in an expression and return the base variable if it has a ProvableStruct instance
-/
partial def findProvableStructVars (e : Lean.Expr) : Lean.MetaM (List Lean.FVarId) := do
  let e' ← whnf e
  let rec go (e : Lean.Expr) (acc : List Lean.FVarId) : Lean.MetaM (List Lean.FVarId) := do
    match e with
    | .proj _ _ base => 
      -- Found a projection, check if base is a variable with ProvableStruct
      match base with
      | .fvar fvarId => 
        let localDecl ← fvarId.getDecl
        let type ← inferType localDecl.toExpr
        -- Get the type constructor
        let typeCtor := type.getAppFn
        -- Try to synthesize a ProvableStruct instance
        try
          let inst ← synthInstance (← mkAppM ``ProvableStruct #[typeCtor])
          return fvarId :: acc
        catch _ =>
          return acc
      | _ => go base acc
    | .app f a => 
      -- Check if this is a structure field access function
      match f with
      | .const name _ =>
        -- Check if it's a structure field accessor
        let env ← getEnv
        if let some projInfo := env.getProjectionFnInfo? name then
          -- This is a projection function, check the argument
          match a with
          | .fvar fvarId =>
            let localDecl ← fvarId.getDecl
            let type ← inferType localDecl.toExpr
            let typeCtor := type.getAppFn
            try
              let inst ← synthInstance (← mkAppM ``ProvableStruct #[typeCtor])
              return fvarId :: acc
            catch _ =>
              return acc
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
  Find all variables in the context that have a ProvableStruct instance,
  including those that appear in field projections in hypotheses
-/
def findAllProvableStructVars : Lean.Elab.Tactic.TacticM (List Lean.FVarId) := do
  withMainContext do
    let ctx ← Lean.MonadLCtx.getLCtx
    let mut result := []
    
    -- First, find all variables that directly have ProvableStruct instances
    for localDecl in ctx do
      if localDecl.isImplementationDetail then
        continue
      
      let type ← inferType localDecl.toExpr
      let typeCtor := type.getAppFn
      
      try
        let _ ← synthInstance (← mkAppM ``ProvableStruct #[typeCtor])
        result := localDecl.fvarId :: result
      catch _ =>
        continue
    
    -- Also search for projections in the types of hypotheses
    for localDecl in ctx do
      if localDecl.isImplementationDetail then
        continue
      
      -- Search in the type of each hypothesis
      let varsInType ← findProvableStructVars localDecl.type
      result := result ++ varsInType
    
    -- Remove duplicates and return
    return result.eraseDups

/--
  Decompose all variables with ProvableStruct instances in the context
-/
def decomposeProvableStruct : Lean.Elab.Tactic.TacticM Unit := do
  withMainContext do
    let goal ← getMainGoal
    let target ← goal.getType
    
    -- Find all variables with ProvableStruct in the context
    let mut fvarIds ← findAllProvableStructVars
    
    -- Also search for projections in the goal
    let varsInGoal ← findProvableStructVars target
    fvarIds := (fvarIds ++ varsInGoal).eraseDups
    
    if fvarIds.isEmpty then
      throwError "No variables with ProvableStruct instances found in the context or goal"
    
    -- Apply cases on each variable
    let mut currentGoal := goal
    for fvarId in fvarIds do
      let localDecl ← fvarId.getDecl
      let userName := localDecl.userName
      
      -- Use cases tactic on the variable
      let casesResult ← currentGoal.cases fvarId
      
      -- Get the new goal from the cases result
      match casesResult.toList with
      | [subgoal] => 
        currentGoal := subgoal.mvarId
      | _ => 
        throwError s!"Unexpected result from cases on {userName}"
    
    replaceMainGoal [currentGoal]

/--
  Decompose a specific variable with a ProvableStruct instance
-/
def decomposeProvableStructVar (fvarId : Lean.FVarId) : Lean.Elab.Tactic.TacticM Unit := do
  withMainContext do
    let goal ← getMainGoal
    
    -- Check if the variable has a ProvableStruct instance
    let localDecl ← fvarId.getDecl
    let type ← inferType localDecl.toExpr
    
    -- Extract the type constructor (e.g., TestInputs from TestInputs F)
    let typeCtor := type.getAppFn
    
    try
      let _ ← synthInstance (← mkAppM ``ProvableStruct #[typeCtor])
    catch _ =>
      throwError s!"Variable {localDecl.userName} does not have a ProvableStruct instance for type {type}"
    
    -- Use cases tactic on the variable
    let casesResult ← goal.cases fvarId
    
    -- Get the new goal from the cases result
    match casesResult.toList with
    | [subgoal] => 
      replaceMainGoal [subgoal.mvarId]
    | _ => 
      throwError s!"Unexpected result from cases on {localDecl.userName}"

/--
  Automatically decompose ALL variables with ProvableStruct instances that either:
  1. Are in the context as variables with ProvableStruct types
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
  Decompose a specific variable with a ProvableStruct instance by name
  
  Example:
  ```lean
  theorem example_theorem (input : Inputs (F p)) : 
    input.x + input.y = someValue := by
    decompose_provable_struct input  -- Explicitly destruct `input`
    -- Now we have x, y in context instead of input
    sorry
  ```
-/
elab "decompose_provable_struct" e:ident : tactic => withMainContext do
  let fvar ← getFVarId e
  decomposeProvableStructVar fvar
