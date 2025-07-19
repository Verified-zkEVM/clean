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
  Decompose variables with ProvableStruct instances that appear in field projections in the goal
-/
def decomposeProvableStruct : Lean.Elab.Tactic.TacticM Unit := do
  withMainContext do
    let goal ← getMainGoal
    let target ← goal.getType
    
    -- Find all variables with ProvableStruct that appear in projections
    let fvarIds ← findProvableStructVars target
    let uniqueFvarIds := fvarIds.eraseDups
    
    if uniqueFvarIds.isEmpty then
      throwError "No variables with ProvableStruct instances found in field projections"
    
    -- Apply cases on each variable
    let mut currentGoal := goal
    for fvarId in uniqueFvarIds do
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
  Automatically decompose variables with ProvableStruct instances when they appear 
  in field access patterns (like x.component) in the goal.
  
  Example:
  ```lean
  theorem example_theorem (input : Inputs (F p)) : 
    input.x + input.y = someValue := by
    decompose_provable_struct  -- This will automatically destruct `input`
    -- Now we have x, y in context instead of input
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
