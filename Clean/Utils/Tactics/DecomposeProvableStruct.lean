import Lean.Elab.Tactic
import Lean.Elab.Exception
import Clean.Circuit.Provable

open Lean.Elab.Tactic
open Lean.Meta
open Lean

/--
  Find field projections in an expression and return the base variable if it's a structure
-/
partial def findStructVars (e : Lean.Expr) : Lean.MetaM (List Lean.FVarId) := do
  let rec go (e : Lean.Expr) (acc : List Lean.FVarId) : Lean.MetaM (List Lean.FVarId) := do
    match e with
    | .proj _ _ base =>
      -- Found a projection, check if base is a variable
      match base with
      | .fvar fvarId =>
        return fvarId :: acc
      | _ => go base acc
    | .app _ _ =>
      -- Check if this is a structure field access function application
      -- Get the function and all its arguments
      let f := e.getAppFn
      let args := e.getAppArgs
      match f with
      | .const name _ =>
        -- Check if it's a structure field accessor
        let env ← getEnv
        if let some projInfo := env.getProjectionFnInfo? name then
          -- This is a projection function
          -- The struct instance is at position projInfo.numParams
          if h : projInfo.numParams < args.size then
            let structArg := args[projInfo.numParams]
            match structArg with
            | .fvar fvarId =>
              -- Also continue searching in other arguments
              let acc' ← args.foldlM (fun acc arg => go arg acc) acc
              return fvarId :: acc'
            | _ =>
              -- Continue searching in all arguments
              args.foldlM (fun acc arg => go arg acc) acc
          else
            -- Not enough arguments, continue searching
            args.foldlM (fun acc arg => go arg acc) acc
        else
          -- Regular application, search in function and all arguments
          let acc' ← go f acc
          args.foldlM (fun acc arg => go arg acc) acc'
      | _ =>
        -- Regular application, search in function and all arguments
        let acc' ← go f acc
        args.foldlM (fun acc arg => go arg acc) acc'
    | .lam _ _ body _ | .forallE _ _ body _ =>
      -- For binders, check the body
      go body acc
    | .letE _ _ val body _ =>
      -- For let expressions, check both value and body
      let acc' ← go val acc
      go body acc'
    | .mdata _ expr => go expr acc
    | _ => return acc

  go e []

/--
  Find all variables that have ProvableStruct instances AND appear in field projections
  in hypotheses or the goal (not just any variable with a ProvableStruct type)
-/
def findProvableStructVars : Lean.Elab.Tactic.TacticM (List Lean.FVarId) := do
  withMainContext do
    let ctx ← Lean.MonadLCtx.getLCtx
    let mut result := []

    -- Helper function to check if an fvarId has a ProvableStruct instance
    let hasProvableStructInstance (fvarId : Lean.FVarId) : Lean.MetaM Bool := do
      let type ← inferType (.fvar fvarId)
      let type' ← withTransparency .reducible (whnf type)
      -- For a type like `Inputs n (F p)`, we want to check `ProvableStruct (Inputs n)`
      -- So we need to extract the type constructor with its type parameters (but not value parameters)
      match type' with
      | .app typeCtor _ =>
        -- type' is something like `Inputs n (F p)`
        -- typeCtor is `Inputs n`
        try
          let instType ← mkAppM ``ProvableStruct #[typeCtor]
          if let .some _ ← trySynthInstance instType then
            return true
          else
            return false
        catch _ => return false
      | _ => return false

    -- Search for projections in the types of hypotheses
    for localDecl in ctx do
      if localDecl.isImplementationDetail then
        continue

      -- Search in the type of each hypothesis
      let varsInType ← findStructVars localDecl.type
      -- Filter to only include those with ProvableStruct instances
      for fvarId in varsInType do
        if ← hasProvableStructInstance fvarId then
          result := fvarId :: result

    -- Also search for projections in the goal
    let goal ← getMainGoal
    let target ← goal.getType
    let varsInGoal ← findStructVars target
    -- Filter to only include those with ProvableStruct instances
    for fvarId in varsInGoal do
      if ← hasProvableStructInstance fvarId then
        result := fvarId :: result

    -- Remove duplicates and return
    return result.reverse.eraseDups

/--
  Decompose all ProvableStruct variables that appear in projections
-/
def decomposeProvableStruct : Lean.Elab.Tactic.TacticM Unit := do
  withMainContext do
    let goal ← getMainGoal

    -- Find all variables with ProvableStruct instances that appear in projections
    let fvarIds ← findProvableStructVars

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
      catch e =>
        -- Skip variables that can't be decomposed
        -- This can happen with type synonyms or other non-destructurable types
        trace[Meta.Tactic] "Failed to decompose struct variable {userName}: {e.toMessageData}"
        continue

    if not decomposed then
      throwError "Failed to decompose any variables with ProvableStruct instances"

    replaceMainGoal [currentGoal]

/--
  Automatically decompose ALL variables with ProvableStruct instances that either:
  1. appear in field projections in hypotheses (e.g., h : input.x = 5)
  2. appear in field projections in the goal

  Note:
  - The new variables introduced by decomposition are not explicitly named.
    Use `rename_i` after this tactic to give them names.
  - This tactic only performs one level of decomposition. For nested structures,
    it will decompose the outer structure but not the inner ones. Use under
    `repeat` to decompose nested structures fully. `provable_struct_simp` is one
    implementation of such a loop.

  Example:
  ```lean
  theorem example_theorem (input : Inputs (F p)) (h : input.x = 5) :
    input.y + input.z = someValue := by
    decompose_provable_struct  -- This will destruct `input` (found via projections)
    -- Now we have auto-named variables for x, y and z components in context
    -- and h has been updated to reference the new x component
    sorry
  ```
-/
elab "decompose_provable_struct" : tactic => decomposeProvableStruct

/--
  Print all ProvableStruct variables found in projections in the context and goal
  (useful for debugging decompose_provable_struct)
-/
elab "show_provable_struct_vars" : tactic => do
  withMainContext do
    -- Find all variables with ProvableStruct instances that appear in projections
    let fvarIds ← findProvableStructVars

    if fvarIds.isEmpty then
      logInfo "No ProvableStruct variables found in context or goal"
    else
      logInfo "Found ProvableStruct variables:"
      for fvarId in fvarIds do
        let localDecl ← fvarId.getDecl
        let type ← inferType localDecl.toExpr
        logInfo m!"  {localDecl.userName} : {type}"
