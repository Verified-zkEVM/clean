import Lean.Elab.Tactic
import Lean.Elab.Exception
import Clean.Circuit.Provable

open Lean.Elab.Tactic
open Lean.Meta
open Lean

/--
  Find pair projections in an expression and return the base variable if it's a pair
-/
partial def findPairVars (e : Lean.Expr) : Lean.MetaM (List Lean.FVarId) := do
  let rec go (e : Lean.Expr) (acc : List Lean.FVarId) : Lean.MetaM (List Lean.FVarId) := do
    match e with
    | .app f a =>
      -- Check if this is Prod.fst or Prod.snd application
      let f' := f.getAppFn
      match f' with
      | .const name _ =>
        -- Check for both Prod.fst/snd and the desugared names
        if name == ``Prod.fst || name == ``Prod.snd then
          -- The pair should be the last argument
          match a with
          | .fvar fvarId => 
            let acc' ← go f acc
            return fvarId :: acc'
          | _ =>
            let acc' ← go f acc
            go a acc'
        else
          -- Regular application, search in function and argument
          let acc' ← go f acc
          go a acc'
      | _ =>
        -- Search in function and argument
        let acc' ← go f acc
        go a acc'
    | .forallE _ type body _ =>
      let acc' ← go type acc
      go body acc'
    | .lam _ type body _ =>
      let acc' ← go type acc
      go body acc'
    | .letE _ type value body _ =>
      let acc' ← go type acc
      let acc'' ← go value acc'
      go body acc''
    | .mdata _ e => go e acc
    | _ => return acc
  go e []

/--
  Check if a type is a product type (Prod or similar)
-/
def isProdType (type : Lean.Expr) : Lean.MetaM Bool := do
  let type ← whnf type
  match type with
  | .app (.app (.const ``Prod _) _) _ => return true
  | _ => return false

/--
  Find all pair variables that appear in projections in the context and goal
-/
def findPairVarsInContext : TacticM (List Lean.FVarId) := withMainContext do
  let mut fvarIds : List Lean.FVarId := []
  
  -- Check hypotheses
  let ctx ← getLCtx
  for decl in ctx do
    if !decl.isImplementationDetail then
      let vars ← findPairVars decl.type
      fvarIds := fvarIds ++ vars
      if let some value := decl.value? then
        let vars ← findPairVars value
        fvarIds := fvarIds ++ vars
  
  -- Check goal
  let goal ← getMainTarget
  let vars ← findPairVars goal
  fvarIds := fvarIds ++ vars
  
  -- Remove duplicates and filter for actual pairs
  let mut uniqueFVarIds : List Lean.FVarId := []
  for fvarId in fvarIds do
    if !uniqueFVarIds.contains fvarId then
      let type ← inferType (.fvar fvarId)
      if ← isProdType type then
        uniqueFVarIds := uniqueFVarIds.cons fvarId
  
  return uniqueFVarIds

/--
  Decompose a single pair variable using rcases pattern
-/
def decomposePairVar (fvarId : Lean.FVarId) : TacticM Unit := do
  let ldecl ← fvarId.getDecl
  let userName := ldecl.userName
  
  -- Generate names for components
  let fstName := Name.mkSimple (userName.toString ++ "_fst")
  let sndName := Name.mkSimple (userName.toString ++ "_snd")
  
  -- Use rcases tactic syntax
  evalTactic (← `(tactic| rcases $(mkIdent userName):ident with ⟨$(mkIdent fstName):ident, $(mkIdent sndName):ident⟩))

/--
  Main tactic: decompose all pair variables that appear in projections
-/
def decomposeProvablePair : TacticM Unit := do
  let fvarIds ← findPairVarsInContext
  
  if fvarIds.isEmpty then
    -- Don't log anything when no pairs found
    return ()
  else
    for fvarId in fvarIds do
      try
        decomposePairVar fvarId
      catch _ =>
        -- Silently skip errors
        return ()

/--
  Tactic to decompose variables of pair types (like ProvablePair or fieldPair) that appear in projections.
  
  This tactic finds all variables of product type that appear in projections like `.1`, `.2`, 
  `Prod.fst`, or `Prod.snd` and decomposes them into their components.
  
  Example:
  ```lean
  example (input : F × F) (h : input.1 = 5) : input.2 + 5 = input.1 + input.2 := by
    decompose_provable_pair
    -- Now we have input_fst : F, input_snd : F instead of input
    -- and h : input_fst = 5
    sorry
  ```
-/
elab "decompose_provable_pair" : tactic => decomposeProvablePair

/--
  Print all pair variables found in the context and goal
  (useful for debugging decompose_provable_pair)
-/
elab "show_pair_vars" : tactic => do
  withMainContext do
    let fvarIds ← findPairVarsInContext
    if fvarIds.isEmpty then
      logInfo "No pair variables found in projections"
    else
      logInfo "Found pair variables in projections:"
      for fvarId in fvarIds do
        let ldecl ← fvarId.getDecl  
        let type ← inferType (.fvar fvarId)
        logInfo m!"  {ldecl.userName} : {type}"