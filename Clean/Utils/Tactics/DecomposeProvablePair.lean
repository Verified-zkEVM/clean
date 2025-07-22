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

mutual
  /--
    Check if a type looks like it comes from a ProvableType, ProvableStruct, or is an Expression type
    Optimized to reduce the number of type class instance lookups
  -/
  partial def isProvableTypeOrStructOrExpression (type : Lean.Expr) : Lean.MetaM Bool := do
    try
      -- Fast path: Check common patterns first before expensive instance synthesis
      
      -- Case 1: Direct Expression type (very common)
      match type with
      | .app (.const ``Expression _) fieldType =>
        -- Expression F requires Field F
        let fieldClass ← mkAppM ``Field #[fieldType]
        match ← trySynthInstance fieldClass with
        | .some _ => return true
        | _ => pure ()
      | _ => pure ()

      -- Case 2: Check if it's a known Field type (F, F p, etc.)
      -- This is cheaper than checking product types
      let fieldClass ← mkAppM ``Field #[type]
      match ← trySynthInstance fieldClass with
      | .some _ => return true
      | _ => pure ()

      -- Case 3: Check if it's a product type - but avoid recursive call if possible
      match type with
      | .app (.app (.const ``Prod _) α) β =>
        -- For Prod α β, both components must be provable
        -- Do a quick check first - if either is obviously not provable, skip
        let αSimple := α.isSort || α.isFVar || α.isMVar
        let βSimple := β.isSort || β.isFVar || β.isMVar
        if αSimple || βSimple then
          return false
        -- Otherwise do the full check
        if ← isProdTypeWithProvableType type then
          return true
      | _ => pure ()

      -- Case 4: For type applications, check the type constructor
      match type with
      | .app typeMap _ =>
        -- Try both ProvableType and ProvableStruct in one go
        let provableTypeClass ← mkAppM ``ProvableType #[typeMap]
        let provableStructClass ← mkAppM ``ProvableStruct #[typeMap]
        
        -- Check both type classes
        match ← trySynthInstance provableTypeClass with
        | .some _ => return true
        | _ => 
          match ← trySynthInstance provableStructClass with
          | .some _ => return true
          | _ => return false
      | _ =>
        -- Case 5: Abstract type map candidates
        -- This is the most expensive case, so we do it last
        let typeMapCandidates ← extractTypeMapCandidates type
        for typeMap in typeMapCandidates do
          -- Check both instances for each candidate
          let provableTypeClass ← mkAppM ``ProvableType #[typeMap]
          match ← trySynthInstance provableTypeClass with
          | .some _ => return true
          | _ =>
            let provableStructClass ← mkAppM ``ProvableStruct #[typeMap]
            match ← trySynthInstance provableStructClass with
            | .some _ => return true
            | _ => continue
        
        return false
    catch _ =>
      return false
  where
    -- Extract potential TypeMap expressions from a type
    extractTypeMapCandidates (type : Lean.Expr) : Lean.MetaM (List Lean.Expr) := do
      -- If type looks like `SomeType F` where F might be a field,
      -- return [SomeType] as a candidate TypeMap
      match type with
      | .app f _ => return [f]
      | _ => return []

  /--
    Check if a type is a product type (Prod or similar) that comes from a ProvableType
  -/
  partial def isProdTypeWithProvableType (type : Lean.Expr) : Lean.MetaM Bool := do
    -- Special case: Check if it's Var fieldPair _ or Var fieldTriple _ BEFORE reduction
    match type with
    | .app (.app (.const ``Var _) (.const ``fieldPair _)) _ =>
      return true
    | .app (.app (.const ``Var _) (.const ``fieldTriple _)) _ =>
      return true
    | _ => pure ()

    let type ← whnf type

    -- First check if it's a product type
    match type with
    | .app (.app (.const ``Prod _) α) β =>
      -- General case: check if both components are provable
      try
        let αProvable ← isProvableTypeOrStructOrExpression α
        let βProvable ← isProvableTypeOrStructOrExpression β

        if αProvable && βProvable then
          -- Both components are provable, so this pair should be decomposable
          return true
        else
          return false
      catch _ =>
        return false
    | _ =>
      -- Check if it's a direct application of a TypeMap with ProvableType
      try
        match type with
        | .app typeMap _ =>
          -- Check if typeMap has ProvableType instance
          let provableTypeClass ← mkAppM ``ProvableType #[typeMap]
          let inst? ← trySynthInstance provableTypeClass
          match inst? with
          | .some _ => return true
          | .none => return false
          | .undef => return false
        | _ => return false
      catch _ =>
        return false
end

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

  -- Remove duplicates and filter for actual pairs with ProvableType
  let mut uniqueFVarIds : List Lean.FVarId := []
  for fvarId in fvarIds do
    if !uniqueFVarIds.contains fvarId then
      let type ← inferType (.fvar fvarId)
      let isProvable ← isProdTypeWithProvableType type
      if isProvable then
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
def decomposeProvablePair : TacticM Unit := withMainContext do
  let fvarIds ← findPairVarsInContext

  if fvarIds.isEmpty then
    -- Don't log anything when no pairs found
    return ()
  else
    for fvarId in fvarIds do
      try
        decomposePairVar fvarId
      catch e =>
        -- Log the error for debugging but continue with other variables
        trace[Meta.Tactic] "Failed to decompose pair variable: {e.toMessageData}"
        -- Don't return early - continue with other variables
        continue

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
        let typeProvable ← isProdTypeWithProvableType type
        logInfo m!"  {ldecl.userName} : {type} (provable: {typeProvable})"
