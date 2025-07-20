import Lean.Elab.Tactic
import Lean.Elab.Exception
import Clean.Circuit.Provable

open Lean.Elab.Tactic
open Lean.Meta
open Lean

/--
  Check if an expression is a struct literal (constructor application)
-/
def isStructConstructor (e : Expr) : MetaM Bool := do
  -- Use transparency to see through definitions
  let e' ← withTransparency .all (whnf e)
  match e'.getAppFn with
  | .const name _ =>
    -- Check if it's a constructor (ends with .mk)
    return name.components.getLast? == some `mk
  | _ => return false

/--
  Find struct variables that appear in equalities with struct literals
  Returns a list of FVarIds that should have cases applied
-/
def findStructVarsInEqualities : TacticM (List FVarId) := do
  withMainContext do
    let ctx ← getLCtx
    let mut structVarsToCase := []
    
    -- Look for equalities in hypotheses
    for localDecl in ctx do
      if localDecl.isImplementationDetail then
        continue
      
      let type := localDecl.type
      
      -- Check if it's an equality using isAppOf
      if type.isAppOf `Eq then
        -- Get both sides of the equality
        if let (some lhs, some rhs) := (type.getArg? 1, type.getArg? 2) then
          -- Check if one side is a struct constructor and the other is a variable
          let lhsIsConstructor ← isStructConstructor lhs
          let rhsIsConstructor ← isStructConstructor rhs
          
          if lhsIsConstructor && !rhsIsConstructor then
            -- struct_literal = variable
            match rhs with
            | .fvar fvarId =>
              -- Check if the variable has ProvableStruct
              let varType ← inferType rhs
              let varType' ← withTransparency .reducible (whnf varType)
              match varType'.getAppFn with
              | .const typeName _ =>
                try
                  let instType ← mkAppM ``ProvableStruct #[.const typeName []]
                  match ← trySynthInstance instType with
                  | .some _ => structVarsToCase := fvarId :: structVarsToCase
                  | _ => pure ()
                catch _ => pure ()
              | _ => pure ()
            | _ => pure ()
          else if rhsIsConstructor && !lhsIsConstructor then
            -- variable = struct_literal
            match lhs with
            | .fvar fvarId =>
              -- Check if the variable has ProvableStruct
              let varType ← inferType lhs
              let varType' ← withTransparency .reducible (whnf varType)
              match varType'.getAppFn with
              | .const typeName _ =>
                try
                  let instType ← mkAppM ``ProvableStruct #[.const typeName []]
                  match ← trySynthInstance instType with
                  | .some _ => structVarsToCase := fvarId :: structVarsToCase
                  | _ => pure ()
                catch _ => pure ()
              | _ => pure ()
            | _ => pure ()
    
    return structVarsToCase.eraseDups

/--
  Split struct equalities using mk.injEq for all ProvableStruct types
-/
def splitStructEq : TacticM Unit := do
  withMainContext do
    -- First, find and apply cases on struct variables in equalities
    let varsToCase ← findStructVarsInEqualities
    
    if !varsToCase.isEmpty then
      let mut currentGoal ← getMainGoal
      for fvarId in varsToCase do
        try
          let casesResult ← currentGoal.cases fvarId
          match casesResult.toList with
          | [subgoal] =>
            currentGoal := subgoal.mvarId
          | _ => continue
        catch _ => continue
      
      -- Update the goal after cases
      replaceMainGoal [currentGoal]
    
    -- Apply mk.injEq lemmas - much simpler approach
    withMainContext do
      -- Get environment to check which lemmas exist
      let env ← getEnv
      let mut lemmasToApply : List Ident := []
      
      -- Get all the types that appear in equalities
      let ctx ← getLCtx
      for localDecl in ctx do
        if localDecl.isImplementationDetail then
          continue
          
        let type := localDecl.type
        -- Check if it's an equality
        if type.isAppOf `Eq then
          -- Get the type argument (first argument of Eq)
          if let some typeExpr := type.getArg? 0 then
            -- Get the type name
            let typeExpr' ← whnf typeExpr
            match typeExpr'.getAppFn with
            | .const typeName _ =>
              -- Check if mk.injEq exists for this type
              let mkInjEqName := typeName ++ `mk ++ `injEq
              if env.contains mkInjEqName then
                -- Check if type has ProvableStruct instance
                try
                  let instType ← mkAppM ``ProvableStruct #[.const typeName []]
                  match ← trySynthInstance instType with
                  | .some _ =>
                    let lemmaIdent := mkIdent mkInjEqName
                    if !lemmasToApply.any (fun l => l.getId == mkInjEqName) then
                      lemmasToApply := lemmaIdent :: lemmasToApply
                  | _ => pure ()
                catch _ => pure ()
            | _ => pure ()
      
      -- Apply all the lemmas we found
      for lemmaIdent in lemmasToApply do
        try
          evalTactic (← `(tactic| simp only [$lemmaIdent:ident] at *))
        catch _ => continue

/--
  Automatically split struct equalities (where struct has ProvableStruct instance) into field-wise equalities.
  
  This tactic:
  1. First applies `cases` on struct variables that appear in equalities with struct literals
  2. Then applies `mk.injEq` lemmas for all ProvableStruct types found in the context
  
  It transforms equalities of the form:
  - `StructName.mk f1 f2 ... = StructName.mk v1 v2 ...` into `f1 = v1 ∧ f2 = v2 ∧ ...`
  - `StructName.mk f1 f2 ... = variable` into `f1 = v1 ∧ f2 = v2 ∧ ...` (after automatic cases)
  - `variable = StructName.mk f1 f2 ...` into `v1 = f1 ∧ v2 = f2 ∧ ...` (after automatic cases)
  
  Note: The struct literal syntax `{ field1 := value1, ... }` is automatically handled.
  
  Only works on structures that have a ProvableStruct instance.
  
  Example:
  ```lean
  theorem example (input : TestInputs F)
      (h : TestInputs.mk 1 2 3 = input) : 
      input.x = 1 := by
    split_struct_eq
    -- input is automatically destructured via cases
    -- Then h is split into: 1 = x ∧ 2 = y ∧ 3 = z
    sorry
  ```
-/
elab "split_struct_eq" : tactic => splitStructEq