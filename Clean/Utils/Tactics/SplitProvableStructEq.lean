import Lean.Elab.Tactic
import Lean.Elab.Exception
import Clean.Circuit.Provable
import Clean.Utils.Tactics.ProvableTacticUtils

open Lean.Elab.Tactic
open Lean.Meta
open Lean

/--
  Find struct variables that appear in equalities with struct literals
  Returns a list of FVarIds that should have cases applied
-/
def findStructVarsInEqualities : TacticM (List FVarId) := do
  withMainContext do
    let ctx ← getLCtx
    let mut structVarsToCase := []

    -- Look for equalities in hypotheses (including inside conjunctions)
    for localDecl in ctx do
      if localDecl.isImplementationDetail then
        continue

      let type := localDecl.type

      -- Extract all equalities from this hypothesis (handles conjunctions)
      let equalities ← extractEqualities type

      for (_, lhs, rhs) in equalities do
        -- Check if one side is a struct constructor and the other is a variable
        let lhsIsConstructor ← isMkConstructor lhs
        let rhsIsConstructor ← isMkConstructor rhs

        if lhsIsConstructor && !rhsIsConstructor then
          -- struct_literal = variable
          match rhs with
          | .fvar fvarId =>
            -- Check if the variable has ProvableStruct
            let varType ← inferType rhs
            if ← hasProvableStructInstance varType then
              structVarsToCase := fvarId :: structVarsToCase
          | _ => pure ()
        else if rhsIsConstructor && !lhsIsConstructor then
          -- variable = struct_literal
          match lhs with
          | .fvar fvarId =>
            -- Check if the variable has ProvableStruct
            let varType ← inferType lhs
            if ← hasProvableStructInstance varType then
              structVarsToCase := fvarId :: structVarsToCase
          | _ => pure ()

    return structVarsToCase.eraseDups

/--
  Split struct equalities using mk.injEq for all ProvableStruct types
-/
def splitProvableStructEq : TacticM Unit := do
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
        catch e =>
          let ldecl ← fvarId.getDecl
          trace[Meta.Tactic] "Failed to apply cases to struct variable {ldecl.userName}: {e.toMessageData}"
          continue

      -- Update the goal after cases
      replaceMainGoal [currentGoal]

    -- Apply mk.injEq lemmas - much simpler approach
    withMainContext do
      -- Get environment to check which lemmas exist
      let env ← getEnv
      let mut lemmasToApply : List Ident := []

      -- Get all the types that appear in equalities (including inside conjunctions)
      let ctx ← getLCtx
      for localDecl in ctx do
        if localDecl.isImplementationDetail then
          continue

        let type := localDecl.type

        -- Extract all equalities from this hypothesis (handles conjunctions)
        let equalities ← extractEqualities type

        for (eqExpr, _, _) in equalities do
          -- Get the type argument (first argument of Eq)
          if let some typeExpr := eqExpr.getArg? 0 then
            -- Get the type constructor for finding mk.injEq
            let typeExpr' ← whnf typeExpr
            match typeExpr'.getAppFn with
            | .const typeName _ =>
              -- Check if mk.injEq exists for this type
              let mkInjEqName := typeName ++ `mk ++ `injEq
              if env.contains mkInjEqName then
                -- Check if the full type (not just the constructor) has ProvableStruct instance
                -- For types like MyStruct n (F p), check ProvableStruct (MyStruct n)
                if ← hasProvableStructInstance typeExpr' then
                  let lemmaIdent := mkIdent mkInjEqName
                  if !lemmasToApply.any (fun l => l.getId == mkInjEqName) then
                    lemmasToApply := lemmaIdent :: lemmasToApply
            | _ => pure ()

      -- Apply all the lemmas we found
      for lemmaIdent in lemmasToApply do
        try
          evalTactic (← `(tactic| simp only [$lemmaIdent:ident] at *))
        catch e =>
          trace[Meta.Tactic] "Failed to apply lemma {lemmaIdent}: {e.toMessageData}"
          continue

/--
  Automatically split struct equalities (where struct has ProvableStruct instance) into field-wise equalities.

  This tactic:
  1. First applies `cases` on struct variables that appear in equalities with struct literals
  2. Then applies `mk.injEq` lemmas for all ProvableStruct types found in the context

  It transforms equalities of the form:
  - `StructName.mk f1 f2 ... = StructName.mk v1 v2 ...` into `f1 = v1 ∧ f2 = v2 ∧ ...`
  - `StructName.mk f1 f2 ... = variable` into `f1 = v1 ∧ f2 = v2 ∧ ...` (after automatic cases)
  - `variable = StructName.mk f1 f2 ...` into `v1 = f1 ∧ v2 = f2 ∧ ...` (after automatic cases)

  The tactic also looks inside conjunctions to find struct equalities:
  - `(StructName.mk f1 f2 ... = variable ∧ P)` → struct equality is found and split
  - Nested conjunctions are also supported

  Note: The struct literal syntax `{ field1 := value1, ... }` is automatically handled.

  Only works on structures that have a ProvableStruct instance.

  Example:
  ```lean
  theorem example (input : TestInputs F)
      (h : TestInputs.mk 1 2 3 = input ∧ x = 7) :
      input.x = 1 := by
    split_provable_struct_eq
    -- input is automatically destructured via cases
    -- The struct equality inside the conjunction is found and split
    -- h.1 becomes: 1 = x ∧ 2 = y ∧ 3 = z
    exact h.1.1.symm
  ```
-/
elab "split_provable_struct_eq" : tactic => splitProvableStructEq
