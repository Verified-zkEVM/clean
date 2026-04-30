import Lean.Elab.Tactic
import Lean.Elab.Exception
import Clean.Circuit.Provable
import Clean.Utils.Tactics.ProvableTacticUtils
import Clean.Utils.Tactics.ProvableStructNaming

open Lean.Elab.Tactic
open Lean.Meta
open Lean
open ProvableStructNaming

private def derivedCircuitTypeOfValueType? (type : Expr) : Option Expr :=
  if type.getAppFn.isConstOf ``CircuitType.Value then
    type.getAppArgs[0]?
  else if type.getAppFn.isConstOf ``CircuitType.ProverValue then
    type.getAppArgs[0]?
  else
    none

private def hasDerivedCircuitType (m : Expr) : MetaM Bool := do
  let instType ← mkAppM ``DerivedCircuitType #[m]
  match ← trySynthInstance instType with
  | .some _ => return true
  | _ => return false

private def hasDerivedCircuitTypeValueType (type : Expr) : MetaM Bool := do
  match derivedCircuitTypeOfValueType? type with
  | some m => hasDerivedCircuitType m
  | none => return false

private def mkInjNameFromConstructor? (e : Expr) : MetaM (Option Name) := do
  let env ← getEnv
  match e.consumeMData.getAppFn with
  | .const name _ =>
    if name.components.getLast? == some `mk then
      let mkInjName := name ++ `inj
      if env.contains mkInjName then
        return some mkInjName
    return none
  | _ => return none

private def addIdentLemmaIfMissing
    (lemmas : Array (TSyntax `Lean.Parser.Tactic.simpLemma)) (lemmaName : Name) :
    MetaM (Array (TSyntax `Lean.Parser.Tactic.simpLemma)) := do
  let key := toString lemmaName
  if lemmas.any (fun l => toString l == key) then
    return lemmas
  else
    let lemmaIdent := mkIdent lemmaName
    return lemmas.push (← `(Lean.Parser.Tactic.simpLemma| $lemmaIdent:ident))

private def splitDerivedCircuitTypeEqualities : TacticM Unit := do
  withMainContext do
    let ctx ← getLCtx
    for localDecl in ctx do
      if localDecl.isImplementationDetail then
        continue

      let type ← instantiateMVars localDecl.type
      unless type.isAppOf `Eq do
        continue
      let some typeExpr := type.getArg? 0
        | continue
      unless ← hasDerivedCircuitTypeValueType typeExpr do
        continue

      let some lhs := type.getArg? 1
        | continue
      let some rhs := type.getArg? 2
        | continue

      let mut split := false
      for side in #[lhs, rhs] do
        unless split do
          if let some mkInjName ← mkInjNameFromConstructor? side then
            try
              let hypIdent := mkIdent localDecl.userName
              let injIdent := mkIdent mkInjName
              evalTactic (← `(tactic| replace $hypIdent:ident := $injIdent:ident $hypIdent:ident))
              split := true
            catch e =>
              trace[Meta.Tactic] "Failed to inject derived CircuitType equality {localDecl.userName}: {e.toMessageData}"

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
            -- Keep ordinary records opaque: besides ProvableStruct variables,
            -- only DerivedCircuitType variables opt into splitting here.
            let varType ← inferType rhs
            if (← hasProvableStructInstance varType) || (← hasDerivedCircuitTypeValueType varType) then
              structVarsToCase := fvarId :: structVarsToCase
          | _ => pure ()
        else if rhsIsConstructor && !lhsIsConstructor then
          -- variable = struct_literal
          match lhs with
          | .fvar fvarId =>
            -- Keep ordinary records opaque: besides ProvableStruct variables,
            -- only DerivedCircuitType variables opt into splitting here.
            let varType ← inferType lhs
            if (← hasProvableStructInstance varType) || (← hasDerivedCircuitTypeValueType varType) then
              structVarsToCase := fvarId :: structVarsToCase
          | _ => pure ()

    return structVarsToCase.eraseDups

/--
  Split struct equalities using mk.injEq for all ProvableStruct types
-/
def splitProvableStructEq : TacticM Unit := do
  withMainContext do
    -- Struct equalities sometimes have a wrapper equality type such as
    -- `Value MyStruct F` or `ProverValue MyStruct F`. Normalize those type
    -- wrappers before looking for constructor equalities, so generated
    -- `MyStruct.mk.injEq` lemmas can match.
    try
      evalTactic (← `(tactic|
        simp only [CircuitType.value_of_provableType, CircuitType.proverValue_of_provableType] at *))
    catch _ =>
      pure ()

    -- First, find and apply cases on struct variables in equalities
    let varsToCase ← findStructVarsInEqualities

    if !varsToCase.isEmpty then
      let mut currentGoal ← getMainGoal
      for fvarId in varsToCase do
        try
          -- Generate field-based names for the struct variable
          let altVarNames ← generateStructFieldNames fvarId

          -- Use cases tactic on the variable with custom names
          let casesResult ← currentGoal.cases fvarId #[altVarNames]

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

    -- DerivedCircuitType equalities can have equality types like
    -- `Value M F` / `ProverValue M F`, which do not expose the generated
    -- `mk.injEq` theorem to simp. Constructor injection splits them directly.
    try
      splitDerivedCircuitTypeEqualities
    catch _ =>
      pure ()

    -- Apply mk.injEq lemmas - much simpler approach
    withMainContext do
      let mut lemmasToApply : Array (TSyntax `Lean.Parser.Tactic.simpLemma) := #[]

      -- Get all the types that appear in equalities (including inside conjunctions)
      let ctx ← getLCtx
      for localDecl in ctx do
        if localDecl.isImplementationDetail then
          continue

        let type := localDecl.type

        -- Extract all equalities from this hypothesis (handles conjunctions)
        let equalities ← extractEqualities type

        for (eqExpr, lhs, rhs) in equalities do
          -- Get the type argument (first argument of Eq)
          if let some typeExpr := eqExpr.getArg? 0 then
            -- Get the type constructor for finding mk.injEq. Reducible
            -- normalization lets `Value Input F` expose the generated
            -- `Input.Value.mk.injEq` lemma.
            if let some mkInjEqName ← mkInjEqNameFromType? typeExpr then
              if (← hasProvableStructInstance typeExpr) || (← hasDerivedCircuitTypeValueType typeExpr) then
                lemmasToApply ← addIdentLemmaIfMissing lemmasToApply mkInjEqName

            -- If a DerivedCircuitType equality type is hidden behind an opaque class
            -- projection, recover the injector lemma from constructor sides
            -- directly. Do not use this path for arbitrary record equalities.
            if ← hasDerivedCircuitTypeValueType typeExpr then
              for side in #[lhs, rhs] do
                if let some mkInjEqName ← mkInjEqNameFromConstructor? side then
                  lemmasToApply ← addIdentLemmaIfMissing lemmasToApply mkInjEqName

      -- Apply all the lemmas we found
      if !lemmasToApply.isEmpty then
        try
          evalTactic (← `(tactic| simp only [$[$lemmasToApply],*] at *))
        catch e =>
          trace[Meta.Tactic] "Failed to apply struct equality lemmas: {e.toMessageData}"

/--
  Automatically split struct equalities (where struct has ProvableStruct instance) into field-wise equalities.

  This tactic:
  1. First applies `cases` on struct variables that appear in equalities with struct literals
  2. Then applies `mk.injEq` lemmas for all ProvableStruct types in equations involving struct literals

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
