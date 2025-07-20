import Lean.Elab.Tactic
import Lean.Elab.Exception
import Clean.Circuit.Provable

open Lean.Elab.Tactic
open Lean.Meta
open Lean

/--
  Split struct equalities using mk.injEq for all ProvableStruct types
-/
def splitStructEq : TacticM Unit := do
  withMainContext do
    -- Collect all structure types with ProvableStruct instances from the context
    let ctx ← getLCtx
    let mut mkInjEqLemmas := []
    let mut foundTypes : List Name := []
    
    for localDecl in ctx do
      if localDecl.isImplementationDetail then
        continue
      
      -- Get the type
      let type ← inferType localDecl.toExpr
      let type' ← withTransparency .reducible (whnf type)
      
      -- Check if it's a structure type with ProvableStruct
      match type'.getAppFn with
      | .const typeName _ =>
        if foundTypes.contains typeName then
          continue
        
        -- Check if it has ProvableStruct instance
        try
          let instType ← mkAppM ``ProvableStruct #[.const typeName []]
          match ← trySynthInstance instType with
          | .some _ => 
            foundTypes := typeName :: foundTypes
            let mkInjEqName := typeName ++ `mk ++ `injEq
            mkInjEqLemmas := mkIdent mkInjEqName :: mkInjEqLemmas
          | _ => continue
        catch _ => continue
      | _ => continue
    
    -- Apply simp with all collected mk.injEq lemmas
    if !mkInjEqLemmas.isEmpty then
      -- Apply each lemma individually
      for lemmaIdent in mkInjEqLemmas do
        try
          evalTactic (← `(tactic| simp only [$lemmaIdent:ident] at *))
        catch _ =>
          -- Skip if lemma doesn't apply
          continue

/--
  Automatically split struct equalities (where struct has ProvableStruct instance) into field-wise equalities.
  
  This tactic applies `mk.injEq` lemmas for all ProvableStruct types found in the context.
  
  It transforms equalities of the form:
  - `StructName.mk f1 f2 ... = StructName.mk v1 v2 ...` into `f1 = v1 ∧ f2 = v2 ∧ ...`
  
  Note: 
  - The struct literal syntax `{ field1 := value1, ... }` is automatically handled.
  - For equalities involving struct variables (e.g., `StructName.mk ... = variable`), 
    you may need to apply `decompose_provable_struct` or `cases` on the variable first.
  
  Only works on structures that have a ProvableStruct instance.
  
  Example:
  ```lean
  theorem example (dummy : TestInputs F)
      (h : TestInputs.mk 1 2 3 = TestInputs.mk 4 5 6) : 
      1 = 4 := by
    split_struct_eq
    -- Now h is: 1 = 4 ∧ 2 = 5 ∧ 3 = 6
    exact h.1
  ```
-/
elab "split_struct_eq" : tactic => splitStructEq