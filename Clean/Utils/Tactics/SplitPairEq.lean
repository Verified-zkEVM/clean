import Lean.Elab.Tactic
import Lean.Elab.Exception
import Clean.Circuit.Provable
import Clean.Utils.Tactics.DecomposeProvablePair

open Lean.Elab.Tactic
open Lean.Meta
open Lean

namespace ProvenZK

/--
  Check if an expression is a pair literal (Prod.mk application)
-/
def isPairConstructor (e : Expr) : MetaM Bool := do
  -- Use transparency to see through definitions
  let e' ← withTransparency .all (whnf e)
  match e'.getAppFn with
  | .const name _ =>
    -- Check if it's Prod.mk
    return name == ``Prod.mk
  | _ => return false

/--
  Extract all pair equalities from an expression (including inside conjunctions)
-/
partial def extractPairEqualities (e : Expr) : MetaM (List (Expr × Expr × Expr)) := do
  -- Returns list of (equality_expr, lhs, rhs) triples
  match e with
  | .app (.app (.const ``And _) left) right =>
    -- Handle conjunction
    let leftEqs ← extractPairEqualities left
    let rightEqs ← extractPairEqualities right
    return leftEqs ++ rightEqs
  | _ =>
    -- Check if it's an equality
    if e.isAppOf `Eq then
      if let (some lhs, some rhs) := (e.getArg? 1, e.getArg? 2) then
        return [(e, lhs, rhs)]
    return []

/--
  Find pair variables that appear in equalities with pair literals
  Returns a list of FVarIds that should have rcases applied
-/
def findPairVarsInEqualities : TacticM (List FVarId) := do
  withMainContext do
    let ctx ← getLCtx
    let mut pairVarsToCase := []
    
    -- Look for equalities in hypotheses (including inside conjunctions)
    for localDecl in ctx do
      if localDecl.isImplementationDetail then
        continue
      
      let type := localDecl.type
      
      -- Extract all equalities from this hypothesis (handles conjunctions)
      let equalities ← extractPairEqualities type
      
      for (_, lhs, rhs) in equalities do
        -- Check if one side is a pair constructor and the other is a variable
        let lhsIsConstructor ← isPairConstructor lhs
        let rhsIsConstructor ← isPairConstructor rhs
        
        if lhsIsConstructor && !rhsIsConstructor then
          -- pair_literal = variable
          match rhs with
          | .fvar fvarId =>
            -- Check if the variable has a provable pair type
            let varType ← inferType rhs
            if ← isProdTypeWithProvableType varType then
              pairVarsToCase := fvarId :: pairVarsToCase
          | _ => pure ()
        else if rhsIsConstructor && !lhsIsConstructor then
          -- variable = pair_literal
          match lhs with
          | .fvar fvarId =>
            -- Check if the variable has a provable pair type
            let varType ← inferType lhs
            if ← isProdTypeWithProvableType varType then
              pairVarsToCase := fvarId :: pairVarsToCase
          | _ => pure ()
    
    return pairVarsToCase.eraseDups

/--
  Split pair equalities using Prod.mk.injEq for all provable pair types
-/
def splitPairEq : TacticM Unit := do
  withMainContext do
    -- First, find and apply rcases on pair variables in equalities
    let varsToCase ← findPairVarsInEqualities
    
    if !varsToCase.isEmpty then
      for fvarId in varsToCase do
        try
          -- Use rcases instead of cases for better handling of pairs
          let ldecl ← fvarId.getDecl
          let userName := ldecl.userName
          let fstName := Name.mkSimple (userName.toString ++ "_fst")
          let sndName := Name.mkSimple (userName.toString ++ "_snd")
          evalTactic (← `(tactic| rcases $(mkIdent userName):ident with ⟨$(mkIdent fstName):ident, $(mkIdent sndName):ident⟩))
        catch _ => continue
    
    -- Apply Prod.mk.injEq lemma
    withMainContext do
      try
        evalTactic (← `(tactic| simp only [Prod.mk.injEq] at *))
      catch _ => pure ()

/--
  Automatically split pair equalities (where pair has provable type) into component-wise equalities.
  
  This tactic:
  1. First applies `rcases` on pair variables that appear in equalities with pair literals
  2. Then applies `Prod.mk.injEq` lemmas for all pairs found in the context
  
  It transforms equalities of the form:
  - `(a, b) = (c, d)` into `a = c ∧ b = d`
  - `(a, b) = variable` into `a = v1 ∧ b = v2` (after automatic rcases)
  - `variable = (a, b)` into `v1 = a ∧ v2 = b` (after automatic rcases)
  
  The tactic also looks inside conjunctions to find pair equalities:
  - `((a, b) = variable ∧ P)` → pair equality is found and split
  - Nested conjunctions are also supported
  
  Only works on pairs where both components have:
  - Field instances, or
  - Expression types, or  
  - ProvableType/ProvableStruct instances
  
  Example:
  ```lean
  example (x : F p × F p) (h : (5, 3) = x) : x.1 = 5 := by
    split_pair_eq
    -- x is automatically destructured via rcases
    -- The pair equality is split: h becomes 5 = x_fst ∧ 3 = x_snd
    exact h.1.symm
  ```
-/
elab "split_pair_eq" : tactic => splitPairEq

end ProvenZK