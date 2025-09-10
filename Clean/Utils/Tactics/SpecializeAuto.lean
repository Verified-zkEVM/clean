import Lean.Elab.Tactic
import Lean.Elab.Exception

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
