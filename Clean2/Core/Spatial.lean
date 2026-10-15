/-
The `spatial` tactic: discharges the spatial obligation of an implementation
(`{inputs exist} main {well-formed ∗ outputs exist}`) mechanically.

After normalization, the obligation is a tree of `∧` and `→` whose leaves are
`footprint v ⊆ Alloc s'`, with hypotheses of the same shape (the inputs' footprints,
each call's `post`, and heap growth). The tree is split *syntactically*, never unfolding
`⊆`, and each leaf is closed by chaining hypotheses with `Set.Subset.trans`.
-/
module

public import Clean2.Core.Circuit
public import Clean2.Core.CType
public import Lean.Elab.Tactic
public import Mathlib.Tactic.CasesM

@[expose] public section

open Lean Elab Tactic Meta

namespace Clean2

meta section

/-- Destructure every hypothesis whose type is a product (inputs are tuples of variables),
so that the pattern-matching `main` reduces. -/
partial def destructProds : TacticM Unit := do
  let goal ← getMainGoal
  let fvar? ← goal.withContext do
    let lctx ← getLCtx
    let mut r := none
    for decl in lctx do
      if decl.isImplementationDetail then continue
      let ty ← whnfR decl.type
      if ty.isAppOfArity ``Prod 2 then
        r := some decl.fvarId
        break
    pure r
  match fvar? with
  | some fvarId =>
    let subgoals ← goal.cases fvarId
    setGoals (subgoals.map (·.mvarId)).toList
    destructProds
  | none => pure ()

/-- `A ⊆ B` or `A ≤ B` between sets: `(α, A, B)`. -/
def subsetParts? (t : Expr) : Option (Expr × Expr × Expr) :=
  match t.app4? ``HasSubset.Subset <|> t.app4? ``LE.le with
  | some (ty, _, a, b) => if ty.isAppOfArity ``Set 1 then some (ty.appArg!, a, b) else none
  | none => none

/-- Close a leaf `A ⊆ C` by a path `A ⊆ B₁ ⊆ … ⊆ C` of hypotheses, found by breadth-first search on
the graph whose edges are the hypotheses `X ⊆ Y`, comparing sets up to reducible unfolding (the
same footprint can be stated at two reducibly equal shapes). Polynomial in the number of
hypotheses, where a depth-first search through `Set.Subset.trans` is exponential: the
terms are large (nested states), and every failed unification is expensive. -/
def chainLeaf : TacticM Bool := do
  let goal ← getMainGoal
  goal.withContext do
    let some (α, lhs, rhs) := subsetParts? (← instantiateMVars (← goal.getType)).cleanupAnnotations | return false
    let u ← getDecLevel α
    if lhs.isAppOfArity ``EmptyCollection.emptyCollection 2 then
      goal.assign (mkAppN (.const ``Set.empty_subset [u]) #[α, rhs])
      replaceMainGoal []
      return true
    let mut edges : Array (Expr × Expr × Expr) := #[]
    for decl in ← getLCtx do
      if decl.isImplementationDetail then continue
      if let some (_, a, b) := subsetParts? (← instantiateMVars decl.type).cleanupAnnotations then
        edges := edges.push (a, b, decl.toExpr)
    -- breadth-first, from `lhs`, remembering a proof of `lhs ⊆ X` for each reached `X`
    let mut queue : Array (Expr × Option Expr) := #[(lhs, none)]
    let mut i := 0
    while h : i < queue.size do
      let (x, px) := queue[i]
      i := i + 1
      for (a, b, hab) in edges do
        unless a == x || (← withReducible (isDefEq a x)) do continue
        if queue.any (·.1 == b) then continue
        let pb := match px with
          | none => hab
          | some p => mkAppN (.const ``Set.Subset.trans [u]) #[α, lhs, x, b, p, hab]
        if b == rhs || (← withReducible (isDefEq b rhs)) then
          goal.assign pb
          replaceMainGoal []
          return true
        queue := queue.push (b, some pb)
    return false

/-- Close a leaf `footprint v ⊆ Alloc s'`: first through one of the extra lemmas (which are
directed: they reduce the footprint of a part of an input to the footprint of the input), and
otherwise by chaining hypotheses with `Set.Subset.trans`. The extra lemmas are tried *before*
the search, and never inside it: an unprovable subgoal such as `Alloc s ⊆ Alloc s` makes the
depth-first search exponential. -/
partial def spatialLeaf (extra : Array Term) : TacticM Unit := do
  if ← chainLeaf then return
  -- a pair reads what its components read (only for a literal pair: unifying with anything else
  -- would unfold it)
  let isPair ← (← getMainGoal).withContext do
    let some (_, lhs, _) := subsetParts? (← instantiateMVars (← (← getMainGoal).getType)).cleanupAnnotations | return false
    return lhs.isAppOfArity ``Backend.footprintT 4 && lhs.appArg!.isAppOfArity ``Prod.mk 4
  if isPair then
    let saved ← saveState
    try
      evalTactic (← `(tactic| apply Backend.footprintT_pair_subset_of))
      let goals ← getGoals
      for g in goals do
        setGoals [g]
        spatialLeaf extra
      return
    catch _ =>
      saved.restore
  for l in extra do
    let saved ← saveState
    try
      evalTactic (← `(tactic| (apply $l; solve_by_elim (maxDepth := 12) [Set.Subset.trans])))
      return
    catch _ =>
      saved.restore
  evalTactic (← `(tactic| solve_by_elim (maxDepth := 12) [Set.Subset.trans]))

/-- Split the goal along syntactic `∧` and `→` (no unfolding), then close the leaves. -/
partial def spatialSplit (extra : Array Term) : TacticM Unit := do
  let goals ← getUnsolvedGoals
  for goal in goals do
    setGoals [goal]
    let ty := (← instantiateMVars (← goal.getType)).cleanupAnnotations
    if ty.isAppOfArity ``And 2 then
      evalTactic (← `(tactic| constructor))
      spatialSplit extra
    else if ty.isForall then
      evalTactic (← `(tactic| (intro _; try casesm* _ ∧ _)))
      spatialSplit extra
    else if ty.isConstOf ``True then
      evalTactic (← `(tactic| trivial))
    else
      spatialLeaf extra
  setGoals []

/--
Discharge a `Spatial` obligation: destructure the input, normalize the operations (which
unfolds `LocalHold` into the tree of the calls' `pre`/`post`), and split and close the tree.
`spatial [l₁, l₂]` also uses the lemmas `lᵢ` to close leaves: facts of the form
`footprintT v ⊆ S → footprint (part of v) ⊆ S`, for inputs that are not tuples.
-/
syntax "spatial" (" [" term,* "]")? : tactic
elab_rules : tactic
  | `(tactic| spatial $[[$extra,*]]?) => do
    let extra := (extra.map (·.getElems)).getD #[]
    evalTactic (← `(tactic| intro input s h_in))
    destructProds
    evalTactic (← `(tactic| (
      simp only [circuit_norm, Set.union_subset_iff, Set.empty_subset, and_imp] at h_in ⊢
      try casesm* _ ∧ _)))
    spatialSplit extra

end

end Clean2
