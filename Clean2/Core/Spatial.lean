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

/-- Close a leaf `footprint v ⊆ Alloc s'`: first through one of the extra lemmas (which are
directed: they reduce the footprint of a part of an input to the footprint of the input), and
otherwise by chaining hypotheses with `Set.Subset.trans`. The extra lemmas are tried *before*
the search, and never inside it: an unprovable subgoal such as `Alloc s ⊆ Alloc s` makes the
depth-first search exponential. -/
def spatialLeaf (extra : Array Term) : TacticM Unit := do
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
    let ty ← instantiateMVars (← goal.getType)
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
