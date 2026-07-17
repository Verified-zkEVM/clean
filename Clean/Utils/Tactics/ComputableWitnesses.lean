import Clean.Circuit.Explicit

/-!
# `computable_witnesses`

Automation for the common `FormalCircuitBase.ComputableWitnesses` proof shape.

The tactic deliberately uses controlled simp sets and performs at most two rounds of
unfolding circuit-valued wrapper definitions. Circuits needing more abstraction layers
should express those layers as subcircuits instead.
-/

open Lean Meta Simp Elab Tactic

/-- Unfold circuit-valued wrapper definitions while respecting explicit-circuit boundaries. -/
elab "unfold_formal_circuit_consts" : tactic => do
  withMainContext do
    let noUnfold ← labelled `explicit_circuit_no_unfold
    let unfoldTypes ← labelled `explicit_circuit_unfold_type
    let names ← collectUnfoldableCircuitDecls (← getMainTarget) #[]
      (some noUnfold) (some unfoldTypes)
    for name in names do
      try
        evalTactic (← `(tactic| unfold $(mkIdent name)))
      catch _ =>
        pure ()

namespace ComputableWitnesses

/--
Split equalities between applications of the same structure constructor using the
constructor's generated `injEq` theorem. This is supplied only to the controlled simp
passes in `computable_witnesses`; it does not affect the global simp set.
-/
def structEqSplitProc : Simproc := fun e => do
  unless e.isAppOfArity ``Eq 3 do return .continue
  let args := e.getAppArgs
  let lhs := args[1]!.consumeMData
  let rhs := args[2]!.consumeMData
  let .const ctorName _ := lhs.getAppFn | return .continue
  unless rhs.getAppFn.isConstOf ctorName do return .continue
  let some (.ctorInfo info) := (← getEnv).find? ctorName | return .continue
  unless info.numFields > 0 do return .continue
  unless lhs.getAppNumArgs == info.numParams + info.numFields &&
      rhs.getAppNumArgs == info.numParams + info.numFields do return .continue
  let injEqName := ctorName ++ `injEq
  unless (← getEnv).contains injEqName do return .continue
  try
    let params := lhs.getAppArgs[:info.numParams].toArray.map some
    let lhsFields := lhs.getAppArgs[info.numParams:].toArray.map some
    let rhsFields := rhs.getAppArgs[info.numParams:].toArray.map some
    let proof ← withTransparency .default <|
      mkAppOptM injEqName (params ++ lhsFields ++ rhsFields)
    let some (_, _, conjunction) := (← inferType proof).eq? | return .continue
    return .visit { expr := conjunction, proof? := some proof }
  catch _ =>
    return .continue

simproc structEqSplit (_ = _) := structEqSplitProc

private def runComputableWitnesses
    (extraTerms : Array (TSyntax `term)) (unfoldCircuitConsts : Bool) : TacticM Unit := do
  let lemmasArray ← extraTerms.mapM fun term =>
    `(Lean.Parser.Tactic.simpLemma| $term:term)
  let simpPass : TacticM Unit := do
    unless (← getGoals).isEmpty do
      try
        evalTactic (← `(tactic| simp only [circuit_norm, computable_witnesses_norm,
          ComputableWitnesses.structEqSplit, $lemmasArray,*]))
      catch _ =>
        pure ()
  simpPass
  if !unfoldCircuitConsts then
    unless (← getGoals).isEmpty do
      try
        evalTactic (← `(tactic| unfold $(mkIdent `main):ident))
      catch _ =>
        pure ()
      simpPass
  else
    for _ in [0:2] do
      unless (← getGoals).isEmpty do
        evalTactic (← `(tactic| unfold_formal_circuit_consts))
        simpPass
  unless (← getGoals).isEmpty do
    evalTactic (← `(tactic| intros))
  unless (← getGoals).isEmpty do
    withMainContext do
      let target ← whnf (← getMainTarget)
      if target.isAppOfArity ``And 2 then
        evalTacticSeq (← `(tacticSeq|
          apply And.intro
          · intros
            (try and_intros) <;> grind
          · grind))
      else
        evalTactic (← `(tactic| grind))

/--
Prove the standard computable-witness obligation using a controlled normalization pass,
two bounded rounds of circuit-wrapper unfolding, structural splitting of the operations/output
conjunction, and `grind`.

Extra simp lemmas may be supplied as `computable_witnesses [lemma₁, lemma₂]`.
-/
syntax "computable_witnesses" ("[" term,* "]")? : tactic

/--
Experimental variant of `computable_witnesses` that does not unfold circuit-valued constants.
It unfolds a `main` declaration in the current scope, while child subcircuit constants remain opaque.
-/
syntax "computable_witnesses'" ("[" term,* "]")? : tactic

elab_rules : tactic
  | `(tactic| computable_witnesses $[[$terms:term,*]]?) =>
      runComputableWitnesses (terms.map (fun terms => terms.getElems) |>.getD #[]) true
  | `(tactic| computable_witnesses' $[[$terms:term,*]]?) =>
      runComputableWitnesses (terms.map (fun terms => terms.getElems) |>.getD #[]) false

end ComputableWitnesses
