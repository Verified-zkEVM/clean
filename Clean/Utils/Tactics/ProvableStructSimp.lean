import Lean.Elab.Tactic
import Clean.Circuit.StructEvalSimprocs
import Clean.Utils.Tactics.ProvableTacticUtils
import Clean.Utils.Tactics.ProvableStructNaming

/-!
# `provable_struct_simp`

The single tactic that normalizes provable-struct values in a goal state. It alternates
two passes until neither makes progress:

1. **Destructure**: apply `cases` (with field-based names) to struct variables that
   participate in struct-specific facts — variables under a folded `eval`, bases of field
   projections, and variables equated with a constructor literal. This exposes constructor
   literals for the eval simprocs while leaving unrelated record variables opaque.
2. **Simp**: one `simp only` pass with the struct-eval simp set below — the eval bridges,
   the struct-eval simprocs (literal decomposition, projection lift, constructor-equality
   split), and the scalar/vector eval lemmas.

Every member of the simp set is also a `circuit_norm` member, so this tactic and any later
`circuit_norm` pass agree on the normal form: whatever `provable_struct_simp` leaves in
place, `circuit_norm` will not rewrite into a different struct spelling (and vice versa).

The normal form is component-preserving and row-level: constructor literals under `eval`
decompose field-wise, evaluation of a projection becomes a projection of the row-level
evaluation, opaque structs stay folded atoms, and constructor equalities split into
field-wise conjunctions.
-/

open Lean Elab Tactic Meta
open ProvableStructNaming

namespace ProvableStructSimp

/--
The struct-eval simp set. Except for the getElem lemmas (see below), all members are
also tagged `circuit_norm`; keep the two in sync when adding lemmas, so
`provable_struct_simp` and `circuit_norm` passes produce the same struct normal form.
-/
def structEvalSimpLemmas : Array Name := #[
  -- bridges from the `Eval`/`Var` class spellings to `ProvableStruct.eval`
  ``ProvableStruct.eval_eq_eval, ``ProvableStruct.eval_eq_eval_prover,
  ``ProvableStruct.eval_var_eq_eval, ``ProvableStruct.eval_var_eq_eval_prover,
  ``ProvableStruct.eval_field_var_eq_eval, ``ProvableStruct.eval_field_var_eq_eval_prover,
  -- struct-eval simprocs: literal decomposition, projection lift, constructor-eq split
  ``ProvableStruct.structEvalLiteralProc, ``ProvableStruct.structEvalProjectionProc,
  ``ProvableStruct.structEvalProjectionEvalProc,
  ``ProvableStruct.structEvalProjectionExpr, ``ProvableStruct.structEqSplit,
  ``ProvableStruct.components,
  -- scalar and vector element evaluation. The getElem lemmas are deliberately *not*
  -- in `circuit_norm`: there they loop against the element-map spelling
  -- (`eval_var_fields` + `Vector.map_mk`); here the map spelling is absent, so vector
  -- indexing converges to the row level, `Expression.eval env (v[i]) ~~> (eval env v)[i]`
  ``ProvableType.eval_field, ``ProvableType.getElem_eval_fields,
  ``ProvableType.getElem_eval_fields_prover, ``getElem_eval_vector,
  -- `CircuitType` wrappers and coercions
  ``CircuitType.eval_var_prover_to_verifier,
  ``CircuitType.eval_var_field, ``CircuitType.eval_var_field_prover,
  ``CircuitType.eval_expr, ``CircuitType.eval_expr_prover,
  ``CircuitType.value_of_provableType, ``CircuitType.proverValue_of_provableType,
  -- derived `CircuitType` evaluation
  ``DerivedCircuitType.eval_verifier, ``DerivedCircuitType.eval_prover,
  ``CircuitType.evalVerifier, ``CircuitType.evalProver
]

private def synthesizes (cls : Name) (arg : Expr) : MetaM Bool := do
  try
    let instType ← mkAppM cls #[arg]
    return (← trySynthInstance instType) matches .some _
  catch _ => return false

/--
Whether a variable should be destructured by `cases`: its type is a provable struct
(the `TypeMap` has a `ProvableStruct` instance, possibly behind `Var`/`Value` synonyms)
or the value view of a `DerivedCircuitType`. Ordinary records stay opaque.
-/
private def isDestructurableStructVar (fvarId : FVarId) : MetaM Bool := do
  if (← fvarId.findDecl?).isNone then return false
  let type ← instantiateMVars (← inferType (.fvar fvarId))
  -- `Value M F` / `ProverValue M F` views of derived circuit types
  if type.getAppFn.isConstOf ``CircuitType.Value ||
      type.getAppFn.isConstOf ``CircuitType.ProverValue then
    if let some m := type.getAppArgs[0]? then
      if ← synthesizes ``DerivedCircuitType m then return true
  -- `S ps F` (possibly behind class-projection synonyms, hence `.instances` whnf):
  -- check `ProvableStruct (S ps)`
  let type' ← withTransparency .instances <| whnf type
  let .app typeCtor _ := type' | return false
  synthesizes ``ProvableStruct typeCtor

/-- Evaluation heads whose equations drive destructuring. -/
private def evalHeads : Array Name :=
  #[``ProvableStruct.eval, ``Eval.eval, ``ProvableType.eval]

private def isEvalApp (e : Expr) : Bool :=
  if let .const name _ := e.getAppFn then evalHeads.contains name else false

/--
Collect the bases of structure projections in `e` (both `.proj` nodes and
projection-function applications).
-/
private partial def projectionBaseVars (e : Expr) : MetaM (Array FVarId) := do
  let (_, vars) ← (go e).run #[]
  return vars
where
  go (e : Expr) : StateT (Array FVarId) MetaM Unit := do
    match e with
    | .proj _ _ base =>
      if let .fvar fvarId := base then
        modify (·.push fvarId)
      else
        go base
    | .app .. =>
      let f := e.getAppFn
      let args := e.getAppArgs
      if let .const name _ := f then
        if let some pinfo ← getProjectionFnInfo? name then
          if h : pinfo.numParams < args.size then
            if let .fvar fvarId := args[pinfo.numParams] then
              modify (·.push fvarId)
      go f
      for arg in args do
        go arg
    | .lam _ t b _ | .forallE _ t b _ => go t; go b
    | .letE _ t v b _ => go t; go v; go b
    | .mdata _ b => go b
    | _ => pure ()

/--
Variables in an equality that drive destructuring:

* a variable equated with a constructor literal, and
* for an equation between a folded `eval` and a constructor literal or plain variable:
  the eval argument (so the literal simproc can decompose the evaluation) and the
  variable on the other side (so the resulting constructor equality splits into
  variable-free field equations).

`eval = eval` equations between opaque structs are left alone: they are row-level facts,
meant to be used whole.
-/
private def equationVars (lhs rhs : Expr) : MetaM (Array FVarId) := do
  let mut out : Array FVarId := #[]
  for (side, other) in #[(lhs.consumeMData, rhs.consumeMData), (rhs.consumeMData, lhs.consumeMData)] do
    if ← isMkConstructor side then
      if let .fvar fvarId := other then
        out := out.push fvarId
    if isEvalApp side && !isEvalApp other then
      if other.isFVar || (← isMkConstructor other) then
        if let some (.fvar argId) := side.getAppArgs.back? then
          out := out.push argId
        if let .fvar otherId := other then
          out := out.push otherId
  return out

/--
Collect all struct variables to destructure, from the goal and all hypotheses:
projection bases, variables equated with constructor literals, and eval arguments in
equations (possibly inside conjunctions).
-/
private def collectStructVarsToDestructure : TacticM (Array FVarId) :=
  withMainContext do
    let mut candidates : Array FVarId := #[]
    let scan := fun (e : Expr) => do
      let mut acc ← projectionBaseVars e
      for (_, lhs, rhs) in ← extractEqualities e do
        acc := acc ++ (← equationVars lhs rhs)
      return acc
    for decl in (← getLCtx) do
      if decl.isImplementationDetail then continue
      candidates := candidates ++ (← scan (← instantiateMVars decl.type))
    candidates := candidates ++ (← scan (← getMainTarget))
    let mut result : Array FVarId := #[]
    for fvarId in candidates do
      unless result.contains fvarId do
        if ← isDestructurableStructVar fvarId then
          result := result.push fvarId
    return result

/--
Destructure the collected struct variables via `cases`, naming the fields after the
variable (`input` with fields `x, y` becomes `input_x, input_y`). Returns whether any
variable was destructured. Variables invalidated by an earlier `cases` (their `FVarId`
changes when a dependent hypothesis is reverted) are skipped and picked up in the next
round.
-/
private def destructurePass : TacticM Bool := do
  let toDestructure ← collectStructVarsToDestructure
  let mut progress := false
  for fvarId in toDestructure do
    try
      let goal ← getMainGoal
      let altNames ← goal.withContext <| generateStructFieldNames fvarId
      let casesResult ← goal.cases fvarId #[altNames]
      let [subgoal] := casesResult.toList | continue
      replaceMainGoal [subgoal.mvarId]
      progress := true
    catch _ =>
      continue
  return progress

/-- One `simp only` pass with the struct-eval simp set, over the goal and all
hypotheses. Returns whether simp made progress. -/
private def simpPass : TacticM Bool := do
  let lemmas ← structEvalSimpLemmas.mapM fun name =>
    `(Lean.Parser.Tactic.simpLemma| $(mkIdent name):ident)
  try
    evalTactic (← `(tactic| simp +instances only [$[$lemmas],*] at *))
    return true
  catch _ =>
    return false

/--
Normalize all provable-struct values in the goal state: destructure struct variables that
appear under a folded `eval`, in field projections, or opposite constructor literals in
equalities; decompose evaluation of the resulting literals field-wise; lift evaluation of
projections to the row level; and split constructor equalities into field-wise
conjunctions. Opaque struct variables not involved in any such fact stay folded.

Runs to a fixpoint and never fails; it just stops when no pass makes progress.
-/
elab "provable_struct_simp" : tactic => do
  -- fixpoint: `cases` strictly consumes struct variables (new ones only appear for
  -- nested structs, of smaller depth) and simp fails once nothing rewrites; the counter
  -- is a safety net only
  for _ in [0:100] do
    if (← getGoals).isEmpty then return
    let destructured ← destructurePass
    let simplified ← simpPass
    unless destructured || simplified do return

end ProvableStructSimp
