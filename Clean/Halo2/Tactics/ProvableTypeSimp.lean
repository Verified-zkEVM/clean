import Lean.Elab.Tactic
import Clean.Halo2.StructEvalSimprocs
import Clean.Halo2.WitnessIR
import Clean.Utils.Tactics.ProvableTacticUtils
import Clean.Utils.Tactics.ProvableStructNaming

/-!
# `provable_type_simp`

The halo2 counterpart of main Clean's `provable_struct_simp` (PR #424): the single tactic
that normalizes provable-type values in a goal state, along semantic component boundaries.
It alternates two passes to a fixpoint:

1. **Destructure**: `cases` (with field-based names) on variables that participate in a
   provable-type-specific fact — variables under a folded `eval`, bases of field
   projections, and variables equated with a constructor literal. This exposes constructor
   literals for the eval simprocs while leaving unrelated values folded.
2. **Simp**: one `simp only` pass with the halo2 struct-eval set — the `↓ high`
   `ProvableStruct` bridges (component-preserving), the flat `ProvableType` bridges
   (fallback for leaf types like `Point`), the scalar-cell lemmas, and the three struct-eval
   simprocs (literal decomposition, projection lift, constructor-equality split).

Unlike `provable_struct_simp`, the gate is `ProvableType`, not `ProvableStruct`: a
`ProvableStruct` value decomposes along its component boundaries (higher priority via the
`↓ high` bridges — e.g. `{x:U32,y:U32}` splits into two `U32`s, kept whole), while a plain
`ProvableType` value (e.g. `Point`) still decomposes componentwise via the literal simproc.
Every simp-set member is also a `circuit_norm` member, so this tactic and later
`circuit_norm` passes agree on the normal form by construction.
-/

open Lean Elab Tactic Meta
open ProvableStructNaming

namespace Halo2.ProvableTypeSimp

/-- The struct-eval simp set (all members are also `circuit_norm`). -/
def structEvalSimpLemmas : Array Name := #[
  -- `ProvableStruct` bridges: component-preserving, applied first (`↓ high`). Plain
  -- `ProvableType`s are NOT bridged to `ProvableType.eval` — `Eval.eval` stays the normal
  -- form; the literal simproc below decomposes plain-type *literals* on the `Eval.eval` head.
  ``Halo2.ProvableStruct.eval_var_eq_eval, ``Halo2.ProvableStruct.eval_var_eq_eval_prover,
  ``Halo2.ProvableStruct.eval_cells_eq_eval, ``Halo2.ProvableStruct.eval_cells_eq_eval_prover,
  -- scalar single-cell evaluation, down to the typed-read normal form (matches
  -- `circuit_norm`, so the assigned-cell path agrees with the query path in the
  -- constraints): named cells (`Cell.of`) project componentwise, typed reads land on the
  -- `Environment.advice`-family accessors, witness reads unfold to assigned-cell evals
  ``Halo2.ProvableType.eval_field, ``Halo2.ProvableType.eval_field_prover,
  ``Halo2.AssignedCell.eval,
  ``Halo2.AssignedCell.of_cell, ``Halo2.Cell.of_regionIndex, ``Halo2.Cell.of_rowOffset,
  ``Halo2.Cell.of_column,
  ``Halo2.Environment.get_advice, ``Halo2.Environment.get_fixed, ``Halo2.Environment.get_inst,
  ``Halo2.WitgenEnv.readVar_halo2,
  -- the (verifier-side) struct-eval simprocs
  ``Halo2.StructEval.structEvalLiteralStructProc, ``Halo2.StructEval.structEvalLiteralTypeProc,
  ``Halo2.StructEval.structEvalLiteralEvalProc,
  ``Halo2.StructEval.evalProjectionLiftStructProc, ``Halo2.StructEval.evalProjectionLiftTypeProc,
  ``Halo2.StructEval.evalProjectionLiftEvalProc, ``Halo2.StructEval.structEqSplit,
  -- witgen (prover-side) evaluation: the shared simprocs decompose `Witgen.eval` of a
  -- struct/point literal and lift `FExprOver.eval` of a projection (completeness proofs)
  ``Witgen.evalStructLiteral, ``Witgen.evalProjection
]

/-- Whether a variable should be destructured: its type is a `ProvableType` (behind
`Var`/`Value` synonyms, hence `.instances` whnf). -/
private def isDestructurableVar (fvarId : FVarId) : MetaM Bool := do
  if (← fvarId.findDecl?).isNone then return false
  let type ← instantiateMVars (← inferType (.fvar fvarId))
  Halo2.StructEval.isProvableTypeLike type

/-- Evaluation heads whose equations/arguments drive destructuring (verifier + witgen). -/
private def evalHeads : Array Name :=
  #[``Eval.eval, ``Halo2.ProvableStruct.eval, ``Halo2.ProvableType.eval,
    ``Witgen.eval, ``Witgen.FExprOver.eval]

private def isEvalApp (e : Expr) : Bool :=
  if let .const name _ := e.getAppFn then evalHeads.contains name else false

/-- Collect the bases of structure projections in `e`. -/
private partial def projectionBaseVars (e : Expr) : MetaM (Array FVarId) := do
  let (_, vars) ← (go e).run #[]
  return vars
where
  go (e : Expr) : StateT (Array FVarId) MetaM Unit := do
    match e with
    | .proj _ _ base =>
      if let .fvar fvarId := base then modify (·.push fvarId) else go base
    | .app .. =>
      let f := e.getAppFn
      let args := e.getAppArgs
      if let .const name _ := f then
        if let some pinfo ← getProjectionFnInfo? name then
          if h : pinfo.numParams < args.size then
            if let .fvar fvarId := args[pinfo.numParams] then
              modify (·.push fvarId)
      go f
      for arg in args do go arg
    | .lam _ t b _ | .forallE _ t b _ => go t; go b
    | .letE _ t v b _ => go t; go v; go b
    | .mdata _ b => go b
    | _ => pure ()

/-- Variables in an equality that drive destructuring: a variable equated with a constructor
literal, and for an equation between a folded `eval` and a literal/variable, the eval
argument and the other side. `eval = eval` equations between opaque values are left alone
(row-level facts, used whole). -/
private def equationVars (lhs rhs : Expr) : MetaM (Array FVarId) := do
  let mut out : Array FVarId := #[]
  for (side, other) in #[(lhs.consumeMData, rhs.consumeMData), (rhs.consumeMData, lhs.consumeMData)] do
    if ← isMkConstructor side then
      if let .fvar fvarId := other then out := out.push fvarId
    if isEvalApp side && !isEvalApp other then
      if other.isFVar || (← isMkConstructor other) then
        if let some (.fvar argId) := side.getAppArgs.back? then out := out.push argId
        if let .fvar otherId := other then out := out.push otherId
  return out

/-- Collect all vars to destructure, from the goal and all hypotheses. -/
private def collectVarsToDestructure : TacticM (Array FVarId) :=
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
        if ← isDestructurableVar fvarId then result := result.push fvarId
    return result

/-- Destructure the collected vars via `cases`, field-naming (`input` → `input_x, input_y`).
Vars invalidated by an earlier `cases` are skipped and picked up next round. -/
private def destructurePass : TacticM Bool := do
  let toDestructure ← collectVarsToDestructure
  let mut progress := false
  for fvarId in toDestructure do
    try
      let goal ← getMainGoal
      let altNames ← goal.withContext <| generateStructFieldNames fvarId
      let casesResult ← goal.cases fvarId #[altNames]
      let [subgoal] := casesResult.toList | continue
      replaceMainGoal [subgoal.mvarId]
      progress := true
    catch _ => continue
  return progress

/-- One `simp only` pass with the halo2 struct-eval set, over goal and hypotheses. -/
private def simpPass : TacticM Bool := do
  let lemmas ← structEvalSimpLemmas.mapM fun name =>
    `(Lean.Parser.Tactic.simpLemma| $(mkIdent name):ident)
  try
    evalTactic (← `(tactic| simp +instances only [$[$lemmas],*] at *))
    return true
  catch _ => return false

/--
Normalize all provable-type values in the goal state: destructure participating variables,
decompose evaluation of the resulting literals along component boundaries, lift evaluation
of projections to the row level, and split constructor equalities field-wise. Opaque values
not involved in any such fact stay folded. Runs to a fixpoint; never fails.
-/
elab "provable_type_simp" : tactic => do
  for _ in [0:100] do
    if (← getGoals).isEmpty then return
    let destructured ← destructurePass
    let simplified ← simpPass
    unless destructured || simplified do return

end Halo2.ProvableTypeSimp
