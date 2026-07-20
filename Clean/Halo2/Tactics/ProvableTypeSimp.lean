import Lean.Elab.Tactic
import Clean.Halo2.StructEvalSimprocs
import Clean.Halo2.WitnessIR
import Clean.Utils.Tactics.ProvableTacticUtils
import Clean.Utils.Tactics.ProvableStructNaming

/-!
# `provable_type_simp`

The halo2 counterpart of main Clean's `provable_struct_simp` (PR #424): normalizes provable-type
values in a goal state along semantic component boundaries. **Status: under construction** (part of
the halo2 tactic layer still being exercised across the corpus). It alternates passes to a fixpoint:

1. **Destructure**: `cases` (with field-based names) on variables that participate in a
   provable-type-specific fact — variables under a folded `eval`, bases of field
   projections, and variables equated with a constructor literal. This exposes constructor
   literals for the eval simprocs while leaving unrelated values folded. Naming: a var equated
   with a constructor literal, or the bundle's `output` binder, uses multi-parameter naming
   (`Output numBits F` destructures); other participants use single-parameter naming, which skips a
   multi-parameter type (so a whole multi-parameter *input* fed into a recursive body lemma — the
   Sinsemilla chains — stays folded).
2. **Simp**: one `simp only` pass with the halo2 struct-eval set — the `↓ high`
   `ProvableStruct` bridges (component-preserving), the flat `ProvableType` bridges
   (fallback for leaf types like `Point`), the scalar-cell lemmas, and the three struct-eval
   simprocs (literal decomposition, projection lift, constructor-equality split).
3. **Vector-equation forming**: after `structEqSplit` splits a provable-struct value equation into
   per-component equations, a **vector** component bottoms out at a whole-vector equation
   `Eval.eval env ⟨cells⟩ = output_zs`. Since the per-index fact is a hypothesis-forming step (not a
   rewrite simp can express), this pass replaces such a hypothesis with the individually-named
   component facts, the vector one as `∀ i (hi : i < n), <cell i> = output_zs[i]` (atom-left, its
   per-index LHS resolved through the lazy `getElem_eval_fields_cells` bridge).

Unlike `provable_struct_simp`, the gate is `ProvableType`, not `ProvableStruct`: a
`ProvableStruct` value decomposes along its component boundaries (higher priority via the
`↓ high` bridges — e.g. `{x:U32,y:U32}` splits into two `U32`s, kept whole), while a plain
`ProvableType` value (e.g. `Point`) still decomposes componentwise via the literal simproc.
Every simp-set member is also a `circuit_norm` member, so this tactic and later `circuit_norm`
passes share the same normal form.
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
  ``Halo2.ProvableType.eval_field', ``Halo2.ProvableType.eval_field_prover',
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
`Var`/`Value` synonyms, hence `.instances` whnf), or a view companion of a
`deriving CircuitType` mixed hint+provable record (marked `DecomposableStruct` by the
deriver). Mixed records follow the SAME flow as pure `ProvableStruct`s: both the var and
the value views destructure, the resulting record-literal evals decompose per-field
(each field's `Eval` instance resolves — hint fields via the named `Unconstrained*`
forwarders), and the constructor-vs-constructor equation splits componentwise. -/
private def isDestructurableVar (fvarId : FVarId) : MetaM Bool := do
  if (← fvarId.findDecl?).isNone then return false
  let type ← instantiateMVars (← inferType (.fvar fvarId))
  Halo2.StructEval.isProvableTypeLike type (allowDecomposable := true)

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

/-- Variables in an equality that drive destructuring, tagged by whether they are a variable
equated with a **constructor literal** (`⟨cells⟩ = var` — the OUTPUT-split pattern, `literal? =
true`) or come from a folded `eval`-vs-var/literal equation (`eval x = v` — the INPUT-read pattern,
`literal? = false`). `eval = eval` equations between opaque values are left alone (row-level facts,
used whole). The tag selects the naming scheme in `destructurePass`. -/
private def equationVars (lhs rhs : Expr) : MetaM (Array (FVarId × Bool)) := do
  let mut out : Array (FVarId × Bool) := #[]
  for (side, other) in #[(lhs.consumeMData, rhs.consumeMData), (rhs.consumeMData, lhs.consumeMData)] do
    if ← isMkConstructor side then
      if let .fvar fvarId := other then out := out.push (fvarId, true)
    if isEvalApp side && !isEvalApp other then
      if other.isFVar || (← isMkConstructor other) then
        if let some (.fvar argId) := side.getAppArgs.back? then out := out.push (argId, false)
        if let .fvar otherId := other then out := out.push (otherId, false)
  return out

/-- Collect all vars to destructure, from the goal and all hypotheses, tagged `true` when equated
with a constructor literal (the output-split pattern; eligible for multi-parameter naming). -/
private def collectVarsToDestructure : TacticM (Array (FVarId × Bool)) :=
  withMainContext do
    let mut candidates : Array (FVarId × Bool) := #[]
    let scan := fun (e : Expr) => do
      let mut acc : Array (FVarId × Bool) := (← projectionBaseVars e).map (·, false)
      for (_, lhs, rhs) in ← extractEqualities e do
        acc := acc ++ (← equationVars lhs rhs)
      return acc
    for decl in (← getLCtx) do
      if decl.isImplementationDetail then continue
      candidates := candidates ++ (← scan (← instantiateMVars decl.type))
    candidates := candidates ++ (← scan (← getMainTarget))
    -- dedup by fvar, keeping `multi? = true` if it appears anywhere. A var is multi-param-eligible
    -- when it is equated with a constructor literal OR it is the bundle's `output` binder (the
    -- house name `circuit_proof_start` introduces): the gadget's own output is the one struct whose
    -- components the `Spec` always speaks about, so a multi-parameter `Output numBits F` must
    -- destructure — whereas a multi-parameter *input* fed whole into a recursive body lemma
    -- (Sinsemilla chains) must stay folded, so it stays on the single-parameter (skip) path.
    let mut result : Array (FVarId × Bool) := #[]
    for (fvarId, lit) in candidates do
      let isOutput := (← fvarId.getDecl).userName == `output
      let multi := lit || isOutput
      if let some idx := result.findIdx? (·.1 == fvarId) then
        if multi then result := result.set! idx (fvarId, true)
      else if ← isDestructurableVar fvarId then
        result := result.push (fvarId, multi)
    return result

/-- Destructure the collected vars via `cases`, field-naming (`input` → `input_x, input_y`). Vars
invalidated by an earlier `cases` are skipped and picked up next round.

Naming scheme by tag: a var equated with a **constructor literal** (the output-split pattern) uses
the **multi-parameter** naming (`generateStructFieldNamesMulti`, reading the struct name off the
application head), so a provable type whose constructor carries parameters before the field type —
`Output numBits F` — destructures into its components. All other participants (projection bases,
`eval`-read inputs) use the **single-parameter** naming, which SKIPS a multi-parameter type: this
deliberately leaves a whole multi-parameter *input* (`Inputs numPieces F`, fed whole into a
recursive body lemma, as the Sinsemilla chains do) folded, matching the pre-existing behaviour. -/
private def destructurePass : TacticM Bool := do
  let toDestructure ← collectVarsToDestructure
  let mut progress := false
  for (fvarId, literal?) in toDestructure do
    try
      let goal ← getMainGoal
      let altNames ← goal.withContext <|
        if literal? then generateStructFieldNamesMulti fvarId
        else generateStructFieldNames fvarId
      let casesResult ← goal.cases fvarId #[altNames]
      let [subgoal] := casesResult.toList | continue
      replaceMainGoal [subgoal.mvarId]
      progress := true
    catch _ => continue
  return progress

/-- Whether `ty` reduces to `Vector _ _`. Reduces at `.instances` transparency so the halo2
`Value (fields n) F` spelling (a reducible `Value` over the `fields n` circuit-type instance)
unfolds to the underlying `Vector F n` — a `withReducible` whnf stops at `Value`. -/
private def isVectorType (ty : Expr) : MetaM Bool := do
  return (← withTransparency .instances <| whnf ty).getAppFn.isConstOf ``Vector

/-- Whether an equation `(lhs, rhs)` is a vector-eval-vs-variable equation
`Eval.eval env ⟨cells⟩ = v` (or reversed): one side a `fields n` vector value under an `Eval.eval`
head, the other a free variable. Returns `(evalSide, var)` when so. -/
private def asVectorEvalEq (lhs rhs : Expr) : MetaM (Option (Expr × Expr)) := do
  if (← isVectorType (← inferType lhs)) && rhs.consumeMData.isFVar
      && lhs.getAppFn.isConstOf ``Eval.eval then
    return some (lhs, rhs.consumeMData)
  if (← isVectorType (← inferType rhs)) && lhs.consumeMData.isFVar
      && rhs.getAppFn.isConstOf ``Eval.eval then
    return some (rhs, lhs.consumeMData)
  return none

/-- Collect the leaf equations `(lhs, rhs)` of an `And`-tree (a `structEqSplit` output), reading the
head *syntactically* (`getAppFnArgs`, no `whnf`) — the `And`/`Eq` structure `structEqSplit` produces
is not behind reducible defs, and avoiding `whnf` keeps this cheap on the deep composed hypotheses of
layouter-level proofs (whnf there blows the recursion depth). Returns `none` on a shape that is not a
pure conjunction-of-equations, so a non-split hypothesis short-circuits immediately. -/
private partial def conjunctionEqs (e : Expr) : Option (Array (Expr × Expr)) :=
  match e.getAppFnArgs with
  | (``And, #[a, b]) =>
    match conjunctionEqs a, conjunctionEqs b with
    | some ea, some eb => some (ea ++ eb)
    | _, _ => none
  | (``Eq, #[_, lhs, rhs]) => some #[(lhs, rhs)]
  | _ => none

/-- Destructuring pattern mirroring an ∧-tree's actual shape (the leaves arrive in
`conjunctionEqs` order, but the tree may be left-nested — a flat pattern only matches
right-nested chains). -/
private partial def conjPat (names : Array Name) (e : Expr) (i : ℕ) :
    TacticM (TSyntax `rcasesPat × ℕ) := do
  match e.getAppFnArgs with
  | (``And, #[a, b]) =>
    let (pa, i) ← conjPat names a i
    let (pb, i) ← conjPat names b i
    return (← `(rcasesPat| ⟨$pa, $pb⟩), i)
  | _ => return (← `(rcasesPat| $(mkIdent names[i]!):ident), i + 1)

/-- Replace a hypothesis whose type is (a conjunction of) per-component value equations — as
`structEqSplit` leaves a split provable-struct value equation — with individually-named component
facts, forming the per-index quantified fact for any **vector** component (`Eval.eval env ⟨cells⟩ =
output_zs`, the point at which `structEqSplit` bottoms out).

Each component fact keeps the **atom-left** orientation `<cell/eval> = <var>` (the universal
row-fact convention, so a later `simp only [h] at hc ⊢` rewrites cell atoms toward values). A
vector component becomes `∀ i (hi : i < n), <cell i, framework normal form> = output_zs[i]`, its
per-index LHS resolved through the LAZY `getElem_eval_fields_cells` bridge (projection-on-demand,
no whole-vector map). Fires only when at least one leaf is a vector-eval-vs-var equation, so scalar-
only splits (the common leaf case) are left as their conjunction. Fully state-restoring.

META-STYLE(follow-up): this function drives `obtain`/`have`/`simp`/`clear` via `evalTactic` on
constructed syntax. The preferred meta-level style is direct `MVarId` APIs (`MVarId.cases` for the
`obtain`, `MVarId.assert` + a built proof term for the `have`, `Simp.main`/`simpGoal` for the simp,
`MVarId.clear`). Converting this (and the sibling `evalTactic` sites in `destructurePass`/`simpPass`)
to the programmatic style is left for a follow-up pass. -/

private def formVectorEqFacts (fvarId : FVarId) : TacticM Bool := withMainContext do
  let decl ← fvarId.getDecl
  if decl.isImplementationDetail then return false
  let ty ← instantiateMVars decl.type
  -- cheap syntactic gate: a pure conjunction of equations, at least one a vector-eval-vs-var eq
  let some eqs := conjunctionEqs ty | return false
  unless eqs.size ≥ 1 do return false
  -- Fire only on the clean case: EVERY leaf is a value equation whose value side is a bare
  -- free variable (a scalar output component), with at least one being a vector-eval-vs-var
  -- equation. This is the shape a struct output of scalar + vector components produces (the
  -- `MulIncomplete.Output {xA, yA, zs}` family). A struct output with a *nested struct* or an
  -- *opaque-eval* component (`MulComplete.Output {acc : Point, zs}`, `HashPiece.Output` with
  -- `DoubleAndAddRow` rows) leaves a literal/opaque-sided leaf; those `h_output`s are consumed
  -- whole by their user halves (this pass is a clean no-op on them, so the split stays predictable).
  let mut hasVector := false
  let mut allOk := true
  for (lhs, rhs) in eqs do
    if (← asVectorEvalEq lhs rhs).isSome then hasVector := true
    else unless lhs.consumeMData.isFVar || rhs.consumeMData.isFVar do allOk := false
  unless allOk do return false
  unless hasVector do return false
  let hName := decl.userName
  -- final fact name `h_<field>`, after the value variable each leaf constrains (`output_xA` →
  -- `h_output_xA`); fall back to `<hName>_<i>` when neither side is a bare variable.
  let finalNames ← eqs.mapIdxM fun i (lhs, rhs) => do
    let v := if rhs.consumeMData.isFVar then rhs.consumeMData else lhs.consumeMData
    if let .fvar fv := v then
      return Name.mkSimple ("h_" ++ (← fv.getDecl).userName.eraseMacroScopes.toString)
    else
      return Name.mkSimple s!"{hName.toString}_{i}"
  -- temporary obtain names (never reused as a `have` binder name, so no shadowing hazard)
  let tmpNames := (Array.range eqs.size).map (fun i => Name.mkSimple s!"__veq_{i}")
  let s ← saveState
  try
    -- Single bare equation (a one-field struct output): do NOT `obtain` — `rcases h with x`
    -- on a top-level `Eq` SUBSTITUTES the variable side instead of renaming (so the temp
    -- name would never exist); the hypothesis already is its own single "leaf".
    let isSingleEq := ty.getAppFnArgs.1 == ``Eq
    let tmpIdents ←
      if isSingleEq then
        pure #[mkIdent hName]
      else do
        let (pat, _) ← conjPat tmpNames ty 0
        evalTactic (← `(tactic| obtain $pat := $(mkIdent hName):ident))
        pure (tmpNames.map mkIdent)
    for i in [0:eqs.size] do
      let (lhs, rhs) := eqs[i]!
      let tmpId := tmpIdents[i]!
      let finalId := mkIdent finalNames[i]!
      match ← asVectorEvalEq lhs rhs with
      | some (evalSide, varSide) =>
        let evalStx ← Lean.Elab.Term.exprToSyntax evalSide
        let varStx ← Lean.Elab.Term.exprToSyntax varSide
        -- `__veq_i : eval env ⟨cells⟩ = v` (up to orientation) → `∀ i hi, (eval ⟨cells⟩)[i] = v[i]`
        evalTactic (← `(tactic|
          have $finalId:ident : ∀ (i : ℕ) (hi : i < _), ($evalStx)[i]'hi = ($varStx)[i]'hi := by
            intro i hi
            first
            | exact congrArg (fun w => w[i]'hi) $tmpId:ident
            | exact congrArg (fun w => w[i]'hi) ($tmpId:ident).symm))
        -- reduce the per-index LHS `getElem` to the single cell read (lazy bridge). `try`-guarded:
        -- if it does not fire the fact is still valid in `(eval …)[i]` form, not a reason to abort.
        try evalTactic (← `(tactic| simp +instances only [circuit_norm] at $finalId:ident))
          catch _ => pure ()
        try evalTactic (← `(tactic| clear $tmpId:ident)) catch _ => pure ()
      | none =>
        -- scalar component: keep the atom-left equation, just rename to `h_<field>`
        evalTactic (← `(tactic| have $finalId:ident := $tmpId:ident))
        try evalTactic (← `(tactic| clear $tmpId:ident)) catch _ => pure ()
    return true
  catch _ =>
    restoreState s
    return false

/-- Form the per-index atom-left facts for every vector-component split currently in context. -/
private def vectorEqPass : TacticM Bool := do
  if (← getGoals).isEmpty then return false
  withMainContext do
    let mut progress := false
    for decl in (← getLCtx) do
      if decl.isImplementationDetail then continue
      if ← formVectorEqFacts decl.fvarId then progress := true
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
  -- Phase 1: destructure + struct-eval simp, to a fixpoint. This does the participation-gated
  -- `cases`, the literal decomposition, projection lift, and `structEqSplit`.
  for _ in [0:100] do
    if (← getGoals).isEmpty then return
    let destructured ← destructurePass
    let simplified ← simpPass
    unless destructured || simplified do break
  -- Phase 2: after the simp fixpoint, a vector *component* of a split provable-struct value equation
  -- is left as a whole-vector eval-vs-var equation. Form its per-index atom-left fact (the one
  -- hypothesis-forming step simp cannot express). Run ONCE, after the simp fixpoint, so a later
  -- `simpPass` cannot revert the formed quantified fact.
  if (← getGoals).isEmpty then return
  discard <| vectorEqPass

end Halo2.ProvableTypeSimp
