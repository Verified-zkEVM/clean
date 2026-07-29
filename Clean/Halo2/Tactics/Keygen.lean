import Clean.Halo2.Loops
import Clean.Halo2.KeygenAttr
import Batteries.Lean.TagAttribute
import Lean.Elab.Tactic

/-!
# Configure/synthesis registration automation

`keygen_registration` proves that every gate and lookup enabled by a circuit's synthesis
stream was either supplied by its caller or appended by its configure program.  The
normalization set is deliberately separate from `circuit_norm`: registration proofs
open configure deltas and operation streams, while ordinary circuit proofs preserve
formal-circuit call boundaries. Parent circuits discharge those folded calls with the
generic `call_keygenRegistered` lemmas.
-/

namespace Halo2

open Lean

initialize keygenCallAttr : TagAttribute ←
  registerTagAttribute `keygen_call
    "A folded circuit-call certificate used by keygen registration."

initialize keygenCallExpressionAttr : TagAttribute ←
  registerTagAttribute `keygen_call_expression
    "An opaque circuit-call expression recognized by keygen registration."

initialize keygenCallBundleAttr : TagAttribute ←
  registerTagAttribute `keygen_call_bundle
    "A formal-circuit bundle type carried by a keygen call expression."

initialize keygenConfiguredAttr : TagAttribute ←
  registerTagAttribute `keygen_configured
    "A constructor proving that a circuit config came from its configure program."

initialize keygenHelperAttr : TagAttribute ←
  registerTagAttribute `keygen_helper
    "A registration certificate for a raw circuit helper."

initialize keygenBundleProjectionAttr : TagAttribute ←
  registerTagAttribute `keygen_bundle_projection
    "A formal-circuit projection through which keygen registration finds a concrete bundle."

initialize keygenMetadataProjectionAttr : TagAttribute ←
  registerTagAttribute `keygen_metadata_projection
    "A keygen metadata projection that may be unfolded without exposing synthesis operations."

attribute [keygen_norm]
  Configure.delta_bind Configure.delta_pure
  Configure.delta_selector Configure.delta_complexSelector
  Configure.delta_createGate
  Configure.output_bind Configure.output_pure
  Configure.output_adviceColumn Configure.output_fixedColumn
  Configure.output_instanceColumn Configure.output_selector
  Configure.output_complexSelector Configure.output_enableEquality
  Configure.output_enableConstant Configure.output_createGate
  Configure.output_lookup
  ConfigureDelta.gates_append ConfigureDelta.lookups_append
  ConfigureDelta.gates_queriedCells ConfigureDelta.lookups_queriedCells
  RegionOperation.KeygenRegistered Operation.KeygenRegistered
  Operations.KeygenRegistered.nil Operations.KeygenRegistered.append
  Operations.KeygenRegistered.region_cons
  Operations.KeygenRegistered.constrainInstance_cons
  Operations.KeygenRegistered.loadTable_cons
  List.forall_append List.forall_cons
  List.mem_append List.mem_cons List.mem_singleton
  List.nil_append List.append_nil List.append_assoc
  and_self and_true true_and ite_self

attribute [keygen_spine]
  RegionCircuit.operations_bind RegionCircuit.operations_pure
  Circuit.operations_bind Circuit.operations_pure
  RegionOperation.KeygenRegistered Operation.KeygenRegistered
  Operations.KeygenRegistered.nil Operations.KeygenRegistered.append
  Operations.KeygenRegistered.region_cons
  Operations.KeygenRegistered.constrainInstance_cons
  Operations.KeygenRegistered.loadTable_cons
  List.forall_append List.forall_cons
  List.nil_append List.append_nil List.append_assoc
  and_self and_true true_and

attribute [keygen_norm]
  RegionCircuit.loopAux_forall RegionCircuit.forRange'_forall
  RegionCircuit.forRangeVar'_forall RegionCircuit.foldRangeVarAux_forall
  RegionCircuit.foldRangeVar_forall RegionCircuit.foldRange_forall

attribute [keygen_spine]
  RegionCircuit.loopAux_forall RegionCircuit.forRange'_forall
  RegionCircuit.forRangeVar'_forall RegionCircuit.foldRangeVarAux_forall
  RegionCircuit.foldRangeVar_forall RegionCircuit.foldRange_forall

@[keygen_norm]
theorem List.forall_ite {α : Type} (property : α → Prop)
    {condition : Prop} [Decidable condition] (yes no : List α) :
    (if condition then yes else no).Forall property ↔
      if condition then yes.Forall property else no.Forall property := by
  split <;> rfl

@[keygen_norm]
theorem List.forall_nil {α : Type} (property : α → Prop) :
    ([].Forall property) ↔ True :=
  Iff.rfl

open Lean Elab Tactic Meta

namespace KeygenRegistration

/-- Find a transparent configure-program head below an output/delta projection. -/
def configureHead? (target : Expr) : Option Name := do
  let projection ← target.find? fun expression =>
    expression.isAppOf ``Configure.delta ||
      expression.isAppOf ``Configure.output ||
      expression.isAppOf ``Configure.finalCounts ||
      expression.isAppOf ``Configure.plan
  let arguments := projection.getAppArgs
  guard (arguments.size ≥ 2)
  arguments[arguments.size - 2]!.getAppFn.constName?

/-- Find a transparent synthesis-body head below an operations projection. -/
def circuitHead? (target : Expr) : Option Name := do
  let projection ← target.find? fun expression =>
      expression.isAppOf ``RegionCircuit.operations ||
      expression.isAppOf ``Circuit.operations
  let arguments := projection.getAppArgs
  guard (arguments.size ≥ 2)
  arguments[arguments.size - 2]!.getAppFn.constName?

/-- Find a concrete formal-circuit bundle below one of its registered projections. -/
def bundleHeadIn? (projections : Array Name) (expression : Expr) : Option Name := do
  let projection ← expression.find? fun candidate =>
    projections.any candidate.isAppOf
  let bundle ← projection.getAppArgs.back?
  bundle.getAppFn.constName?

/-- Find a projected child bundle in the target or local hypotheses. -/
def bundleHead? : TacticM (Option Name) := withMainContext do
  let projections := keygenBundleProjectionAttr.getDecls (← getEnv)
  if let some head :=
      bundleHeadIn? projections (← instantiateMVars (← getMainTarget)) then
    return some head
  for declaration in ← getLCtx do
    if let some head :=
        bundleHeadIn? projections (← instantiateMVars declaration.type) then
      return some head
  return none

/-- Unfold registered metadata projections to a fixed point. -/
partial def unfoldMetadata : TacticM Unit := do
  let mut changed := false
  for projection in keygenMetadataProjectionAttr.getDecls (← getEnv) do
    let state ← saveState
    try
      evalTactic (← `(tactic| unfold $(mkIdent projection) at *))
      changed := true
    catch _ =>
      state.restore
  if changed then
    unfoldMetadata

/-- Reduce only concrete child bundle wrappers in call-routing side conditions. -/
partial def closeCallSideCondition
    (unfolded : Std.HashSet Name := {}) : TacticM Unit := do
  let state ← saveState
  try
    evalTactic (← `(tactic|
      first | assumption | exact () | rfl | simp_all only [keygen_norm]))
  catch _ =>
    state.restore
  if (← getGoals).isEmpty then
    return
  unfoldMetadata
  if (← getGoals).isEmpty then
    return
  let state ← saveState
  try
    evalTactic (← `(tactic| simp_all))
  catch _ =>
    state.restore
  if (← getGoals).isEmpty then
    return
  for constructor in keygenConfiguredAttr.getDecls (← getEnv) do
    let state ← saveState
    try
      let constructorTerm ← mkConstWithFreshMVarLevels constructor
      let sideConditions ← (← getMainGoal).apply constructorTerm
      let mut remaining := []
      for sideCondition in sideConditions do
        if ← liftMetaM sideCondition.isAssigned then
          continue
        setGoals [sideCondition]
        closeCallSideCondition unfolded
        remaining := remaining ++ (← getGoals)
      setGoals remaining
      if (← getGoals).isEmpty then
        return
      state.restore
    catch _ =>
      state.restore
  let some head ← bundleHead?
    | return
  if unfolded.contains head then
    return
  try
    evalTactic (← `(tactic| unfold $(mkIdent head) at *))
  catch _ =>
    return
  closeCallSideCondition (unfolded.insert head)

/--
Retry routed call obligations whenever an earlier obligation was discharged. This
matters when a configured-handle proof assigns metavariables shared by the later gate
and lookup inclusions.
-/
partial def closeCallGoals : TacticM Unit := do
  let before := (← getGoals).length
  let mut remaining := []
  for goal in ← getGoals do
    setGoals [goal]
    closeCallSideCondition
    remaining := remaining ++ (← getGoals)
  setGoals remaining
  if remaining.length < before then
    closeCallGoals

/-- Apply a registered certificate for a raw circuit helper. -/
def applyHelperCertificate : TacticM Bool := withMainContext do
  for candidate in keygenHelperAttr.getDecls (← getEnv) do
    let state ← saveState
    try
      let certificateLemma ← mkConstWithFreshMVarLevels candidate
      let sideConditions ← (← getMainGoal).apply certificateLemma
      let mut remaining := []
      for sideCondition in sideConditions do
        if ← liftMetaM sideCondition.isAssigned then
          continue
        setGoals [sideCondition]
        closeCallSideCondition
        remaining := remaining ++ (← getGoals)
      setGoals remaining
      if (← getGoals).isEmpty then
        return true
      state.restore
    catch _ =>
      state.restore
  return false

/-- Recover the formal-circuit bundle carried by a tagged call expression. -/
def taggedCallBundle? (target : Expr) : TacticM (Option Expr) := do
  let callExpressions := keygenCallExpressionAttr.getDecls (← getEnv)
  let bundleTypes := keygenCallBundleAttr.getDecls (← getEnv)
  let some call := target.find? fun expression =>
      callExpressions.any expression.isAppOf
    | return none
  for argument in call.getAppArgs do
    let type ← liftMetaM do
      whnf (← inferType argument)
    if bundleTypes.any type.isAppOf then
      return some argument
  return none

/-- Apply the mandatory certificate of a folded layouter- or region-level child call. -/
def applyChildCertificate : TacticM Bool := withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  let some bundle ← taggedCallBundle? target
    | return false
  let candidates := keygenCallAttr.getDecls (← getEnv)
  for candidate in candidates do
    let state ← saveState
    try
      let certificateLemma ← liftMetaM <| mkAppM candidate #[bundle]
      let sideConditions ← (← getMainGoal).apply certificateLemma
      let mut remaining := []
      for sideCondition in sideConditions do
        if ← liftMetaM sideCondition.isAssigned then
          continue
        setGoals [sideCondition]
        try
          evalTactic (← `(tactic| intros))
        catch _ =>
          pure ()
        closeCallSideCondition
        remaining := remaining ++ (← getGoals)
      setGoals remaining
      closeCallGoals
      return true
    catch _ =>
      state.restore
  return false

/-- Recursively normalize operation spines and conjunctions. -/
partial def close (unfolded : Std.HashSet Name := {}) : TacticM Unit := do
  let state ← saveState
  try
    evalTactic (← `(tactic| first | assumption | trivial))
  catch _ =>
    state.restore
  if (← getGoals).isEmpty then
    return

  if ← applyHelperCertificate then
    return
  if ← applyChildCertificate then
    return

  let state ← saveState
  try
    evalTactic (← `(tactic| simp_all only [keygen_spine]))
  catch _ =>
    state.restore
  if (← getGoals).isEmpty then
    return
  if ← applyHelperCertificate then
    return
  if ← applyChildCertificate then
    return

  let state ← saveState
  try
    evalTactic (← `(tactic|
      simp_all only [
        circuit_norm, keygen_norm,
        RegionOperation.KeygenRegistered,
        Operation.KeygenRegistered]))
  catch _ =>
    state.restore
  if (← getGoals).isEmpty then
    return
  let state ← saveState
  try
    evalTactic (← `(tactic| simp_all))
  catch _ =>
    state.restore
  if (← getGoals).isEmpty then
    return
  if ← applyHelperCertificate then
    return
  if ← applyChildCertificate then
    return

  withMainContext do
    let target ← whnf (← instantiateMVars (← getMainTarget))
    if target.isForall then
      evalTactic (← `(tactic| intro))
      close unfolded
      return

    if target.isAppOfArity ``And 2 then
      evalTactic (← `(tactic| constructor))
      let branches ← getGoals
      let mut remaining := []
      for branch in branches do
        setGoals [branch]
        close unfolded
        remaining := remaining ++ (← getGoals)
      setGoals remaining
      return

    let some head := circuitHead? target
      | return
    if unfolded.contains head || head == ``Nat.rec then
      return
    try
      evalTactic (← `(tactic| unfold $(mkIdent head)))
    catch _ =>
      return
    close (unfolded.insert head)

/--
Normalize all configure output/delta projections before opening the synthesis bind
spine. This ordering preserves formal-circuit `.call` heads for the registration rules.
-/
partial def prepareConfigure (unfolded : Std.HashSet Name := {}) : TacticM Unit := do
  let state ← saveState
  try
    evalTactic (← `(tactic|
      simp_all! +zetaDelta only [
        Configure.delta_bind, Configure.delta_pure,
        Configure.output_bind, Configure.output_pure,
        Configure.output_adviceColumn, Configure.output_fixedColumn,
        Configure.output_instanceColumn, Configure.output_selector,
        Configure.output_complexSelector, Configure.output_enableEquality,
        Configure.output_enableConstant, Configure.output_createGate,
        Configure.output_lookup,
        ConfigureDelta.gates_append, ConfigureDelta.lookups_append,
        ConfigureDelta.gates_queriedCells, ConfigureDelta.lookups_queriedCells,
        List.mem_append, List.mem_cons, List.mem_singleton,
        List.nil_append, List.append_nil, List.append_assoc]))
  catch _ =>
    state.restore
  if (← getGoals).isEmpty then
    return
  withMainContext do
    let target ← instantiateMVars (← getMainTarget)
    let some head := configureHead? target
      | return
    if unfolded.contains head then
      return
    try
      evalTactic (← `(tactic| unfold $(mkIdent head)))
    catch _ =>
      return
    prepareConfigure (unfolded.insert head)

end KeygenRegistration

/--
Default proof search for an `ElaboratedCircuit.registered` field.

It first applies the shared structural simp sets, then selectively unfolds named
configure/synthesis heads that still block a registration goal. Formal-circuit calls
stay opaque for explicit discharge through the compositional registration lemmas.
-/
elab "keygen_registration" : tactic => do
  evalTactic (← `(tactic| intros))
  KeygenRegistration.prepareConfigure
  KeygenRegistration.close

end Halo2
