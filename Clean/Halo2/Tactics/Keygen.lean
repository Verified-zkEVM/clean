import Clean.Halo2.Loops
import Clean.Halo2.KeygenAttr
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
  Operations.KeygenRegistered.nil Operations.KeygenRegistered.append
  Operations.KeygenRegistered.region_cons
  Operations.KeygenRegistered.constrainInstance_cons
  Operations.KeygenRegistered.loadTable_cons
  List.forall_append List.mem_append List.mem_cons List.mem_singleton
  List.nil_append List.append_nil List.append_assoc
  and_self and_true true_and ite_self

attribute [keygen_norm]
  RegionCircuit.loopAux_forall RegionCircuit.forRange'_forall
  RegionCircuit.forRangeVar'_forall

@[keygen_norm]
theorem List.forall_ite {α : Type} (property : α → Prop)
    {condition : Prop} [Decidable condition] (yes no : List α) :
    (if condition then yes else no).Forall property ↔
      if condition then yes.Forall property else no.Forall property := by
  split <;> rfl

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

/-- Recursively normalize operation spines and conjunctions. -/
partial def close (unfolded : Std.HashSet Name := {}) : TacticM Unit := do
  let state ← saveState
  try
    evalTactic (← `(tactic|
      simp_all only [circuit_norm, keygen_norm]))
  catch _ =>
    state.restore
  if (← getGoals).isEmpty then
    return

  withMainContext do
    let target ← whnf (← instantiateMVars (← getMainTarget))
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
