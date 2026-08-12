import Clean.Halo2.Loops
import Clean.Halo2.KeygenAttr
import Batteries.Lean.TagAttribute
import Lean.Elab.Tactic

/-!
# Configure/synthesis registration automation

`keygen_registration` proves that every gate, lookup, and equality-dependent operation
in a circuit's synthesis stream is covered by caller-supplied or configure-produced
capabilities. The
normalization set is deliberately separate from `circuit_norm`: registration proofs
open configure deltas and operation streams, while ordinary circuit proofs preserve
formal-circuit call boundaries. Parent circuits discharge those folded calls with the
generic `call_keygenRegistered` lemmas.
-/

namespace Halo2

attribute [keygen_norm]
  RegionCircuit.Vector.map_getElem_mem_toList
  RegionCircuit.Vector.map_getElem!_mem_toList

open Lean

initialize registerTraceClass `Halo2.keygen

attribute [keygen_norm]
  ComplexSelector.toSelector_index ComplexSelector.toSelector_simple
  Configure.delta_bind Configure.delta_pure
  Configure.delta_permutationRequests
  Configure.delta_enableEquality_gates
  Configure.delta_enableEquality_lookups
  Configure.delta_enableEquality_permutationRequests
  Configure.plan_enableEquality_permutationRequests
  Configure.delta_selector Configure.delta_complexSelector
  Configure.delta_createGate
  Configure.output_bind Configure.output_pure
  Configure.output_adviceColumn Configure.output_fixedColumn
  Configure.output_instanceColumn Configure.output_selector
  Configure.output_complexSelector Configure.output_enableEquality
  Configure.output_enableConstant Configure.output_createGate
  Configure.output_lookup
  ConfigureDelta.gates_append ConfigureDelta.lookups_append
  ConfigureDelta.permutationRequests_append
  ConfigureDelta.gates_queriedCells ConfigureDelta.lookups_queriedCells
  ConfigureDelta.permutationRequests_queryAny
  ConfigureDelta.permutationRequests_queriedCells
  RegionOperation.KeygenRegistered Operation.KeygenRegistered
  KeygenRequirements.inputPermutationColumns
  RegionOperation.LookupActivationWellFormed
  Operation.LookupActivationsWellFormed
  RegionOperations.LookupActivationsWellFormed
  Operations.LookupActivationsWellFormed
  RegionOperation.assignedCells RegionOperation.copiedCells
  RegionOperations.assignedCells RegionOperations.copiedCells
  RegionOperations.CopyCellsAssigned
  RegionOperations.assignedCellsAfter
  Operation.copiedCells
  Operations.assignedCellsFrom Operations.assignedCells
  Operations.copiedCells Operations.CopyCellsAssigned
  LookupArgument.lookupActivationWellFormed_enable
  selectorEnabledAtIndex_cons_self complexSelectorEnabledAtIndex_cons_self
  Operations.KeygenRegistered.nil Operations.KeygenRegistered.append
  Operations.KeygenRegistered.region_cons
  Operations.KeygenRegistered.constrainInstance_cons
  Operations.KeygenRegistered.loadTable_cons
  List.forall_append List.forall_cons
  List.flatMap_cons List.flatMap_append
  List.mem_append List.mem_cons List.mem_singleton List.mem_flatMap List.mem_map
  List.not_mem_nil
  List.nil_append List.append_nil List.append_assoc
  and_self and_true true_and
  or_self or_true true_or or_false false_or
  false_implies implies_true forall_true_iff
  forall_eq forall_eq_or_imp imp_self or_imp
  ite_self
  Cell.of_column AssignedCell.of_cell
  output_assignAdvice output_assignRegion output_cellAt
  Vector.getElem_ofFn

attribute [grind norm]
  Configure.output_pure Configure.delta_pure

attribute [keygen_spine]
  RegionCircuit.operations_bind RegionCircuit.operations_pure
  Circuit.operations_bind Circuit.operations_pure
  operations_assignRegion operations_assignAdvice operations_assignFixed
  operations_copyAdvice operations_enable operations_enableLookup
  operations_constrainEqual operations_constrainInstance operations_loadTable
  operations_constrainConstant operations_assignAdviceFromInstance
  operations_cellAt operations_cellVec
  RegionOperation.KeygenRegistered Operation.KeygenRegistered
  KeygenRequirements.inputPermutationColumns
  RegionOperation.LookupActivationWellFormed
  Operation.LookupActivationsWellFormed
  RegionOperations.LookupActivationsWellFormed
  Operations.LookupActivationsWellFormed
  RegionOperation.assignedCells RegionOperation.copiedCells
  RegionOperations.assignedCells RegionOperations.copiedCells
  RegionOperations.CopyCellsAssigned
  RegionOperations.assignedCellsAfter
  Operation.copiedCells
  Operations.assignedCellsFrom Operations.assignedCells
  Operations.copiedCells Operations.CopyCellsAssigned
  Operations.KeygenRegistered.nil Operations.KeygenRegistered.append
  Operations.KeygenRegistered.region_cons
  Operations.KeygenRegistered.constrainInstance_cons
  Operations.KeygenRegistered.loadTable_cons
  List.forall_append List.forall_cons
  List.flatMap_cons List.flatMap_append
  List.mem_append List.mem_cons List.mem_singleton List.mem_flatMap List.mem_map
  List.nil_append List.append_nil List.append_assoc
  and_self and_true true_and
  or_self or_true true_or or_false false_or

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

@[keygen_norm]
theorem List.forall_true {α : Type} (values : List α) :
    values.Forall (fun _ => True) ↔ True := by
  induction values <;> simp_all

@[keygen_norm, keygen_spine]
theorem List.forall_nil_append {α : Type} (property : α → Prop) (values : List α) :
    ([].append values).Forall property ↔ values.Forall property :=
  Iff.rfl

attribute [keygen_spine] List.forall_nil
attribute [keygen_spine] RegionCircuit.operations_ite List.forall_ite

variable {F α β : Type}

theorem Configure.mem_gates_delta_bind_left
    (program : Configure F α) (next : α → Configure F β)
    (counts : ConfigureCounts) (gate : Gate F)
    (hgate : gate ∈ (program.delta counts).gates) :
    gate ∈ ((program >>= next).delta counts).gates := by
  rw [Configure.delta_bind, ConfigureDelta.gates_append]
  exact List.mem_append_left _ hgate

theorem Configure.mem_gates_delta_bind_right
    (program : Configure F α) (next : α → Configure F β)
    (counts : ConfigureCounts) (gate : Gate F)
    (hgate : gate ∈
      ((next (program.output counts)).delta
        (program.finalCounts counts)).gates) :
    gate ∈ ((program >>= next).delta counts).gates := by
  rw [Configure.delta_bind, ConfigureDelta.gates_append]
  exact List.mem_append_right _ hgate

theorem Configure.mem_lookups_delta_bind_left
    (program : Configure F α) (next : α → Configure F β)
    (counts : ConfigureCounts) (argument : LookupArgument F)
    (hargument : argument ∈ (program.delta counts).lookups) :
    argument ∈ ((program >>= next).delta counts).lookups := by
  rw [Configure.delta_bind, ConfigureDelta.lookups_append]
  exact List.mem_append_left _ hargument

theorem Configure.mem_lookups_delta_bind_right
    (program : Configure F α) (next : α → Configure F β)
    (counts : ConfigureCounts) (argument : LookupArgument F)
    (hargument : argument ∈
      ((next (program.output counts)).delta
        (program.finalCounts counts)).lookups) :
    argument ∈ ((program >>= next).delta counts).lookups := by
  rw [Configure.delta_bind, ConfigureDelta.lookups_append]
  exact List.mem_append_right _ hargument

theorem Configure.mem_permutationRequests_delta_bind_left
    (program : Configure F α) (next : α → Configure F β)
    (counts : ConfigureCounts) (column : AnyColumn)
    (hcolumn : column ∈ (program.delta counts).permutationRequests) :
    column ∈ ((program >>= next).delta counts).permutationRequests := by
  rw [Configure.delta_bind, ConfigureDelta.permutationRequests_append]
  exact List.mem_append_left _ hcolumn

theorem Configure.mem_permutationRequests_delta_bind_right
    (program : Configure F α) (next : α → Configure F β)
    (counts : ConfigureCounts) (column : AnyColumn)
    (hcolumn : column ∈
      ((next (program.output counts)).delta
        (program.finalCounts counts)).permutationRequests) :
    column ∈ ((program >>= next).delta counts).permutationRequests := by
  rw [Configure.delta_bind, ConfigureDelta.permutationRequests_append]
  exact List.mem_append_right _ hcolumn

theorem Configure.mem_permutationRequests_delta_enableEquality
    {kind : ColumnKind} (column : Column kind) (counts : ConfigureCounts) :
    column.toAny ∈
      ((enableEquality (F := F) column).delta counts).permutationRequests := by
  rw [Configure.delta_enableEquality_permutationRequests]
  exact List.mem_singleton_self column.toAny

theorem Configure.mem_gates_delta_createGate
    (gate : Gate F) (counts : ConfigureCounts) :
    gate ∈ ((createGate gate).delta counts).gates := by
  simp [Configure.delta_createGate]

@[keygen_norm, keygen_helper]
theorem assignAdvice_keygenRegistered
    {F : Type} [FiniteField F]
    (column : Column .advice) (row : ℕ) (compute : WitgenIR F 1)
    (self : RegionIndex) (gates : List (Gate F)) (lookups : List (LookupArgument F))
    (permutationColumns : List AnyColumn) :
    ((assignAdvice column row compute).operations self).Forall
      (RegionOperation.KeygenRegistered gates lookups permutationColumns) := by
  simp only [operations_assignAdvice, List.forall_cons,
    RegionOperation.KeygenRegistered, List.forall_nil, and_self]

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
  arguments[arguments.size - 2]!.headBeta.getAppFn.constName?

/-- Find a transparent synthesis-body head below an operations projection. -/
def circuitHead? (target : Expr) : Option Name := do
  let projection ← target.find? fun expression =>
      expression.isAppOf ``RegionCircuit.operations ||
      expression.isAppOf ``Circuit.operations
  let arguments := projection.getAppArgs
  guard (arguments.size ≥ 2)
  arguments[arguments.size - 2]!.headBeta.getAppFn.constName?

/-- Reduce registered bundle projections after their concrete bundle head has been
unfolded. Keeping this out of the general normalization set prevents opaque child
bundles from being expanded to their inferred elaboration instances prematurely. -/
def reduceBundleProjections : TacticM Unit := do
  let mut simpArgs : Array (TSyntax `Lean.Parser.Tactic.simpLemma) := #[]
  for projection in keygenRequirementProjectionAttr.getDecls (← getEnv) do
    let projectionIdent := mkIdent projection
    simpArgs := simpArgs.push
      (← `(Lean.Parser.Tactic.simpLemma| $projectionIdent:ident))
  evalTactic (← `(tactic|
    simp (config := { failIfUnchanged := false }) only [$[$simpArgs],*] at *))

/-- Unfold one concrete configure-program head, if doing so changes the goal. -/
def unfoldConfigureHead : TacticM Bool := withMainContext do
  let env ← getEnv
  let bundleProjections := keygenBundleProjectionAttr.getDecls env
  let acceptable (head : Name) : Bool :=
    !bundleProjections.contains head &&
      !env.isProjectionFn head &&
      match env.find? head with
      | some (.ctorInfo _) => false
      | _ => true
  let mut head? :=
    (configureHead? (← instantiateMVars (← getMainTarget))).filter acceptable
  if head?.isNone then
    let localContext ← getLCtx
    for fvarId in localContext.getFVarIds.reverse do
      let declaration := localContext.get! fvarId
      if let some head := (configureHead?
          (← instantiateMVars declaration.type)).filter acceptable then
        head? := some head
        break
  let some head := head?
    | return false
  let state ← saveState
  try
    evalTactic (← `(tactic| unfold $(mkIdent head) at *))
  catch _ =>
    state.restore
    return false
  reduceBundleProjections
  return true

/-- Beta-reduce only the circuit argument of an operations projection. -/
partial def betaReduceOperationPrograms (expression : Expr) : Expr :=
  let reduced :=
    match expression with
    | .app fn argument =>
        .app (betaReduceOperationPrograms fn) (betaReduceOperationPrograms argument)
    | .lam name type body info =>
        .lam name (betaReduceOperationPrograms type)
          (betaReduceOperationPrograms body) info
    | .forallE name type body info =>
        .forallE name (betaReduceOperationPrograms type)
          (betaReduceOperationPrograms body) info
    | .letE name type value body nonDep =>
        .letE name (betaReduceOperationPrograms type)
          (betaReduceOperationPrograms value) (betaReduceOperationPrograms body) nonDep
    | .mdata data body => .mdata data (betaReduceOperationPrograms body)
    | .proj type index body => .proj type index (betaReduceOperationPrograms body)
    | expression => expression
  if reduced.isAppOf ``RegionCircuit.operations ||
      reduced.isAppOf ``Circuit.operations then
    let arguments := reduced.getAppArgs
    if arguments.size ≥ 2 then
      mkAppN reduced.getAppFn
        (arguments.set! (arguments.size - 2)
          arguments[arguments.size - 2]!.headBeta)
    else
      reduced
  else
    reduced

/-- Follow nested registered projections to the concrete bundle receiver beneath them. -/
partial def bundleReceiverHead?
    (env : Lean.Environment) (projections : Array Name)
    (expression : Expr) : Option Name :=
  match expression.getAppFn.constName? with
  | some head =>
      if projections.contains head then
        let arguments := expression.getAppArgs
        let receiver? :=
          match env.getProjectionFnInfo? head with
          | some info => arguments[info.numParams]?
          | none => arguments.back?
        receiver?.bind (bundleReceiverHead? env projections)
      else
        some head
  | none =>
      match expression with
      | .proj _ _ receiver => bundleReceiverHead? env projections receiver
      | .mdata _ receiver => bundleReceiverHead? env projections receiver
      | _ => none

/-- Find a concrete formal-circuit bundle below one of its registered projections. -/
def bundleHeadIn? (env : Lean.Environment)
    (projections : Array Name) (expression : Expr) : Option Name := do
  let projection ← expression.find? fun candidate =>
    projections.any candidate.isAppOf
  let head ← projection.getAppFn.constName?
  let arguments := projection.getAppArgs
  let bundle ←
    match env.getProjectionFnInfo? head with
    | some info => arguments[info.numParams]?
    | none => arguments.back?
  bundleReceiverHead? env projections bundle

/-- Find a projected child bundle in the target or local hypotheses. -/
def bundleHead? : TacticM (Option Name) := withMainContext do
  let env ← getEnv
  let projections := keygenBundleProjectionAttr.getDecls env
  if let some head :=
      bundleHeadIn? env projections (← instantiateMVars (← getMainTarget)) then
    return some head
  for declaration in ← getLCtx do
    if let some head :=
        bundleHeadIn? env projections (← instantiateMVars declaration.type) then
      return some head
  return none

/-- Reduce metadata wrappers, then unfold only the concrete bundle exposed beneath
them. Bundle projections themselves stay intact until their receiver is concrete. -/
partial def unfoldMetadata : TacticM Unit := do
  let bundleProjections := keygenBundleProjectionAttr.getDecls (← getEnv)
  let mut changed := false
  for projection in keygenMetadataProjectionAttr.getDecls (← getEnv) do
    if bundleProjections.contains projection then
      continue
    let state ← saveState
    try
      evalTactic (← `(tactic| unfold $(mkIdent projection) at *))
      changed := true
    catch _ =>
      state.restore
  if changed then
    unfoldMetadata
    return
  let some head ← bundleHead?
    | return
  if let some (.ctorInfo _) := (← getEnv).find? head then
    reduceBundleProjections
    unfoldMetadata
    return
  try
    evalTactic (← `(tactic| unfold $(mkIdent head) at *))
  catch _ =>
    return
  reduceBundleProjections
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
  reduceBundleProjections
  if ← unfoldConfigureHead then
    closeCallSideCondition unfolded
    return
  let state ← saveState
  try
    evalTactic (← `(tactic| grind))
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

/-- Apply a registered certificate for a raw circuit helper. -/
def applyHelperCertificate : TacticM Bool := withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  let some targetHead := circuitHead? target
    | return false
  for candidate in keygenHelperAttr.getDecls (← getEnv) do
    let state ← saveState
    try
      let certificateLemma ← mkConstWithFreshMVarLevels candidate
      let some candidateHead := circuitHead? (← liftMetaM <| inferType certificateLemma)
        | state.restore
          continue
      if candidateHead != targetHead then
        state.restore
        continue
      let sideConditions ← (← getMainGoal).apply certificateLemma
      let mut remaining := []
      for sideCondition in sideConditions.reverse do
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

/-- Collect the formal-circuit-valued direct arguments of an application. -/
def directCallBundleArguments (bundleTypes : Array Name)
    (expression : Expr) : MetaM (Array Expr) := do
  let mut bundles := #[]
  for argument in expression.getAppArgs do
    try
      let type ← whnf (← inferType argument)
      if bundleTypes.any type.isAppOf && !bundles.any (· == argument) then
        bundles := bundles.push argument
    catch _ =>
      pure ()
  return bundles

/--
Find the first application whose head contains a tagged call and which directly carries
a formal-circuit bundle. This follows the opaque call wrapper without inspecting the
types of every argument in the surrounding synthesis proposition.
-/
partial def taggedCallBundlesIn (callExpressions bundleTypes : Array Name)
    (expression : Expr) : MetaM (Array Expr) := do
  let hasCallHead :=
    (expression.getAppFn.find? fun candidate =>
      callExpressions.any candidate.isAppOf).isSome
  if hasCallHead then
    let bundles ← directCallBundleArguments bundleTypes expression
    if !bundles.isEmpty then
      return bundles
  for argument in expression.getAppArgs do
    let bundles ← taggedCallBundlesIn callExpressions bundleTypes argument
    if !bundles.isEmpty then
      return bundles
  match expression with
  | .proj _ _ value =>
      taggedCallBundlesIn callExpressions bundleTypes value
  | .mdata _ value =>
      taggedCallBundlesIn callExpressions bundleTypes value
  | .letE _ _ value body _ =>
      taggedCallBundlesIn callExpressions bundleTypes (body.instantiate1 value)
  | .lam _ domain body _ | .forallE _ domain body _ =>
      let bundles ← taggedCallBundlesIn callExpressions bundleTypes domain
      if !bundles.isEmpty then
        return bundles
      taggedCallBundlesIn callExpressions bundleTypes body
  | _ =>
      return #[]

/-- Find formal-circuit-valued subexpressions without unfolding their definitions. -/
partial def formalCallBundlesIn (bundleTypes : Array Name)
    (expression : Expr) : MetaM (Array Expr) := do
  try
    let type ← whnf (← inferType expression)
    if bundleTypes.any type.isAppOf then
      return #[expression]
  catch _ =>
    pure ()
  for argument in expression.getAppArgs do
    let bundles ← formalCallBundlesIn bundleTypes argument
    if !bundles.isEmpty then
      return bundles
  match expression with
  | .proj _ _ value | .mdata _ value =>
      formalCallBundlesIn bundleTypes value
  | .letE _ _ value body _ =>
      let bundles ← formalCallBundlesIn bundleTypes value
      if !bundles.isEmpty then
        return bundles
      formalCallBundlesIn bundleTypes (body.instantiate1 value)
  | .lam _ domain body _ | .forallE _ domain body _ =>
      let bundles ← formalCallBundlesIn bundleTypes domain
      if !bundles.isEmpty then
        return bundles
      formalCallBundlesIn bundleTypes body
  | _ =>
      return #[]

/-- Recover the formal-circuit bundle carried by a tagged call expression. -/
def taggedCallBundles (target : Expr) : MetaM (Array Expr) := do
  let env ← getEnv
  let callExpressions := keygenCallExpressionAttr.getDecls env
  let bundleTypes := keygenCallBundleAttr.getDecls env
  let bundles ← taggedCallBundlesIn callExpressions bundleTypes target
  if !bundles.isEmpty then
    return bundles
  unless (target.find? fun candidate =>
      callExpressions.any candidate.isAppOf).isSome do
    return #[]
  formalCallBundlesIn bundleTypes target

/-- Find the formal-circuit bundle type among a certificate's explicit binders. -/
partial def certificateBundleType?
    (bundleTypes : Array Name) (type : Expr) : Option Name :=
  match type with
  | .forallE _ domain body _ =>
      match domain.getAppFn.constName? with
      | some head =>
          if bundleTypes.contains head then
            some head
          else
            certificateBundleType? bundleTypes body
      | none => certificateBundleType? bundleTypes body
  | .letE _ _ value body _ =>
      certificateBundleType? bundleTypes (body.instantiate1 value)
  | _ => none

/--
Search a local configured-handle product without opening either child's circuit.

Parent circuits store the provenance of each direct child in
`KeygenRequirements.configLawful`; composition turns that type into nested products.
The call simproc only needs to project the matching handle back out.
-/
partial def localProductWitness? (target : Expr) : SimpM (Option Expr) := do
  let rec search (candidate : Expr) (fuel : Nat) : SimpM (Option Expr) := do
    let candidateType ← withTransparency .all <| whnf (← inferType candidate)
    if ← isDefEq candidateType target then
      return some candidate
    if fuel == 0 then
      return none
    let candidateType ← whnf candidateType
    unless candidateType.isAppOfArity ``Prod 2 do
      return none
    if let some result ← search (mkProj ``Prod 0 candidate) (fuel - 1) then
      return some result
    search (mkProj ``Prod 1 candidate) (fuel - 1)

  for declaration in ← getLCtx do
    if let some result ← search declaration.toExpr 16 then
      return some result
  return none

/-- Extract a proof when simp has reduced a proposition to `True`. -/
def proofOfSimpTrue? (result : Simp.Result) : MetaM (Option Expr) := do
  unless result.expr.isConstOf ``True do
    return none
  match result.proof? with
  | some proof => return some (← mkOfEqTrue proof)
  | none => return some (mkConst ``True.intro)

/-- The symbolic allocation states at every node of an append-only configure tree. -/
partial def betaZetaHead (expression : Expr) : Expr :=
  match expression.headBeta with
  | .letE _ _ value body _ => betaZetaHead (body.instantiate1 value)
  | expression => expression

partial def configureNodesInProgram
    (program counts : Expr) (fuel : Nat := 256) :
    MetaM (Array (Expr × Expr)) := do
  if fuel == 0 then
    return #[(program, counts)]
  let originalProgram := betaZetaHead program
  let unfolded ←
    match ← withTransparency .default <| unfoldDefinition? originalProgram with
    | some unfolded => pure (betaZetaHead unfolded)
    | none => pure originalProgram
  let arguments := unfolded.getAppArgs
  let mut parts? : Option (Expr × Expr) := none
  if 2 ≤ arguments.size then
    for index in [0:arguments.size - 1] do
      let argumentType ← withTransparency .reducible <|
        whnf (← inferType arguments[index]!)
      if argumentType.getAppFn.isConstOf ``Configure then
        parts? := some (arguments[index]!, arguments[index + 1]!)
  let some (first, next) := parts?
    | return #[(originalProgram, counts)]
  unless (← inferType next).isForall do
    return #[(originalProgram, counts)]
  let firstNodes ← configureNodesInProgram first counts (fuel - 1)
  let firstOutput ← mkAppM ``Configure.output #[first, counts]
  let nextProgram := betaZetaHead (mkApp next firstOutput)
  let nextCounts ← mkAppM ``Configure.finalCounts #[first, counts]
  let remaining ← configureNodesInProgram nextProgram nextCounts (fuel - 1)
  return #[(originalProgram, counts)] ++ firstNodes ++ remaining

/-- Recover the parent configure tree's candidate child-entry allocation states. -/
def configureNodesInTarget (target : Expr) :
    MetaM (Array (Expr × Expr)) := do
  let some configureApp := target.find? fun expression =>
      expression.getAppFn.isConstOf ``Configure.delta
    | return #[]
  let arguments := configureApp.getAppArgs
  if arguments.size < 2 then
    return #[]
  configureNodesInProgram
    arguments[arguments.size - 2]! arguments[arguments.size - 1]!

/-- The configure projection paired with a tagged `Configured` constructor. -/
def configureProjectionOfConstructor? (env : Lean.Environment) (name : Name) :
    Option Name :=
  keygenConfiguredOutputAttr.getParam? env name <|>
    keygenConfiguredPureAttr.getParam? env name

def isConfiguredOfOutput (env : Lean.Environment) (name : Name) : Bool :=
  (keygenConfiguredOutputAttr.getParam? env name).isSome

def isConfiguredOfPure (env : Lean.Environment) (name : Name) : Bool :=
  (keygenConfiguredPureAttr.getParam? env name).isSome

/-- Fresh metavariables with products eta-expanded for projection-friendly unification. -/
partial def freshProductMVars (type : Expr) (fuel : Nat := 32) : MetaM Expr := do
  if fuel == 0 then
    return ← mkFreshExprMVar type
  let reducedType ← whnf type
  unless reducedType.isAppOfArity ``Prod 2 do
    return ← mkFreshExprMVar type
  let arguments := reducedType.getAppArgs
  let left ← freshProductMVars arguments[arguments.size - 2]! (fuel - 1)
  let right ← freshProductMVars arguments[arguments.size - 1]! (fuel - 1)
  mkAppM ``Prod.mk #[left, right]

/--
Retry a call-routing proposition with only its keygen metadata made transparent.
-/
def simpCallRouting (expression : Expr) : SimpM Simp.Result := do
  let env ← getEnv
  let requirementProjections := keygenRequirementProjectionAttr.getDecls env
  let configureProjections := keygenConfigureProjectionAttr.getDecls env
  let bundleTypes := keygenCallBundleAttr.getDecls env
  let outputProjections : SimpTheorems ←
    match ← getSimpExtension? `keygen_output_norm with
    | some extension => extension.getTheorems
    | none => pure {}
  let mut projections := outputProjections
  for projection in keygenMetadataProjectionAttr.getDecls env do
    projections ← projections.addDeclToUnfold projection
  projections ← projections.addConst ``List.mem_append
  projections ← projections.addConst ``List.mem_cons
  projections ← projections.addConst ``Cell.of_column
  projections ← projections.addConst ``AssignedCell.of_cell
  let mut ambient ← Simp.getSimpTheorems
  for declaration in ← getLCtx do
    if ← isProp declaration.type then
      let fact := declaration.toExpr
      ambient ← ambient.addTheorem (.fvar declaration.fvarId) fact
  -- First expose the child's requirement projection from the configured handle;
  -- only then does the concrete bundle occur at a reducible projection.
  let mut exposed ← Simp.withFreshCache <|
    Simp.withSimpTheorems (#[projections] ++ ambient) do
      Simp.simp expression
  let mut unfoldedReceivers : Array Name := #[]
  for _ in [0:8] do
    let requirementsApp? := exposed.expr.find? fun candidate =>
        let arguments := candidate.getAppArgs
        9 ≤ arguments.size &&
          (candidate.getAppFn.constName?.map requirementProjections.contains
            |>.getD false) &&
          (match (arguments.back?).bind (·.getAppFn.constName?) with
           | some receiverHead => !unfoldedReceivers.contains receiverHead
           | none => false)
    let receiver? :=
      match requirementsApp? with
      | some requirementsApp => requirementsApp.getAppArgs.back?
      | none =>
          let configureApp? : Option Expr := exposed.expr.find? fun (candidate : Expr) =>
            let arguments := candidate.getAppArgs
            9 ≤ arguments.size &&
              (candidate.getAppFn.constName?.map configureProjections.contains
                |>.getD false) &&
              (match (arguments.back?).bind (·.getAppFn.constName?) with
               | some receiverHead => !unfoldedReceivers.contains receiverHead
               | none => false)
          match configureApp? with
          | some configureApp =>
              let arguments := configureApp.getAppArgs
              some arguments[arguments.size - 1]!
          | none =>
              (exposed.expr.find? fun candidate =>
                match candidate with
                | .proj structureName _ receiver =>
                    bundleTypes.contains structureName &&
                    (match receiver.getAppFn.constName? with
                     | some receiverHead =>
                         !unfoldedReceivers.contains receiverHead
                     | none => false)
                | _ => false).bind fun
                  | .proj _ _ receiver => some receiver
                  | _ => none
    let some receiver := receiver?
      | break
    let some receiverHead := receiver.getAppFn.constName?
      | break
    trace[Halo2.keygen] "routing unfolds {receiverHead}"
    if unfoldedReceivers.contains receiverHead then
      break
    unfoldedReceivers := unfoldedReceivers.push receiverHead
    projections ← projections.addDeclToUnfold receiverHead
    let next ← Simp.withFreshCache <|
      Simp.withSimpTheorems (#[projections] ++ ambient) do
        Simp.simp exposed.expr
    exposed ← exposed.mkEqTrans next
  -- The formal-bundle projection leaves an opaque receiver below the requirement
  -- projections.
  -- Reduce precisely that small `KeygenRequirements` receiver and add its definitional
  -- equality as a local simp theorem. No synthesis field is projected or normalized.
  let some requirementProjection :=
      exposed.expr.find? fun expression =>
        expression.getAppFn.isConstOf ``KeygenRequirements.gates ||
          expression.getAppFn.isConstOf ``KeygenRequirements.lookups ||
          expression.getAppFn.isConstOf ``KeygenRequirements.permutationColumns ||
          expression.getAppFn.isConstOf ``KeygenRequirements.inputCells ||
          expression.getAppFn.isConstOf ``KeygenRequirements.inputPermutationColumns
    | return exposed
  let arguments := requirementProjection.getAppArgs
  -- `F`, `ConfigInput`, and `InputVar` precede the structure receiver.
  let some requirement := arguments[3]?
    | return exposed
  let reducedRequirement ← withTransparency .all <| whnf requirement
  if reducedRequirement == requirement then
    return exposed
  let reducedExpression := exposed.expr.replace fun candidate =>
    if candidate == requirement then some reducedRequirement else none
  unless ← withTransparency .all <| isDefEq exposed.expr reducedExpression do
    return exposed
  let definitionallyReduced : Simp.Result := { expr := reducedExpression }
  let reduced ← Simp.withFreshCache <|
    Simp.withSimpTheorems (#[projections] ++ ambient) do
      Simp.simp reducedExpression
  (← exposed.mkEqTrans definitionallyReduced).mkEqTrans reduced

/-- Expose only framework projections around a configure program, preserving its head. -/
partial def exposeConfigureProgram (program : Expr) (fuel : Nat := 8) :
    MetaM Expr := do
  if fuel == 0 then
    return program
  let program := program.headBeta
  if program.getAppFn.isProj then
    let reduced ← withTransparency .default <| whnf program
    if reduced != program then
      return ← exposeConfigureProgram reduced (fuel - 1)
  let some head := program.getAppFn.constName?
    | return program
  let env ← getEnv
  let projections := keygenMetadataProjectionAttr.getDecls env
  unless projections.contains head || env.isProjectionFn head do
    return program
  let some unfolded ← withTransparency .default <| unfoldDefinition? program
    | return program
  exposeConfigureProgram unfolded (fuel - 1)

/--
Recover or construct the configured handle required by a call certificate.

Composition normally projects it from the parent's direct-child provenance product.
Pure/output-configured helper calls instead use one of the framework constructors
tagged `keygen_configured`.
-/
partial def configuredWitness? (target : Expr)
    (candidateNodes : Array (Expr × Expr) := #[]) (fuel : Nat := 8) :
    SimpM (Option Expr) := do
  let configureProjections := keygenConfigureProjectionAttr.getDecls (← getEnv)
  let target ← withTransparency .all <| whnf target
  if ← isDefEq target (mkConst ``Unit) then
    return some (mkConst ``Unit.unit)
  if let some proof ← localProductWitness? target then
    return some proof
  if target.isAppOfArity ``Prod 2 then
    let arguments := target.getAppArgs
    let some left ← configuredWitness? arguments[arguments.size - 2]!
        candidateNodes (fuel - 1)
      | return none
    let some right ← configuredWitness? arguments[arguments.size - 1]!
        candidateNodes (fuel - 1)
      | return none
    return some (← mkAppM ``Prod.mk #[left, right])
  if fuel == 0 then
    return none
  let env ← getEnv
  let constructors := keygenConfiguredAttr.getDecls env
  let constructors :=
    constructors.filter (fun name =>
      !isConfiguredOfOutput env name) ++
    constructors.filter (fun name =>
      isConfiguredOfOutput env name)
  for constructor in constructors do
    if isConfiguredOfOutput env constructor then
      let some configureProjection :=
          configureProjectionOfConstructor? env constructor
        | continue
      let targetArguments := target.getAppArgs
      unless 2 ≤ targetArguments.size do
        continue
      let self := targetArguments[targetArguments.size - 2]!
      let config := targetArguments[targetArguments.size - 1]!
      for (program, counts) in candidateNodes do
        let metaState ← getThe Meta.State
        try
          let programType ← withTransparency .reducible <|
            whnf (← inferType program)
          unless programType.isAppOfArity ``Configure 2 do
            throwError "candidate is not a configure program"
          let programTypeArguments := programType.getAppArgs
          let configType ← inferType config
          unless ← isDefEq
              programTypeArguments[programTypeArguments.size - 1]!
              configType do
            throwError "candidate configure output has the wrong type"
          let candidateOutput ← mkAppM ``Configure.output #[program, counts]
          unless ← withTransparency .default <| isDefEq candidateOutput config do
            throwError "candidate configure output does not match the config"
          let configureFunction ← mkAppM configureProjection #[self]
          let configureFunctionType ← whnf (← inferType configureFunction)
          let .forallE _ configInputType _ _ := configureFunctionType
            | throwError "circuit configure projection is not a function"
          let configInput ← freshProductMVars configInputType
          let expectedProgram := mkApp configureFunction configInput
          let some selfHead := self.getAppFn.constName?
            | throwError "configured circuit has no named head"
          let mut circuitDefinition : SimpTheorems := {}
          circuitDefinition ← circuitDefinition.addDeclToUnfold selfHead
          let expectedProgram ← Simp.withFreshCache <|
            Simp.withSimpTheorems #[circuitDefinition] do
              return (← Simp.simp expectedProgram).expr
          let expectedProgram ← exposeConfigureProgram expectedProgram
          let comparisonProgram ←
            if expectedProgram.getAppFn.isConstOf ``Configure.mk then
              withTransparency .default <| whnf program
            else
              pure program
          trace[Halo2.keygen] "comparing configure program for {selfHead}"
          unless ← withTransparency .default <|
              isDefEq expectedProgram comparisonProgram do
            throwError "circuit configure program does not match the candidate"
          trace[Halo2.keygen] "compared configure program for {selfHead}"
          let partialApplication ←
            mkAppM constructor #[self, configInput, counts]
          let partialType ← whnf (← inferType partialApplication)
          let .forallE _ requirementType _ _ := partialType
            | throwError "configured constructor has no requirement argument"
          let some requirement ← configuredWitness?
              requirementType candidateNodes (fuel - 1)
            | throwError "configured requirement was not recovered"
          let proof ← instantiateMVars (mkApp partialApplication requirement)
          return some proof
        catch _ =>
          set metaState
      continue
    for _ in [0:1] do
      let metaState ← getThe Meta.State
      try
        let goalExpr ← mkFreshExprSyntheticOpaqueMVar target
        let sideConditions ← goalExpr.mvarId!.apply
          (← mkConstWithFreshMVarLevels constructor)
        for sideCondition in sideConditions do
          unless ← sideCondition.isAssigned do
            let sideTarget ← instantiateMVars (← sideCondition.getType)
            if ← isProp sideTarget then
              if isConfiguredOfPure env constructor then
                let targetArguments := target.getAppArgs
                unless 2 ≤ targetArguments.size do
                  throwError "configured target has no circuit argument"
                let self := targetArguments[targetArguments.size - 2]!
                let some selfHead := self.getAppFn.constName?
                  | throwError "configured circuit has no named head"
                let mut circuitDefinition : SimpTheorems := {}
                circuitDefinition ← circuitDefinition.addDeclToUnfold selfHead
                circuitDefinition ← circuitDefinition.addConst ``eq_self
                for projection in
                    keygenMetadataProjectionAttr.getDecls (← getEnv) do
                  circuitDefinition ←
                    circuitDefinition.addDeclToUnfold projection
                let mut result ← Simp.withFreshCache <|
                  Simp.withSimpTheorems #[circuitDefinition] do
                    Simp.simp sideTarget
                for _ in [0:8] do
                  if (← proofOfSimpTrue? result).isSome then
                    break
                  let some configureApp := result.expr.find? fun expression =>
                      let head := expression.getAppFn.constName?
                      head.map configureProjections.contains
                        |>.getD false
                    | break
                  let arguments := configureApp.getAppArgs
                  if arguments.size < 2 then
                    break
                  let receiver := arguments[arguments.size - 2]!
                  let some receiverHead := receiver.getAppFn.constName?
                    | break
                  circuitDefinition ←
                    circuitDefinition.addDeclToUnfold receiverHead
                  let next ← Simp.withFreshCache <|
                    Simp.withSimpTheorems #[circuitDefinition] do
                      Simp.simp result.expr
                  result ← result.mkEqTrans next
                let some proof ← proofOfSimpTrue? result
                  | throwError "circuit configure is not definitionally pure"
                sideCondition.assign proof
                continue
              try
                withTransparency .default sideCondition.refl
                continue
              catch _ =>
                pure ()
              let some proof ← proofOfSimpTrue? (← Simp.simp sideTarget)
                | throwError "configured constructor proposition was not simplified"
              sideCondition.assign proof
            else
              let some proof ←
                  configuredWitness? sideTarget candidateNodes (fuel - 1)
                | throwError "configured constructor input was not recovered"
              sideCondition.assign proof
        let proof ← instantiateMVars goalExpr
        unless proof.isMVar do
          return some proof
        throwError "configured constructor left unresolved metavariables"
      catch _ =>
        set metaState
  let targetArguments := target.getAppArgs
  if 2 ≤ targetArguments.size then
    trace[Halo2.keygen] "configured search failed at {
      targetArguments[targetArguments.size - 2]!.getAppFn.constName?}"
  return none

/--
Route one configured child's keygen capability through the append-only configure tree.

This deliberately explores one side of each bind at a time. Simplifying
`member ∈ (left ++ right)` eagerly normalizes both branches and is catastrophic for a
large aggregate configure such as Action; the proof below backtracks over the two
generic inclusion lemmas and never opens an unrelated suffix.
-/
partial def proveConfigureRoute (goal : MVarId) (sourceHead : Option Name)
    (fuel : Nat := 256) :
    MetaM Bool := do
  if fuel == 0 then
    return false
  let target ← instantiateMVars (← goal.getType)
  let deltaApp? := target.find? fun expression =>
    expression.getAppFn.isConstOf ``Configure.delta
  if let some deltaApp := deltaApp? then
    let arguments := deltaApp.getAppArgs
    if 2 ≤ arguments.size then
      let program := arguments[arguments.size - 2]!
      if program.headBeta.getAppFn.constName? == sourceHead then
        try
          goal.assumption
          return true
        catch _ =>
          pure ()
  let rules := #[
    ``Configure.mem_gates_delta_bind_right,
    ``Configure.mem_lookups_delta_bind_right,
    ``Configure.mem_permutationRequests_delta_bind_right,
    ``Configure.mem_gates_delta_bind_left,
    ``Configure.mem_lookups_delta_bind_left,
    ``Configure.mem_permutationRequests_delta_bind_left,
    ``Configure.mem_permutationRequests_delta_enableEquality,
    ``Configure.mem_gates_delta_createGate]
  for rule in rules do
    let metaState ← getThe Meta.State
    try
      let subgoals ← goal.apply (← mkConstWithFreshMVarLevels rule)
      if subgoals.length == 1 &&
          (← proveConfigureRoute subgoals[0]! sourceHead (fuel - 1)) then
        return true
      set metaState
    catch _ =>
      set metaState
  if let some deltaApp := deltaApp? then
    let arguments := deltaApp.getAppArgs
    if hsize : 2 ≤ arguments.size then
      let program := arguments[arguments.size - 2]
      if let some unfolded ← withTransparency .default <|
          unfoldDefinition? program then
        let unfoldedTarget := target.replace fun candidate =>
          if candidate == program then some unfolded else none
        try
          let unfoldedGoal ← goal.replaceTargetDefEq unfoldedTarget
          if ← proveConfigureRoute unfoldedGoal sourceHead (fuel - 1) then
            return true
        catch _ =>
          pure ()
  return false

/-- Introduce a routing premise and prove its final membership by bind traversal. -/
def proveConfigureRoutingPremise (goal : MVarId) : MetaM Bool := do
  let metaState ← getThe Meta.State
  try
    let mut current := goal
    let mut introduced : Option FVarId := none
    while (← instantiateMVars (← current.getType)).isForall do
      let (fvar, next) ← current.intro1P
      introduced := some fvar
      current := next
    try
      current.assumption
      return true
    catch _ =>
      pure ()
    let sourceHead ←
      match introduced with
      | none => pure none
      | some fvar =>
          let sourceType ← withTransparency .all <|
            whnf (← instantiateMVars (← fvar.getType))
          let deltaApp? := sourceType.find? fun expression =>
            expression.getAppFn.isConstOf ``Configure.delta
          let some deltaApp := deltaApp?
            | pure none
          let arguments := deltaApp.getAppArgs
          if 2 ≤ arguments.size then
            let program ← exposeConfigureProgram arguments[arguments.size - 2]!
            pure program.headBeta.getAppFn.constName?
          else
            pure none
    if ← proveConfigureRoute current sourceHead then
      return true
    set metaState
    return false
  catch _ =>
    set metaState
    return false

/--
Try one folded-call certificate against a registration proposition.

Meta code handles only the opaque boundary: choosing the certificate and recovering
the direct child's configured handle. All propositional routing premises are sent back
through the ambient simplifier.
-/
def proveWithCallCertificate?
    (target bundle : Expr) (candidate : Name) : SimpM (Option Expr) := do
  let metaState ← getThe Meta.State
  try
    let candidateNodes ← configureNodesInTarget target
    let certificate ← mkAppM candidate #[bundle]
    let goalExpr ← mkFreshExprSyntheticOpaqueMVar target
    let goal := goalExpr.mvarId!
    let sideConditions ← withTransparency .default <| goal.apply certificate
    -- Resolve Type-valued provenance first: the later Prop premises mention this
    -- witness through `.gates` and `.lookups`.
    for sideCondition in sideConditions do
      unless ← sideCondition.isAssigned do
        let sideTarget ← sideCondition.getType
        unless ← isProp sideTarget do
          let some proof ← configuredWitness? sideTarget candidateNodes
            | throwError m!"no direct-child configured handle for:\n{sideTarget}"
          trace[Halo2.keygen] "recovered configured handle"
          sideCondition.assign proof
    for sideCondition in sideConditions do
      unless ← sideCondition.isAssigned do
        let sideTarget ← instantiateMVars (← sideCondition.getType)
        if ← proveConfigureRoutingPremise sideCondition then
          trace[Halo2.keygen] "routed configure premise"
          continue
        let mut simplified ← Simp.simp sideTarget
        let mut proof? ← proofOfSimpTrue? simplified
        if proof?.isNone then
          simplified ← simpCallRouting sideTarget
          proof? ← proofOfSimpTrue? simplified
        let some proof := proof?
          | trace[Halo2.keygen] "routing residual:\n{simplified.expr}"
            throwError "keygen call routing premise was not simplified"
        sideCondition.assign proof
    let proof ← instantiateMVars goalExpr
    if proof.isMVar then
      throwError "keygen call certificate left unresolved metavariables"
    return some proof
  catch _ =>
    set metaState
    return none

/--
Fold an opaque child call to `True` using its tagged registration certificate.

This is deliberately a simproc rather than custom propositional proof search. It
recognizes the call and chooses the certificate; ordinary `keygen_norm` simp lemmas
prove the gate/lookup inclusions, so standard facts such as `true_or` remain fully
composable with circuit-local simp lemmas.
-/
def callRegistrationSimproc (target : Expr) : SimpM Simp.Step := do
  let bundles ← taggedCallBundles target
  if bundles.isEmpty then
    return .continue
  let env ← getEnv
  let bundleTypes := keygenCallBundleAttr.getDecls env
  let candidates := keygenCallAttr.getDecls env
  for bundle in bundles do
    let bundleType ← whnf (← inferType bundle)
    let some bundleTypeHead := bundleType.getAppFn.constName?
      | continue
    for candidate in candidates do
      let candidateInfo ← getConstInfo candidate
      if certificateBundleType? bundleTypes candidateInfo.type != some bundleTypeHead then
        continue
      if let some proof ← proveWithCallCertificate? target bundle candidate then
        return .done {
          expr := mkConst ``True
          proof? := some (← mkEqTrue proof) }
  return .continue

simproc callRegistration
    (Operations.KeygenRegistered _ _ _ _) := callRegistrationSimproc

simproc regionCallRegistration
    (List.Forall _ _) := callRegistrationSimproc

attribute [keygen_norm] callRegistration regionCallRegistration

/-- Target and hypothesis types used to detect normalization progress. -/
def goalContextTypes : TacticM (Array Expr) := withMainContext do
  let mut expressions := #[← instantiateMVars (← getMainTarget)]
  for declaration in ← getLCtx do
    expressions := expressions.push (← instantiateMVars declaration.type)
  return expressions

/-- Normalize the controlled keygen simp sets to a fixed point. -/
partial def normalize : TacticM Unit := do
  if (← getGoals).isEmpty then
    return
  unfoldMetadata
  if (← getGoals).isEmpty then
    return
  reduceBundleProjections
  if ← unfoldConfigureHead then
    normalize
    return
  let before ← goalContextTypes
  evalTactic (← `(tactic| simp (config := { failIfUnchanged := false }) only [
    keygen_spine, keygen_norm,
    Operations.KeygenRegistered, Operation.KeygenRegistered,
    RegionOperation.KeygenRegistered,
    Operations.KeygenRegistered.nil, Operations.KeygenRegistered.append,
    Operations.KeygenRegistered.region_cons,
    List.forall_append, List.forall_cons, List.forall_nil,
    List.nil_append, List.append_nil, List.append_assoc,
    operations_assignAdvice, assignAdvice_keygenRegistered,
    RegionCircuit.operations_ite, List.forall_ite] at *))
  if (← getGoals).isEmpty then
    return
  unfoldMetadata
  reduceBundleProjections
  if ← unfoldConfigureHead then
    normalize
    return
  let after ← goalContextTypes
  if before != after then
    normalize
    return
  let state ← saveState
  try
    evalTactic (← `(tactic| grind))
  catch _ =>
    state.restore
  if (← getGoals).isEmpty then
    return
  evalTactic (← `(tactic|
    simp_all (config := { failIfUnchanged := false }) only [keygen_norm]))

/-- Recursively normalize operation spines and conjunctions. -/
partial def close (unfolded : Std.HashSet Name := {}) : TacticM Unit := do
  withMainContext do
    let target ← instantiateMVars (← getMainTarget)
    let reduced := betaReduceOperationPrograms target
    if reduced != target then
      let goal ← (← getMainGoal).change reduced (checkDefEq := false)
      setGoals [goal]

  let state ← saveState
  try
    evalTactic (← `(tactic| assumption))
  catch _ =>
    state.restore
  if (← getGoals).isEmpty then
    return

  if ← applyHelperCertificate then
    return

  normalize
  if (← getGoals).isEmpty then
    return
  if ← applyHelperCertificate then
    return

  withMainContext do
    let target ← instantiateMVars (← getMainTarget)
    let target ←
      if target.isAppOf ``List.Forall then
        pure target
      else
        whnf target
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

    if target.isAppOf ``List.Forall then
      if target.getAppArgs.back!.isAppOf ``List.append then
        evalTactic (← `(tactic| apply List.forall_append.mpr))
        close unfolded
        return

    if let some head := circuitHead? target then
      if unfolded.contains head || head == ``Nat.rec then
        return
      try
        evalTactic (← `(tactic| unfold $(mkIdent head)))
      catch _ =>
        return
      close (unfolded.insert head)
      return

    if target.isAppOf ``List.Forall then
      let operations ← whnf target.getAppArgs.back!
      if (operations.isAppOf ``List.nil || operations.isAppOf ``List.cons) &&
          operations != target.getAppArgs.back! then
        let arguments :=
          target.getAppArgs.set! (target.getAppArgs.size - 1) operations
        let normalizedTarget := mkAppN target.getAppFn arguments
        let goal ← (← getMainGoal).replaceTargetDefEq normalizedTarget
        setGoals [goal]
        close unfolded
        return

    let state ← saveState
    try
      evalTactic (← `(tactic| grind))
    catch _ =>
      state.restore

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
        ConfigureDelta.permutationRequests_append,
        ConfigureDelta.gates_queriedCells, ConfigureDelta.lookups_queriedCells,
        ConfigureDelta.permutationRequests_queriedCells,
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

/-- Run the configure fallback independently on every residual structural branch. -/
def finishConfigureGoals : TacticM Unit := do
  let mut remaining := []
  for goal in ← getGoals do
    setGoals [goal]
    prepareConfigure
    close
    remaining := remaining ++ (← getGoals)
  setGoals remaining

end KeygenRegistration

/--
Default proof search for an `ElaboratedCircuit.registered` field.

It first applies the shared structural simp sets, then selectively unfolds named
configure/synthesis heads that still block a registration goal. Formal-circuit calls
stay opaque for explicit discharge through the compositional registration lemmas.
-/
elab "keygen_registration" : tactic => do
  if (← getGoals).isEmpty then
    return
  trace[Halo2.keygen] "keygen_registration: introductions"
  evalTactic (← `(tactic| intros))
  if (← getGoals).isEmpty then
    return
  trace[Halo2.keygen] "keygen_registration: configure preparation"
  KeygenRegistration.prepareConfigure
  trace[Halo2.keygen] "keygen_registration: initial normalization"
  evalTactic (← `(tactic|
    simp_all! +zetaDelta (config := { failIfUnchanged := false }) only [
      keygen_spine, keygen_norm, keygen_output_norm]))
  if (← getGoals).isEmpty then
    return
  trace[Halo2.keygen] "keygen_registration: structural close"
  KeygenRegistration.close
  if !(← getGoals).isEmpty then
    evalTactic (← `(tactic|
      simp_all! +zetaDelta (config := { failIfUnchanged := false }) only [
        keygen_spine, keygen_norm, keygen_output_norm]))
  if !(← getGoals).isEmpty then
    trace[Halo2.keygen] "keygen_registration: configure fallback"
    KeygenRegistration.finishConfigureGoals

macro "keygen_registration" " [" definitions:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| (dsimp only [$definitions,*] <;> keygen_registration))

elab "configure_route" : tactic => do
  let goal ← getMainGoal
  unless ← KeygenRegistration.proveConfigureRoutingPremise goal do
    throwError "configure_route could not find the configured child in the parent program"

end Halo2
