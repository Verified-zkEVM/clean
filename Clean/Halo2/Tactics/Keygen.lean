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

attribute [keygen_norm]
  Configure.delta_bind Configure.delta_pure
  Configure.delta_enableEquality_gates
  Configure.delta_enableEquality_lookups
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
  List.mem_append List.mem_cons List.mem_singleton List.not_mem_nil
  List.nil_append List.append_nil List.append_assoc
  and_self and_true true_and
  or_self or_true true_or or_false false_or
  false_implies implies_true forall_true_iff
  ite_self

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
  Operations.KeygenRegistered.nil Operations.KeygenRegistered.append
  Operations.KeygenRegistered.region_cons
  Operations.KeygenRegistered.constrainInstance_cons
  Operations.KeygenRegistered.loadTable_cons
  List.forall_append List.forall_cons
  List.mem_append List.mem_cons List.mem_singleton
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

@[keygen_norm, keygen_spine]
theorem List.forall_nil_append {α : Type} (property : α → Prop) (values : List α) :
    ([].append values).Forall property ↔ values.Forall property :=
  Iff.rfl

attribute [keygen_spine] List.forall_nil
attribute [keygen_spine] RegionCircuit.operations_ite List.forall_ite

@[keygen_norm, keygen_helper]
theorem assignAdvice_keygenRegistered
    {F : Type} [FiniteField F]
    (column : Column .advice) (row : ℕ) (compute : WitgenIR F 1)
    (self : RegionIndex) (gates : List (Gate F)) (lookups : List (LookupArgument F)) :
    ((assignAdvice column row compute).operations self).Forall
      (RegionOperation.KeygenRegistered gates lookups) := by
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

/--
Retry a call-routing proposition with only its keygen metadata made transparent.
-/
def simpCallRouting (expression : Expr) : SimpM Simp.Result := do
  let env ← getEnv
  let mut projections : SimpTheorems := {}
  for projection in keygenMetadataProjectionAttr.getDecls env do
    projections ← projections.addDeclToUnfold projection
  let ambient ← Simp.getSimpTheorems
  -- First expose the child's requirement projection from the configured handle;
  -- only then does the concrete bundle occur at a reducible projection.
  let exposed ← Simp.withFreshCache <|
    Simp.withSimpTheorems (#[projections] ++ ambient) do
      Simp.simp expression
  -- The formal-bundle projection leaves an opaque receiver below `gates`/`lookups`.
  -- Reduce precisely that small `KeygenRequirements` receiver and add its definitional
  -- equality as a local simp theorem. No synthesis field is projected or normalized.
  let some requirementProjection :=
      exposed.expr.find? fun expression =>
        expression.getAppFn.isConstOf ``KeygenRequirements.gates ||
          expression.getAppFn.isConstOf ``KeygenRequirements.lookups
    | return exposed
  let arguments := requirementProjection.getAppArgs
  let some requirement := arguments[2]?
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

/--
Recover or construct the configured handle required by a call certificate.

Composition normally projects it from the parent's direct-child provenance product.
Pure/output-configured helper calls instead use one of the framework constructors
tagged `keygen_configured`.
-/
partial def configuredWitness? (target : Expr) (fuel : Nat := 4) :
    SimpM (Option Expr) := do
  let normalizedTarget ← withTransparency .all <| whnf target
  if ← isDefEq normalizedTarget (mkConst ``Unit) then
    return some (mkConst ``Unit.unit)
  if let some proof ← localProductWitness? target then
    return some proof
  if fuel == 0 then
    return none
  for constructor in keygenConfiguredAttr.getDecls (← getEnv) do
    let metaState ← getThe Meta.State
    try
      let goalExpr ← mkFreshExprSyntheticOpaqueMVar target
      let sideConditions ← goalExpr.mvarId!.apply
        (← mkConstWithFreshMVarLevels constructor)
      for sideCondition in sideConditions do
        unless ← sideCondition.isAssigned do
          let sideTarget ← instantiateMVars (← sideCondition.getType)
          if ← isProp sideTarget then
            try
              withTransparency .all sideCondition.refl
              continue
            catch _ =>
              pure ()
            let some proof ← proofOfSimpTrue? (← Simp.simp sideTarget)
              | throwError "configured constructor proposition was not simplified"
            sideCondition.assign proof
          else
            let some proof ← configuredWitness? sideTarget (fuel - 1)
              | throwError "configured constructor input was not recovered"
            sideCondition.assign proof
      let proof ← instantiateMVars goalExpr
      unless proof.isMVar do
        return some proof
      throwError "configured constructor left unresolved metavariables"
    catch _ =>
      set metaState
  return none

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
          let some proof ← configuredWitness? sideTarget
            | throwError m!"no direct-child configured handle for:\n{sideTarget}"
          sideCondition.assign proof
    for sideCondition in sideConditions do
      unless ← sideCondition.isAssigned do
        let sideTarget ← instantiateMVars (← sideCondition.getType)
        let mut simplified ← Simp.simp sideTarget
        let mut proof? ← proofOfSimpTrue? simplified
        if proof?.isNone then
          simplified ← simpCallRouting sideTarget
          proof? ← proofOfSimpTrue? simplified
        let some proof := proof?
          | throwError "keygen call routing premise was not simplified"
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
    (Operations.KeygenRegistered _ _ _) := callRegistrationSimproc

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
  evalTactic (← `(tactic| intros))
  KeygenRegistration.prepareConfigure
  evalTactic (← `(tactic|
    simp_all! +zetaDelta (config := { failIfUnchanged := false }) only [
      keygen_spine, keygen_norm]))
  if (← getGoals).isEmpty then
    return
  KeygenRegistration.close
  if !(← getGoals).isEmpty then
    KeygenRegistration.finishConfigureGoals

end Halo2
