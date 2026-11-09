import Clean.Halo2.Keygen.PdqsortEvaluation
import Mathlib.Tactic.ToExpr
import Lean.Elab.Command
import Lean.Meta.Tactic.Simp.Main
import Lean.Meta.Transform

/-!
# Kernel-checked concrete pdqsort evaluation

`pdqsort_certify result input using less` proves the exact result of the legacy
pdqsort implementation, including its order among tied keys. The input must be a closed
array with executable `Inhabited` and `ToExpr` instances for its element type.

Candidate states are computed by untrusted metaprogram execution. Each primitive step
is then checked by the kernel, and generic composition lemmas assemble the final equality.
No native-decide axiom is used. Shared auxiliary definitions and separate proof constants
keep the kernel from retaining or recomputing an entire recursive sort in one reduction.
-/

open Lean Meta Halo2.FloorPlanner

deriving instance ToExpr for Pdqsort.Plan
deriving instance ToExpr for Pdqsort.Request
deriving instance ToExpr for Pdqsort.Layer
deriving instance ToExpr for Pdqsort.PartitionSetup
deriving instance ToExpr for Pdqsort.BlockLoopState
deriving instance ToExpr for ForInStep

namespace Halo2.FloorPlanner.Pdqsort.Certify

theorem runSteps_done {S : Type} (step : S → ForInStep S) (fuel : Nat)
    (state result : S) (hStep : step state = .done result) :
    Pdqsort.runSteps step (fuel + 1) state = result := by
  simp only [Pdqsort.runSteps, hStep]

theorem runSteps_yield {S : Type} (step : S → ForInStep S) (fuel : Nat)
    (state next result : S) (hStep : step state = .yield next)
    (hRest : Pdqsort.runSteps step fuel next = result) :
    Pdqsort.runSteps step (fuel + 1) state = result := by
  simp only [Pdqsort.runSteps, hStep, hRest]

theorem partitionInBlocks_of_steps {T : Type} [Inhabited T]
    (values : Array T) (pivot : T) (less : T → T → Bool)
    (final : Pdqsort.BlockLoopState T) (result : Nat × Array T)
    (hRun : Pdqsort.runSteps (Pdqsort.blockLoopStep pivot less)
      (values.size + 4) (Pdqsort.initialBlockLoopState values) = final)
    (hFinish : Pdqsort.finishBlockLoop final = result) :
    Pdqsort.partitionInBlocks values pivot less = result := by
  rw [Pdqsort.partitionInBlocks_eq_partitionInBlocksBySteps]
  unfold Pdqsort.partitionInBlocksBySteps
  rw [hRun, hFinish]

theorem partitionP_of_steps {T : Type} [Inhabited T]
    (values : Array T) (pivot : Nat) (less : T → T → Bool)
    (setup : Pdqsort.PartitionSetup T) (blockInput : Array T)
    (blockResult : Nat × Array T) (result : (Nat × Bool) × Array T)
    (hSetup : Pdqsort.preparePartition values pivot less = setup)
    (hInput : setup.values.extract (1 + setup.left) (1 + setup.right) = blockInput)
    (hBlocks : Pdqsort.partitionInBlocks blockInput setup.pivot less = blockResult)
    (hFinish : Pdqsort.finishPartition setup blockResult = result) :
    Pdqsort.partitionP values pivot less = result := by
  rw [Pdqsort.partitionP_eq_partitionPFactored]
  unfold Pdqsort.partitionPFactored
  simp only [hSetup]
  rw [hInput, hBlocks, hFinish]

/-- One candidate equation. Composite equations refer to previously checked equations
by their left-hand sides; primitive equations are checked by kernel reduction. -/
structure Event where
  lhs : Expr
  rhs : Expr
  unfoldNames : List Name := []
  assemble : Option (Name × Array (Sum Expr Expr)) := none

structure Quotation where
  type : Expr
  inhabited : Expr
  less : Expr

def Quotation.call (q : Quotation) (name : Name) (args : Array Expr) : Expr :=
  mkAppN (mkConst name) (#[q.type, q.inhabited] ++ args)

def event {α : Type} [ToExpr α] (lhs : Expr) (rhs : α)
    (unfoldNames : List Name := []) : Event :=
  { lhs, rhs := toExpr rhs, unfoldNames }

variable {T : Type} [Inhabited T]

theorem recursePlanned_done (fuel : Nat) (input : Array T) (less : T → T → Bool)
    (pred : Option T) (limit : Nat) (balanced partitioned : Bool) (output : Array T)
    (hLayer : Pdqsort.stepLayer input less pred limit balanced partitioned = .done output) :
    Pdqsort.recursePlanned (fuel + 1) .done input less pred limit balanced partitioned =
      some output := by
  rw [Pdqsort.recursePlanned.eq_2, Pdqsort.recurseStepPlanned_eq_interpretLayer, hLayer]
  rfl

theorem recursePlanned_unary (fuel : Nat) (input : Array T) (less : T → T → Bool)
    (pred : Option T) (limit : Nat) (balanced partitioned : Bool)
    (head : Array T) (child : Pdqsort.Request T) (childPlan : Pdqsort.Plan) (tail : Array T)
    (hLayer : Pdqsort.stepLayer input less pred limit balanced partitioned = .unary head child)
    (hChild : Pdqsort.recursePlanned fuel childPlan child.input less child.predecessor
      child.limit child.wasBalanced child.wasPartitioned = some tail) :
    Pdqsort.recursePlanned (fuel + 1) (.unary childPlan) input less pred limit balanced partitioned =
      some (head ++ tail) := by
  rw [Pdqsort.recursePlanned.eq_2, Pdqsort.recurseStepPlanned_eq_interpretLayer, hLayer]
  simp only [Pdqsort.interpretLayer, hChild]
  rfl

theorem recursePlanned_binary (fuel : Nat) (input : Array T) (less : T → T → Bool)
    (pred : Option T) (limit : Nat) (balanced partitioned : Bool)
    (left : Pdqsort.Request T) (pivot : T) (right : Pdqsort.Request T)
    (leftPlan rightPlan : Pdqsort.Plan) (leftOutput rightOutput : Array T)
    (hLayer : Pdqsort.stepLayer input less pred limit balanced partitioned = .binary left pivot right)
    (hLeft : Pdqsort.recursePlanned fuel leftPlan left.input less left.predecessor
      left.limit left.wasBalanced left.wasPartitioned = some leftOutput)
    (hRight : Pdqsort.recursePlanned fuel rightPlan right.input less right.predecessor
      right.limit right.wasBalanced right.wasPartitioned = some rightOutput) :
    Pdqsort.recursePlanned (fuel + 1) (.binary leftPlan rightPlan) input less pred limit balanced partitioned =
      some (leftOutput ++ #[pivot] ++ rightOutput) := by
  rw [Pdqsort.recursePlanned.eq_2, Pdqsort.recurseStepPlanned_eq_interpretLayer, hLayer]
  simp only [Pdqsort.interpretLayer, hLeft, hRight]
  rfl

variable [ToExpr T]

/-- Split a partition into bounded block-loop steps and their generic composition. -/
def partitionEvents (q : Quotation) (values : Array T)
    (less : T → T → Bool) (pivot : Nat) : List Event := Id.run do
  let setup := Pdqsort.preparePartition values pivot less
  let blockInput := setup.values.extract (1 + setup.left) (1 + setup.right)
  let mut events := [
    event (q.call ``Pdqsort.preparePartition #[toExpr values, toExpr pivot, q.less]) setup,
    event (mkAppN (mkConst ``Array.extract [0])
      #[q.type, toExpr setup.values, toExpr (1 + setup.left), toExpr (1 + setup.right)]) blockInput]
  let initial := Pdqsort.initialBlockLoopState blockInput
  let mut state := initial
  let mut history := #[]
  for _ in [:blockInput.size + 4] do
    let step := Pdqsort.blockLoopStep setup.pivot less state
    history := history.push (state, step)
    events := events ++ [event
      (q.call ``Pdqsort.blockLoopStep #[toExpr setup.pivot, q.less, toExpr state]) step]
    match step with
    | .done final => state := final; break
    | .yield next => state := next
  let stateType := mkApp (mkConst ``Pdqsort.BlockLoopState) q.type
  let stepFn := q.call ``Pdqsort.blockLoopStep #[toExpr setup.pivot, q.less]
  let runCall := fun fuel (s : Pdqsort.BlockLoopState T) =>
    mkAppN (mkConst ``Pdqsort.runSteps) #[stateType, stepFn, toExpr fuel, toExpr s]
  if history.size == blockInput.size + 4 then
    events := events ++ [event (runCall (0 : Nat) state) state]
  for index in (List.range history.size).reverse do
    let (before, step) := history[index]!
    let fuel := blockInput.size + 4 - index - 1
    let stepCall := mkApp stepFn (toExpr before)
    let (name, args) := match step with
      | .done _ => (``runSteps_done, #[.inl stateType, .inl stepFn, .inl (toExpr fuel),
          .inl (toExpr before), .inl (toExpr state), .inr stepCall])
      | .yield next => (``runSteps_yield, #[.inl stateType, .inl stepFn, .inl (toExpr fuel),
          .inl (toExpr before), .inl (toExpr next), .inl (toExpr state),
          .inr stepCall, .inr (runCall fuel next)])
    events := events ++ [{ (event (runCall (fuel + 1) before) state) with
      assemble := some (name, args) }]
  let blockResult := Pdqsort.finishBlockLoop state
  events := events ++ [
    event (q.call ``Pdqsort.finishBlockLoop #[toExpr state]) blockResult,
    { (event (q.call ``Pdqsort.partitionInBlocks #[toExpr blockInput, toExpr setup.pivot, q.less])
        blockResult) with assemble := some (``partitionInBlocks_of_steps, #[
          .inl q.type, .inl q.inhabited, .inl (toExpr blockInput), .inl (toExpr setup.pivot),
          .inl q.less, .inl (toExpr state), .inl (toExpr blockResult),
          .inr (runCall (blockInput.size + 4) initial),
          .inr (q.call ``Pdqsort.finishBlockLoop #[toExpr state])]) }]
  let result := Pdqsort.finishPartition setup blockResult
  let composed := { (event
      (q.call ``Pdqsort.partitionP #[toExpr values, toExpr pivot, q.less]) result) with
    assemble := some (``partitionP_of_steps, #[
      .inl q.type, .inl q.inhabited, .inl (toExpr values), .inl (toExpr pivot), .inl q.less,
      .inl (toExpr setup), .inl (toExpr blockInput), .inl (toExpr blockResult), .inl (toExpr result),
      .inr (q.call ``Pdqsort.preparePartition #[toExpr values, toExpr pivot, q.less]),
      .inr (mkAppN (mkConst ``Array.extract [0])
        #[q.type, toExpr setup.values, toExpr (1 + setup.left), toExpr (1 + setup.right)]),
      .inr (q.call ``Pdqsort.partitionInBlocks #[toExpr blockInput, toExpr setup.pivot, q.less]),
      .inr (q.call ``Pdqsort.finishPartition #[toExpr setup, toExpr blockResult])]) }
  events := events ++ [
    event (q.call ``Pdqsort.finishPartition #[toExpr setup, toExpr blockResult]) result,
    composed]
  return events

def layerEvents (q : Quotation) (values : Array T) (less : T → T → Bool)
    (pred : Option T) (limit : Nat) (balanced partitioned : Bool) : List Event := Id.run do
  let result := Pdqsort.stepLayer values less pred limit balanced partitioned
  let mut events := []
  if values.size ≤ 20 then
    events := [event (q.call ``Pdqsort.insertionSort #[toExpr values, q.less])
      (Pdqsort.insertionSort values less)]
  else if limit == 0 then
    events := [event (q.call ``Pdqsort.heapsort #[toExpr values, q.less])
      (Pdqsort.heapsort values less)]
  else
    let adjusted := if balanced then values else Pdqsort.breakPatterns values
    let adjustedLimit := if balanced then limit else limit - 1
    if !balanced then
      events := [event (q.call ``Pdqsort.breakPatterns #[toExpr values]) adjusted]
    let chosen := Pdqsort.choosePivot adjusted less
    events := events ++ [event (q.call ``Pdqsort.choosePivot #[toExpr adjusted, q.less]) chosen]
    let pivot := chosen.1.1
    let mut selected := chosen.2
    let mut finished := false
    if balanced && partitioned && chosen.1.2 then
      let partialResult := Pdqsort.partialInsertionSort selected less
      events := events ++ [event
        (q.call ``Pdqsort.partialInsertionSort #[toExpr selected, q.less]) partialResult]
      selected := partialResult.2
      finished := partialResult.1
    if !finished then
      if pred.any (fun p => !less p selected[pivot]!) then
        events := events ++ [event
          (q.call ``Pdqsort.partitionEqual #[toExpr selected, toExpr pivot, q.less])
          (Pdqsort.partitionEqual selected pivot less)]
      else
        events := events ++ partitionEvents q selected less pivot
        let partitionedResult := Pdqsort.partitionP selected pivot less
        let partitionLayer := Pdqsort.partitionResultLayer pred adjustedLimit values.size partitionedResult
        events := events ++ [
          event (q.call ``Pdqsort.partitionResultLayer #[toExpr pred, toExpr adjustedLimit,
            toExpr values.size, toExpr partitionedResult]) partitionLayer,
          event (q.call ``Pdqsort.partitionLayer #[toExpr selected, q.less, toExpr pred,
            toExpr adjustedLimit, toExpr values.size, toExpr pivot]) partitionLayer
            [``Pdqsort.partitionLayer]]
      events := events ++ [event
        (q.call ``Pdqsort.predecessorLayer #[toExpr selected, q.less, toExpr pred,
          toExpr adjustedLimit, toExpr values.size, toExpr balanced, toExpr partitioned,
          toExpr pivot]) result [``Pdqsort.predecessorLayer]]
    events := events ++ [
      event (q.call ``Pdqsort.afterPivotLayer #[toExpr chosen.2, q.less, toExpr pred,
        toExpr adjustedLimit, toExpr values.size, toExpr balanced, toExpr partitioned,
        toExpr chosen.1.2, toExpr pivot]) result [``Pdqsort.afterPivotLayer],
      event (q.call ``Pdqsort.chooseLayer #[toExpr adjusted, q.less, toExpr pred,
        toExpr adjustedLimit, toExpr values.size, toExpr balanced, toExpr partitioned])
        result [``Pdqsort.chooseLayer],
      event (q.call ``Pdqsort.longLayer #[toExpr values, q.less, toExpr pred,
        toExpr limit, toExpr values.size, toExpr balanced, toExpr partitioned])
        result [``Pdqsort.longLayer]]
  return events ++ [event
    (q.call ``Pdqsort.stepLayer #[toExpr values, q.less, toExpr pred, toExpr limit,
      toExpr balanced, toExpr partitioned]) result
    [``Pdqsort.stepLayer]]

/-- Generate children before parents, so recursive proofs can reuse checked constants. -/
def nodeEvents (q : Quotation) (less : T → T → Bool) :
    Nat → Array T → Option T → Nat → Bool → Bool →
      Array T × Pdqsort.Plan × List Event
  | 0, values, pred, limit, balanced, partitioned =>
    let output := Pdqsort.heapsort values less
    let plan := Pdqsort.Plan.done
    (output, plan, [event
      (q.call ``Pdqsort.recursePlanned #[toExpr (0 : Nat), toExpr plan, toExpr values,
        q.less, toExpr pred, toExpr limit, toExpr balanced, toExpr partitioned]) (some output)])
  | fuel + 1, values, pred, limit, balanced, partitioned => Id.run do
    let layer := Pdqsort.stepLayer values less pred limit balanced partitioned
    let sizeEvent := event (mkAppN (mkConst ``Array.size [0]) #[q.type, toExpr values]) values.size
    let mut events := sizeEvent :: layerEvents q values less pred limit balanced partitioned
    let stepCall := q.call ``Pdqsort.stepLayer #[toExpr values, q.less, toExpr pred,
      toExpr limit, toExpr balanced, toExpr partitioned]
    let common := #[.inl q.type, .inl q.inhabited, .inl (toExpr fuel), .inl (toExpr values),
      .inl q.less, .inl (toExpr pred), .inl (toExpr limit), .inl (toExpr balanced),
      .inl (toExpr partitioned)]
    let childCall := fun plan (child : Pdqsort.Request T) => q.call ``Pdqsort.recursePlanned
      #[toExpr fuel, toExpr plan, toExpr child.input, q.less, toExpr child.predecessor,
        toExpr child.limit, toExpr child.wasBalanced, toExpr child.wasPartitioned]
    let (output, plan, assembly) ← match layer with
      | .done output => pure (output, .done,
          (``recursePlanned_done, common ++ #[.inl (toExpr output), .inr stepCall]))
      | .unary head child => do
        let (tail, childPlan, childEvents) := nodeEvents q less fuel
          child.input child.predecessor child.limit child.wasBalanced child.wasPartitioned
        events := events ++ childEvents
        pure (head ++ tail, .unary childPlan,
          (``recursePlanned_unary, common ++ #[.inl (toExpr head), .inl (toExpr child),
            .inl (toExpr childPlan), .inl (toExpr tail), .inr stepCall,
            .inr (childCall childPlan child)]))
      | .binary left pivot right => do
        let (leftOutput, leftPlan, leftEvents) := nodeEvents q less fuel
          left.input left.predecessor left.limit left.wasBalanced left.wasPartitioned
        let (rightOutput, rightPlan, rightEvents) := nodeEvents q less fuel
          right.input right.predecessor right.limit right.wasBalanced right.wasPartitioned
        events := events ++ leftEvents ++ rightEvents
        pure (leftOutput ++ #[pivot] ++ rightOutput, .binary leftPlan rightPlan,
          (``recursePlanned_binary, common ++ #[.inl (toExpr left), .inl (toExpr pivot),
            .inl (toExpr right), .inl (toExpr leftPlan), .inl (toExpr rightPlan),
            .inl (toExpr leftOutput), .inl (toExpr rightOutput), .inr stepCall,
            .inr (childCall leftPlan left), .inr (childCall rightPlan right)]))
    events := events ++ [{ (event
      (q.call ``Pdqsort.recursePlanned #[toExpr (fuel + 1), toExpr plan, toExpr values,
        q.less, toExpr pred, toExpr limit, toExpr balanced, toExpr partitioned]) (some output))
      with assemble := some assembly }]
    return (output, plan, events)

def certificates (q : Quotation) (values : Array T) (less : T → T → Bool) :
    Expr × Expr × List Event :=
  let (output, plan, events) := nodeEvents q less (values.size + 1)
    values none (Nat.log2 values.size + 1) true true
  (toExpr output, toExpr plan, events ++ [
    event (mkApp (mkConst ``Nat.log2) (toExpr values.size)) (Nat.log2 values.size), event
    (q.call ``Pdqsort.quicksortPlanned #[toExpr plan, toExpr values, q.less])
    (some output) [``Pdqsort.quicksortPlanned]])

/-- Store each literal array once across checkpoint statements and proof arguments. -/
private def shareArrays (e : Expr) : StateT (Std.HashMap Expr Expr) MetaM Expr :=
  Meta.transform e (pre := fun e => do
    if e.isAppOfArity ``List.toArray 2 then
      if let some shared := (← get)[e]? then
        return .done shared
      let shared ← mkAuxDefinitionFor (← mkAuxDeclName `sortData) e (compile := false)
      modify fun cache => cache.insert e shared
      return .done shared
    return .continue)

private def shareEvent (item : Event) : StateT (Std.HashMap Expr Expr) MetaM Event := do
  let lhs ← shareArrays item.lhs
  let rhs ← shareArrays item.rhs
  let assemble ← item.assemble.mapM fun (name, args) => do
    let args ← args.mapM fun arg => match arg with
      | .inl e => return .inl (← shareArrays e)
      | .inr e => return .inr (← shareArrays e)
    return (name, args)
  return {item with lhs, rhs, assemble}

private def checkEvent (item : Event)
    (cache : Std.HashMap Expr Name) : MetaM Name := do
  if let some (name, args) := item.assemble then
    let args ← args.mapM fun arg => match arg with
      | .inl e => pure e
      | .inr e => match cache[e]? with
        | some h => pure (mkConst h)
        | none => throwError "missing checkpoint {e.getAppFn}"
    return ← mkAuxLemma [] (← mkEq item.lhs item.rhs) (mkAppN (mkConst name) args)
  let mut proof ← mkEqRefl item.rhs
  if !item.unfoldNames.isEmpty then
    let lhs := item.lhs
    let mut rules ← getSimpTheorems
    let relevant := match item.lhs.getAppFn.constName! with
      | ``Pdqsort.partitionLayer => [``Pdqsort.partitionP, ``Pdqsort.partitionResultLayer]
      | ``Pdqsort.predecessorLayer => [``Pdqsort.partitionEqual, ``Pdqsort.partitionLayer]
      | ``Pdqsort.afterPivotLayer => [``Pdqsort.partialInsertionSort, ``Pdqsort.predecessorLayer]
      | ``Pdqsort.chooseLayer => [``Pdqsort.choosePivot, ``Pdqsort.afterPivotLayer]
      | ``Pdqsort.longLayer => [``Pdqsort.breakPatterns, ``Pdqsort.chooseLayer]
      | ``Pdqsort.stepLayer => [``Pdqsort.insertionSort, ``Pdqsort.heapsort, ``Pdqsort.longLayer]
      | _ => [``Pdqsort.stepLayer, ``Pdqsort.recursePlanned]
    for (cachedLhs, name) in cache.toList do
      if [``Array.size, ``Nat.log2].contains cachedLhs.getAppFn.constName! ||
          relevant.contains cachedLhs.getAppFn.constName! then
        for rule in (← mkSimpTheoremFromConst name (prio := 2000)) do
          -- Retain the checked equation, rather than asking the kernel to reduce it again.
          rules := rules.addSimpTheorem {rule with rfl := false}
    for name in item.unfoldNames do
      if (← getConstInfo name).isTheorem then
        rules ← rules.addConst name
      else
        rules ← rules.addDeclToUnfold name
    let ctx ← Simp.mkContext (config := {decide := true})
      (simpTheorems := #[rules]) (congrTheorems := ← getSimpCongrTheorems)
    let (result, _) ← Meta.simp lhs ctx #[(← Simp.getSimprocs)]
    let tailType ← mkEq result.expr item.rhs
    let tail ← mkAuxLemma [] tailType proof
    let resultType ← inferType item.rhs
    let level ← getLevel resultType
    -- Explicit endpoints avoid inferring the type of a large simplifier proof again.
    let trans := fun a b c h₁ h₂ =>
      mkAppN (mkConst ``Eq.trans [level]) #[resultType, a, b, c, h₁, h₂]
    proof ← match result.proof? with
      | none => pure (mkConst tail)
      | some h => pure (trans lhs result.expr item.rhs h (mkConst tail))
  mkAuxLemma [] (← mkEq item.lhs item.rhs) (← instantiateMVars proof)

/-- Prove the exact pdqsort result of a closed array by kernel-checking generated steps. -/
syntax (name := pdqsortCertify) "pdqsort_certify " ident term " using " term : command

@[command_elab pdqsortCertify]
unsafe def elabPdqsortCertify : Elab.Command.CommandElab := fun stx => do
  let `(pdqsort_certify $name:ident $input:term using $comparison:term) := stx
    | Elab.throwUnsupportedSyntax
  let (output, plan, items, inputExpr, compExpr) ← Elab.Command.liftTermElabM do
    let inputExpr ← Elab.Term.elabTermAndSynthesize input none
    let arrayType ← inferType inputExpr
    let_expr Array elementType := arrayType | throwError "expected an array"
    let compType ← mkArrow elementType (← mkArrow elementType (mkConst ``Bool))
    let compExpr ← Elab.Term.elabTermAndSynthesize comparison (some compType)
    let inh ← synthInstance (mkApp (mkConst ``Inhabited [1]) elementType)
    let qExpr := mkApp3 (mkConst ``Quotation.mk) (toExpr elementType) (toExpr inh) (toExpr compExpr)
    let call ← mkAppM ``certificates #[qExpr, inputExpr, compExpr]
    -- Evaluation proposes data only; checkEvent and the final addDecl check every proof.
    let (output, plan, items) ← Meta.evalExpr (Expr × Expr × List Event)
      (mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``Expr)
        (mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``Expr)
          (mkApp (mkConst ``List [0]) (mkConst ``Event)))) call
    return (output, plan, items, inputExpr, compExpr)
  let mut cache : Std.HashMap Expr Name := {}
  let mut shared : Std.HashMap Expr Expr := {}
  let mut last := Name.anonymous
  for item in items do
    let (item, updated) ← Elab.Command.liftTermElabM <| (shareEvent item).run shared
    shared := updated
    last ← Elab.Command.liftTermElabM do
      withOptions (Elab.async.set · false) <| checkEvent item cache
    cache := cache.insert item.lhs last
  Elab.Command.liftTermElabM do
    let (output, _) ← (shareArrays output).run shared
    let proof ← mkAppM ``Pdqsort.quicksortPlanned_sound
      #[plan, inputExpr, compExpr, output, mkConst last]
    let type ← inferType proof
    addDecl (.thmDecl {name := (← getCurrNamespace) ++ name.getId, levelParams := [], type, value := proof})

end Halo2.FloorPlanner.Pdqsort.Certify
