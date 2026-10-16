module

public import Clean.Utils.ResourceHistory.Replay

/-! # One shared execution for control and resources

The same row occurrence list drives control transitions, resource accesses, and
semantic events. An event may own several physical rows and arbitrarily many
accesses. Local refinement consumes established current records and proves the
independent machine step, including its machine-specific frame obligations.
-/

@[expose] public section

namespace Utils.ResourceHistory

variable {Key Record Access Row Control State Event : Type*} [DecidableEq Key]

/-- The local semantic proof boundary for an event's complete resource footprint. -/
structure EventRefinement (key : Record → Key) (edge : Access → Record × Record)
    (control : Row → Control × Control) (accesses : Row → List Access) (event : Row → Event)
    (step : State → Event → State → Prop) (valid : Row → Prop)
    (stateTruth : Control → State → Prop)
    (represents : ResourceFrontier Key Record → State → Prop) : Prop where
  localStep : ∀ row, valid row → ∀ initial final state,
    stateTruth (control row).1 state → represents initial state →
    ResourceReplay key edge initial (accesses row) final →
    ∃ next, step state (event row) next ∧ stateTruth (control row).2 next ∧ represents final next

/-- Control and resource consistency produce one trace of the independent machine.
The trace constructors are supplied by that machine; no second semantic model is introduced. -/
theorem ground (key : Record → Key) (edge : Access → Record × Record)
    (control : Row → Control × Control) (accesses : Row → List Access) (event : Row → Event)
    (step : State → Event → State → Prop) (valid : Row → Prop)
    (stateTruth : Control → State → Prop)
    (represents : ResourceFrontier Key Record → State → Prop)
    (refinement : EventRefinement key edge control accesses event step valid stateTruth represents)
    (trace : State → List Event → State → Prop)
    (nil : ∀ state, trace state [] state)
    (cons : ∀ state next final e events, step state e next → trace next events final →
      trace state (e :: events) final)
    (rows : List Row) (incoming outgoing : Control)
    (initial final : ResourceFrontier Key Record) (state : State)
    (walk : Walk.IsWalk control incoming outgoing rows)
    (replay : ResourceReplay key edge initial (rows.flatMap accesses) final)
    (localFacts : ∀ row ∈ rows, valid row)
    (initialControl : stateTruth incoming state) (initialResources : represents initial state) :
    ∃ result, trace state (rows.map event) result ∧
      stateTruth outgoing result ∧ represents final result := by
  induction rows generalizing incoming initial state with
  | nil =>
    change initial = final at replay
    change incoming = outgoing at walk
    exact ⟨state, nil state, walk ▸ initialControl, replay ▸ initialResources⟩
  | cons row rest ih =>
    obtain ⟨source, tail⟩ := walk
    obtain ⟨middle, firstPart, suffix⟩ :=
      (ResourceReplay.append_iff key edge (accesses row) (rest.flatMap accesses) initial final).mp replay
    obtain ⟨next, nextStep, nextControl, nextResources⟩ := refinement.localStep row
      (localFacts row (List.mem_cons_self ..)) initial middle state
      (by rw [source]; exact initialControl) initialResources firstPart
    obtain ⟨result, traceRest, resultControl, resultResources⟩ := ih _ middle next tail suffix
      (fun r member => localFacts r (List.mem_cons_of_mem _ member)) nextControl nextResources
    exact ⟨result, cons state next result (event row) (rest.map event) nextStep traceRest,
      resultControl, resultResources⟩

end Utils.ResourceHistory
