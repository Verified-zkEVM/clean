import Clean.Ironwood.Action.PlannerTrace.Chunk12

namespace Zcash.Circuits.Action

open Halo2 FloorPlanner

/-- The compact literal trace satisfies every least-fit planner transition. -/
theorem actionExactPlannerTrace_traceLawfulAfter :
    V1.PlannedSummaryBlock.TraceLawfulAfter [] actionExactPlannerTrace := by
  apply V1.PlannedSummaryBlock.traceLawfulAfter_of_steps
  intro index hindex
  have hlength : actionExactPlannerTrace.length = 156 := by rfl
  rw [hlength] at hindex
  have hstep : V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take index)
      ((actionExactPlannerTrace.drop index).take 1) := by
    by_cases h0 : index < 12
    · exact actionExactPlannerStepsChunk00 index (by omega) h0
    · by_cases h1 : index < 24
      · exact actionExactPlannerStepsChunk01 index (by omega) h1
      · by_cases h2 : index < 36
        · exact actionExactPlannerStepsChunk02 index (by omega) h2
        · by_cases h3 : index < 48
          · exact actionExactPlannerStepsChunk03 index (by omega) h3
          · by_cases h4 : index < 60
            · exact actionExactPlannerStepsChunk04 index (by omega) h4
            · by_cases h5 : index < 72
              · exact actionExactPlannerStepsChunk05 index (by omega) h5
              · by_cases h6 : index < 84
                · exact actionExactPlannerStepsChunk06 index (by omega) h6
                · by_cases h7 : index < 96
                  · exact actionExactPlannerStepsChunk07 index (by omega) h7
                  · by_cases h8 : index < 108
                    · exact actionExactPlannerStepsChunk08 index (by omega) h8
                    · by_cases h9 : index < 120
                      · exact actionExactPlannerStepsChunk09 index (by omega) h9
                      · by_cases h10 : index < 132
                        · exact actionExactPlannerStepsChunk10 index (by omega) h10
                        · by_cases h11 : index < 144
                          · exact actionExactPlannerStepsChunk11 index (by omega) h11
                          · by_cases h12 : index < 156
                            · exact actionExactPlannerStepsChunk12 index (by omega) h12
                            · omega
  rw [List.take_one_drop_eq_of_lt_length hindex] at hstep
  exact hstep

theorem actionExactPlannerTrace_lawful :
    V1.PlannedSummaryBlock.Lawful V1.AllocationView.empty
      actionExactPlannerTrace := by
  exact V1.PlannedSummaryBlock.lawful_of_traceLawfulAfter []
    actionExactPlannerTrace (by simp)
      actionExactPlannerTrace_traceLawfulAfter

macro "action_tie_planner_trace" : tactic =>
  `(tactic|
    (apply V1.PlannedSummaryBlock.traceLawfulAfter_of_steps_after
     intro index hindex
     simp only [actionKey8PlannerTrace, actionKey4PlannerTrace,
       V1.PlannedSummaryBlock.run, List.length_append,
       List.length_cons, List.length_nil] at hindex
     norm_num at hindex
     interval_cases index <;>
       (try norm_num [actionKey8PlannerTrace, actionKey4PlannerTrace,
         V1.PlannedSummaryBlock.run] at *) <;>
       action_exact_planner_step))

set_option maxRecDepth 10000 in
private theorem actionKey8PlannerTrace0 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 52) (actionKey8PlannerTrace 0) := by
  action_tie_planner_trace

set_option maxRecDepth 10000 in
private theorem actionKey8PlannerTrace1 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 52) (actionKey8PlannerTrace 1) := by
  action_tie_planner_trace

set_option maxRecDepth 10000 in
private theorem actionKey8PlannerTrace2 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 52) (actionKey8PlannerTrace 2) := by
  action_tie_planner_trace

set_option maxRecDepth 10000 in
private theorem actionKey8PlannerTrace3 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 52) (actionKey8PlannerTrace 3) := by
  action_tie_planner_trace

set_option maxRecDepth 10000 in
private theorem actionKey8PlannerTrace4 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 52) (actionKey8PlannerTrace 4) := by
  action_tie_planner_trace

set_option maxRecDepth 10000 in
private theorem actionKey8PlannerTrace5 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 52) (actionKey8PlannerTrace 5) := by
  action_tie_planner_trace

set_option maxRecDepth 10000 in
private theorem actionKey8PlannerTrace6 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 52) (actionKey8PlannerTrace 6) := by
  action_tie_planner_trace

set_option maxRecDepth 10000 in
private theorem actionKey8PlannerTrace7 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 52) (actionKey8PlannerTrace 7) := by
  action_tie_planner_trace

set_option maxRecDepth 10000 in
private theorem actionKey8PlannerTrace8 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 52) (actionKey8PlannerTrace 8) := by
  action_tie_planner_trace

/-- Every key-eight tie order produces a lawful continuation of the common
higher-key prefix. -/
theorem actionKey8PlannerTrace_traceLawfulAfter
    (before : Nat) (hbefore : before ≤ 8) :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 52) (actionKey8PlannerTrace before) := by
  interval_cases before
  · exact actionKey8PlannerTrace0
  · exact actionKey8PlannerTrace1
  · exact actionKey8PlannerTrace2
  · exact actionKey8PlannerTrace3
  · exact actionKey8PlannerTrace4
  · exact actionKey8PlannerTrace5
  · exact actionKey8PlannerTrace6
  · exact actionKey8PlannerTrace7
  · exact actionKey8PlannerTrace8

theorem actionKey8PlannerTrace_lawful
    (before : Nat) (hBefore : before ≤ 8) :
    V1.PlannedSummaryBlock.Lawful
      (V1.PlannedSummaryBlock.finalView V1.AllocationView.empty
        actionAbove8PlannerTrace)
      (actionKey8PlannerTrace before) := by
  simpa only [actionAbove8PlannerTrace] using
    V1.PlannedSummaryBlock.lawful_of_traceLawfulAfter
      (actionExactPlannerTrace.take 52) (actionKey8PlannerTrace before)
        (V1.PlannedSummaryBlock.Lawful.counts
          (V1.PlannedSummaryBlock.Lawful.take
            actionExactPlannerTrace_lawful 52))
        (actionKey8PlannerTrace_traceLawfulAfter before hBefore)

set_option maxRecDepth 10000 in
private theorem actionKey4PlannerTrace0 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 79) (actionKey4PlannerTrace 0) := by
  action_tie_planner_trace

set_option maxRecDepth 10000 in
private theorem actionKey4PlannerTrace1 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 79) (actionKey4PlannerTrace 1) := by
  action_tie_planner_trace

set_option maxRecDepth 10000 in
private theorem actionKey4PlannerTrace2 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 79) (actionKey4PlannerTrace 2) := by
  action_tie_planner_trace

set_option maxRecDepth 10000 in
private theorem actionKey4PlannerTrace3 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 79) (actionKey4PlannerTrace 3) := by
  action_tie_planner_trace

set_option maxRecDepth 10000 in
private theorem actionKey4PlannerTrace4 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 79) (actionKey4PlannerTrace 4) := by
  action_tie_planner_trace

set_option maxRecDepth 10000 in
private theorem actionKey4PlannerTrace5 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 79) (actionKey4PlannerTrace 5) := by
  action_tie_planner_trace

/-- Every key-four tie order produces a lawful continuation of the common
higher-key prefix. -/
theorem actionKey4PlannerTrace_traceLawfulAfter
    (order : Nat) (horder : order ≤ 5) :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 79) (actionKey4PlannerTrace order) := by
  interval_cases order
  · exact actionKey4PlannerTrace0
  · exact actionKey4PlannerTrace1
  · exact actionKey4PlannerTrace2
  · exact actionKey4PlannerTrace3
  · exact actionKey4PlannerTrace4
  · exact actionKey4PlannerTrace5

theorem actionKey4PlannerTrace_lawful
    (order : Nat) (hOrder : order ≤ 5) :
    V1.PlannedSummaryBlock.Lawful
      (V1.PlannedSummaryBlock.finalView V1.AllocationView.empty
        (actionExactPlannerTrace.take 79))
      (actionKey4PlannerTrace order) := by
  exact V1.PlannedSummaryBlock.lawful_of_traceLawfulAfter
    (actionExactPlannerTrace.take 79) (actionKey4PlannerTrace order)
      (V1.PlannedSummaryBlock.Lawful.counts
        (V1.PlannedSummaryBlock.Lawful.take
          actionExactPlannerTrace_lawful 79))
      (actionKey4PlannerTrace_traceLawfulAfter order hOrder)

theorem actionCanonicalPlannerTrace_take78_finalView :
    V1.PlannedSummaryBlock.finalView V1.AllocationView.empty
        (actionCanonicalPlannerTrace.take 78) =
      V1.PlannedSummaryBlock.finalView V1.AllocationView.empty
        (actionExactPlannerTrace.take 79) := by
  have hPrefix :
      V1.PlannedSummaryBlock.finalView V1.AllocationView.empty
          (actionAbove8PlannerTrace ++ actionKey8PlannerTrace 8) =
        V1.PlannedSummaryBlock.finalView V1.AllocationView.empty
          (actionExactPlannerTrace.take 55) := by
    rw [V1.PlannedSummaryBlock.finalView_append,
      actionExactPlannerTrace_take55_eq,
      V1.PlannedSummaryBlock.finalView_append,
      actionKey8PlannerTrace_finalView _ 8 (by norm_num),
      actionKey8PlannerTrace_finalView _ 1 (by norm_num)]
  calc
    _ = V1.PlannedSummaryBlock.finalView
        (V1.PlannedSummaryBlock.finalView V1.AllocationView.empty
          (actionAbove8PlannerTrace ++ actionKey8PlannerTrace 8))
        actionBetween8And4PlannerTrace := by
      rw [show actionCanonicalPlannerTrace.take 78 =
        (actionAbove8PlannerTrace ++ actionKey8PlannerTrace 8) ++
          actionBetween8And4PlannerTrace by rfl,
        V1.PlannedSummaryBlock.finalView_append]
    _ = V1.PlannedSummaryBlock.finalView
        (V1.PlannedSummaryBlock.finalView V1.AllocationView.empty
          (actionExactPlannerTrace.take 55))
        actionBetween8And4PlannerTrace := congrArg
          (fun view => V1.PlannedSummaryBlock.finalView view
            actionBetween8And4PlannerTrace) hPrefix
    _ = V1.PlannedSummaryBlock.finalView V1.AllocationView.empty
        (actionExactPlannerTrace.take 55 ++
          actionBetween8And4PlannerTrace) :=
      (V1.PlannedSummaryBlock.finalView_append _ _ _).symm
    _ = _ := congrArg
      (V1.PlannedSummaryBlock.finalView V1.AllocationView.empty)
        actionExactPlannerTrace_take79_eq.symm

theorem actionCanonicalPlannerTrace_take78_summaries :
    V1.PlannedSummaryBlock.summaries
        (actionCanonicalPlannerTrace.take 78) =
      V1.PlannedSummaryBlock.summaries actionAbove8PlannerTrace ++
        plannerKey8 actionCanonicalPlannerSummaries ++
          V1.PlannedSummaryBlock.summaries
            actionBetween8And4PlannerTrace := by
  rw [show actionCanonicalPlannerTrace.take 78 =
      (actionAbove8PlannerTrace ++ actionKey8PlannerTrace 8) ++
        actionBetween8And4PlannerTrace by rfl,
    V1.PlannedSummaryBlock.summaries_append,
    V1.PlannedSummaryBlock.summaries_append,
    actionKey8PlannerTrace8_summaries]

theorem actionKey4PlannerTrace_lawful_after_canonicalPrefix
    (order : Nat) (hOrder : order ≤ 5) :
    V1.PlannedSummaryBlock.Lawful
      (V1.PlannedSummaryBlock.finalView V1.AllocationView.empty
        (actionCanonicalPlannerTrace.take 78))
      (actionKey4PlannerTrace order) := by
  rw [actionCanonicalPlannerTrace_take78_finalView]
  exact actionKey4PlannerTrace_lawful order hOrder

/-- The compact canonical-order trace is lawful. Equal-key reorderings are
connected to the actual planner trace solely through their identical final
allocation views. -/
theorem actionCanonicalPlannerTrace_lawful :
    V1.PlannedSummaryBlock.Lawful V1.AllocationView.empty
      actionCanonicalPlannerTrace := by
  have hAbove := V1.PlannedSummaryBlock.Lawful.take
    actionExactPlannerTrace_lawful 52
  have hKey8 := actionKey8PlannerTrace_lawful 8 (by norm_num)
  have hMiddleExact := V1.PlannedSummaryBlock.Lawful.take
    (V1.PlannedSummaryBlock.Lawful.drop
      actionExactPlannerTrace_lawful 55) 24
  have hKey4 := actionKey4PlannerTrace_lawful 0 (by norm_num)
  have hBelowExact := V1.PlannedSummaryBlock.Lawful.drop
    actionExactPlannerTrace_lawful 81
  have hView55 :
      V1.PlannedSummaryBlock.finalView V1.AllocationView.empty
          (actionAbove8PlannerTrace ++ actionKey8PlannerTrace 8) =
        V1.PlannedSummaryBlock.finalView V1.AllocationView.empty
          (actionExactPlannerTrace.take 55) := by
    rw [V1.PlannedSummaryBlock.finalView_append,
      actionExactPlannerTrace_take55_eq,
      V1.PlannedSummaryBlock.finalView_append,
      actionKey8PlannerTrace_finalView _ 8 (by norm_num),
      actionKey8PlannerTrace_finalView _ 1 (by norm_num)]
  have hView79 :
      V1.PlannedSummaryBlock.finalView V1.AllocationView.empty
          ((actionAbove8PlannerTrace ++ actionKey8PlannerTrace 8) ++
            actionBetween8And4PlannerTrace) =
        V1.PlannedSummaryBlock.finalView V1.AllocationView.empty
          (actionExactPlannerTrace.take 79) := by
    rw [V1.PlannedSummaryBlock.finalView_append, hView55,
      actionExactPlannerTrace_take79_eq,
      V1.PlannedSummaryBlock.finalView_append]
  have hView81 :
      V1.PlannedSummaryBlock.finalView V1.AllocationView.empty
          (((actionAbove8PlannerTrace ++ actionKey8PlannerTrace 8) ++
              actionBetween8And4PlannerTrace) ++
            actionKey4PlannerTrace 0) =
        V1.PlannedSummaryBlock.finalView V1.AllocationView.empty
          (actionExactPlannerTrace.take 81) := by
    rw [V1.PlannedSummaryBlock.finalView_append, hView79,
      actionExactPlannerTrace_take81_eq,
      V1.PlannedSummaryBlock.finalView_append,
      actionExactPlannerTrace_drop79_take2_finalView]
  rw [actionCanonicalPlannerTrace,
    V1.PlannedSummaryBlock.lawful_append]
  constructor
  · rw [V1.PlannedSummaryBlock.lawful_append]
    constructor
    · rw [V1.PlannedSummaryBlock.lawful_append]
      constructor
      · rw [V1.PlannedSummaryBlock.lawful_append]
        exact ⟨hAbove, hKey8⟩
      · rw [hView55]
        exact hMiddleExact
    · rw [hView79]
      exact hKey4
  · rw [hView81]
    exact hBelowExact

/-- The canonical reduced Action summary has the same planner state as its
compact placement trace. -/
theorem actionCanonicalPlannerSummaries_equivalent_trace :
    V1.SummaryStateEquivalent
      (V1.slotSummaryStateFromWith 0 actionCanonicalPlannerSummaries
        (∅ : CircuitAllocations))
      (V1.slotSummaryStateFromWith 0
        (V1.PlannedSummaryBlock.summaries actionCanonicalPlannerTrace ++
          List.replicate 2 ({ columns := [], rowCount := 0 } :
            RegionShapeSummary))
        (∅ : CircuitAllocations)) := by
  let above := plannerAbove8 actionCanonicalPlannerSummaries
  let key8 := plannerKey8 actionCanonicalPlannerSummaries
  let middle := plannerBetween8And4 actionCanonicalPlannerSummaries
  let key4 := plannerKey4 actionCanonicalPlannerSummaries
  let below := plannerBelow4 actionCanonicalPlannerSummaries
  let traceAbove := V1.PlannedSummaryBlock.summaries actionAbove8PlannerTrace
  let traceMiddle :=
    V1.PlannedSummaryBlock.summaries actionBetween8And4PlannerTrace
  let traceBelow := actionBelow4PlannerSummaries
  let canonicalAbove :=
    V1.slotSummaryStateFromWith 0 above (∅ : CircuitAllocations)
  let referenceAbove :=
    V1.slotSummaryStateFromWith 0 traceAbove (∅ : CircuitAllocations)
  have hEmptyValid : (∅ : CircuitAllocations).Valid := by
    intro column
    simp [Allocations.Valid]
  have hAbove : V1.SummaryStateEquivalent canonicalAbove referenceAbove :=
    actionAbove8PlannerTrace_equivalent 0 (∅ : CircuitAllocations)
      hEmptyValid
  have hAboveWell : traceAbove.Forall RegionShapeSummary.WellFormed :=
    V1.PlannedSummaryBlock.Lawful.summaries_wellFormed
      (V1.PlannedSummaryBlock.Lawful.take
        actionExactPlannerTrace_lawful 52)
  have hReferenceAboveValid : referenceAbove.2.Valid :=
    V1.slotSummaryStateFromWith_valid 0 traceAbove
      (∅ : CircuitAllocations) hAboveWell hEmptyValid
  let canonical8 :=
    V1.slotSummaryStateFromWith canonicalAbove.1 key8 canonicalAbove.2
  let reference8 :=
    V1.slotSummaryStateFromWith referenceAbove.1 key8 referenceAbove.2
  have hKey8Well : key8.Forall RegionShapeSummary.WellFormed :=
    canonicalFiltered_wellFormed _
  have hKey8 : V1.SummaryStateEquivalent canonical8 reference8 :=
    V1.continueCanonicalSegment key8 hKey8Well hReferenceAboveValid hAbove
  have hReference8Valid : reference8.2.Valid :=
    V1.slotSummaryStateFromWith_valid referenceAbove.1 key8
      referenceAbove.2 hKey8Well hReferenceAboveValid
  let canonicalMiddle :=
    V1.slotSummaryStateFromWith canonical8.1 middle canonical8.2
  let referenceCanonicalMiddle :=
    V1.slotSummaryStateFromWith reference8.1 middle reference8.2
  let referenceMiddle :=
    V1.slotSummaryStateFromWith reference8.1 traceMiddle reference8.2
  have hMiddleWell : middle.Forall RegionShapeSummary.WellFormed :=
    canonicalFiltered_wellFormed _
  have hMiddleContinued :
      V1.SummaryStateEquivalent canonicalMiddle referenceCanonicalMiddle :=
    V1.continueCanonicalSegment middle hMiddleWell hReference8Valid hKey8
  have hMiddleReplaced :
      V1.SummaryStateEquivalent referenceCanonicalMiddle referenceMiddle :=
    actionBetween8And4PlannerTrace_equivalent reference8.1 reference8.2
      hReference8Valid
  have hMiddle :
      V1.SummaryStateEquivalent canonicalMiddle referenceMiddle :=
    hMiddleContinued.trans hMiddleReplaced
  have hTraceMiddleWell : traceMiddle.Forall RegionShapeSummary.WellFormed :=
    V1.PlannedSummaryBlock.Lawful.summaries_wellFormed
      (V1.PlannedSummaryBlock.Lawful.take
        (V1.PlannedSummaryBlock.Lawful.drop
          actionExactPlannerTrace_lawful 55) 24)
  have hReferenceMiddleValid : referenceMiddle.2.Valid :=
    V1.slotSummaryStateFromWith_valid reference8.1 traceMiddle
      reference8.2 hTraceMiddleWell hReference8Valid
  let canonical4 :=
    V1.slotSummaryStateFromWith canonicalMiddle.1 key4 canonicalMiddle.2
  let reference4 :=
    V1.slotSummaryStateFromWith referenceMiddle.1 key4 referenceMiddle.2
  have hKey4Well : key4.Forall RegionShapeSummary.WellFormed :=
    canonicalFiltered_wellFormed _
  have hKey4 : V1.SummaryStateEquivalent canonical4 reference4 :=
    V1.continueCanonicalSegment key4 hKey4Well hReferenceMiddleValid hMiddle
  have hReference4Valid : reference4.2.Valid :=
    V1.slotSummaryStateFromWith_valid referenceMiddle.1 key4
      referenceMiddle.2 hKey4Well hReferenceMiddleValid
  let canonicalBelow :=
    V1.slotSummaryStateFromWith canonical4.1 below canonical4.2
  let referenceCanonicalBelow :=
    V1.slotSummaryStateFromWith reference4.1 below reference4.2
  let referenceBelow :=
    V1.slotSummaryStateFromWith reference4.1 traceBelow reference4.2
  have hBelowWell : below.Forall RegionShapeSummary.WellFormed :=
    canonicalFiltered_wellFormed _
  have hBelowContinued :
      V1.SummaryStateEquivalent canonicalBelow referenceCanonicalBelow :=
    V1.continueCanonicalSegment below hBelowWell hReference4Valid hKey4
  have hBelowReplaced :
      V1.SummaryStateEquivalent referenceCanonicalBelow referenceBelow :=
    actionBelow4PlannerTrace_equivalent reference4.1 reference4.2
      hReference4Valid
  have hBelow : V1.SummaryStateEquivalent canonicalBelow referenceBelow :=
    hBelowContinued.trans hBelowReplaced
  rw [plannerSegments_eq actionCanonicalPlannerSummaries
    actionCanonicalPlannerSummaries_key_sorted]
  simp only [V1.slotSummaryStateFromWith_append]
  simpa only [above, key8, middle, key4, below, traceAbove, traceMiddle,
    traceBelow, canonicalAbove, referenceAbove, canonical8, reference8,
    canonicalMiddle, referenceCanonicalMiddle, referenceMiddle, canonical4,
    reference4, canonicalBelow, referenceCanonicalBelow, referenceBelow,
    actionCanonicalPlannerTrace, V1.PlannedSummaryBlock.summaries_append,
    actionKey8PlannerTrace8_summaries,
    actionKey4PlannerTrace0_summaries, actionBelow4PlannerSummaries,
    V1.slotSummaryStateFromWith_append] using hBelow

/-- The compact canonical placement trace reaches the Action endpoint. -/
theorem actionCanonicalPlannerTrace_endpoint :
    V1.PlannedSummaryBlock.endpointFrom 0 actionCanonicalPlannerTrace =
      1779 := by
  rw [V1.PlannedSummaryBlock.endpointFrom_eq_foldl_max]
  unfold actionCanonicalPlannerTrace actionAbove8PlannerTrace
    actionBetween8And4PlannerTrace actionBelow4PlannerTrace
    actionKey8PlannerTrace actionKey4PlannerTrace
    actionExactPlannerTrace actionPlannerBlocks planner8Wide planner8Short
    planner4Narrow planner4Wide plannerShape
  decide +kernel

/-- The canonical reduced Action summary reaches row 1779. -/
theorem actionCanonicalPlannerSummaries_endpoint :
    (V1.slotSummaryStateFromWith 0 actionCanonicalPlannerSummaries
      (∅ : CircuitAllocations)).1 = 1779 := by
  rw [actionCanonicalPlannerSummaries_equivalent_trace.1]
  rw [V1.slotSummaryStateFromWith_append]
  have hTrace := V1.PlannedSummaryBlock.slotSummaryStateFromWith_summaries_result
    actionCanonicalPlannerTrace 0 (∅ : CircuitAllocations)
      V1.AllocationView.empty V1.AllocationView.empty_represents_empty
      V1.AllocationView.empty_valid actionCanonicalPlannerTrace_lawful
  simp only [V1.slotSummaryStateFromWith_replicate_empty]
  rw [hTrace.1, actionCanonicalPlannerTrace_endpoint]

/-- The consensus-sorted and canonical reduced Action summaries produce the
same planner endpoint and allocation state. -/
theorem actionSortedPlannerSummaries_equivalent_canonical :
    V1.SummaryStateEquivalent
      (V1.slotSummaryStateFromWith 0 actionSortedPlannerSummaries
        (∅ : CircuitAllocations))
      (V1.slotSummaryStateFromWith 0 actionCanonicalPlannerSummaries
        (∅ : CircuitAllocations)) := by
  let sortedAbove := plannerAbove8 actionSortedPlannerSummaries
  let canonicalAbove := plannerAbove8 actionCanonicalPlannerSummaries
  let sorted8 := plannerKey8 actionSortedPlannerSummaries
  let canonical8 := plannerKey8 actionCanonicalPlannerSummaries
  let sortedMiddle := plannerBetween8And4 actionSortedPlannerSummaries
  let canonicalMiddle := plannerBetween8And4 actionCanonicalPlannerSummaries
  let sorted4 := plannerKey4 actionSortedPlannerSummaries
  let canonical4 := plannerKey4 actionCanonicalPlannerSummaries
  let sortedBelow := plannerBelow4 actionSortedPlannerSummaries
  let canonicalBelow := plannerBelow4 actionCanonicalPlannerSummaries
  let referenceAboveSummaries :=
    V1.PlannedSummaryBlock.summaries actionAbove8PlannerTrace
  let sAbove :=
    V1.slotSummaryStateFromWith 0 sortedAbove (∅ : CircuitAllocations)
  let cAbove :=
    V1.slotSummaryStateFromWith 0 canonicalAbove (∅ : CircuitAllocations)
  let rAbove := V1.slotSummaryStateFromWith 0 referenceAboveSummaries
    (∅ : CircuitAllocations)
  have hEmptyValid : (∅ : CircuitAllocations).Valid := by
    intro column
    simp [Allocations.Valid]
  have hSCAbove : V1.SummaryStateEquivalent sAbove cAbove :=
    plannerAbove8_equivalent 0 (∅ : CircuitAllocations) hEmptyValid
  have hCRAbove : V1.SummaryStateEquivalent cAbove rAbove :=
    actionAbove8PlannerTrace_equivalent 0 (∅ : CircuitAllocations)
      hEmptyValid
  let viewAbove := V1.PlannedSummaryBlock.finalView
    V1.AllocationView.empty (actionExactPlannerTrace.take 52)
  have hAboveLawful := V1.PlannedSummaryBlock.Lawful.take
    actionExactPlannerTrace_lawful 52
  have hViewAboveValid : viewAbove.Valid :=
    V1.PlannedSummaryBlock.Lawful.finalView_valid hAboveLawful
      V1.AllocationView.empty_valid
  have hRAboveRepresents : viewAbove.Represents rAbove.2 := by
    have hResult :=
      V1.PlannedSummaryBlock.slotSummaryStateFromWith_summaries_result
        (actionExactPlannerTrace.take 52) 0 (∅ : CircuitAllocations)
        V1.AllocationView.empty V1.AllocationView.empty_represents_empty
        V1.AllocationView.empty_valid hAboveLawful
    simpa only [viewAbove, rAbove, referenceAboveSummaries,
      actionAbove8PlannerTrace] using hResult.2
  have hCAboveRepresents : viewAbove.Represents cAbove.2 :=
    V1.AllocationView.Represents.of_equivalent hRAboveRepresents hCRAbove.2
  have hSAboveRepresents : viewAbove.Represents sAbove.2 :=
    V1.AllocationView.Represents.of_equivalent hCAboveRepresents hSCAbove.2
  let s8 := V1.slotSummaryStateFromWith sAbove.1 sorted8 sAbove.2
  let c8 := V1.slotSummaryStateFromWith cAbove.1 canonical8 cAbove.2
  obtain ⟨before8, hBefore8, hSorted8⟩ := actionSortedKey8_exists_trace
  have hSpecial8 :=
    V1.PlannedSummaryBlock.slotSummaryStateFromWith_equivalent_of_traces_of_represents
      sorted8 (actionKey8PlannerTrace before8) (actionKey8PlannerTrace 8)
      hSorted8 sAbove.1 cAbove.1 sAbove.2 cAbove.2 viewAbove
      hSAboveRepresents hCAboveRepresents hViewAboveValid
      (by simpa only [viewAbove, actionAbove8PlannerTrace] using
        actionKey8PlannerTrace_lawful before8 hBefore8)
      (by simpa only [viewAbove, actionAbove8PlannerTrace] using
        actionKey8PlannerTrace_lawful 8 (by norm_num))
      (by rw [actionKey8PlannerTrace_endpointFrom _ before8 hBefore8,
          actionKey8PlannerTrace_endpointFrom _ 8 (by norm_num),
          hSCAbove.1])
      (actionKey8PlannerTrace_finalView viewAbove before8 hBefore8 |>.trans
        (actionKey8PlannerTrace_finalView viewAbove 8 (by norm_num)).symm)
  have hSC8 : V1.SummaryStateEquivalent s8 c8 := by
    simpa only [s8, c8, sorted8, canonical8,
      actionKey8PlannerTrace8_summaries] using hSpecial8
  have hC8Valid : c8.2.Valid := by
    exact (V1.AllocationView.Represents.valid hCAboveRepresents
      hViewAboveValid) |>
      V1.slotSummaryStateFromWith_valid cAbove.1 canonical8 cAbove.2
        (canonicalFiltered_wellFormed _)
  have hS8Valid : s8.2.Valid :=
    V1.allocationsValid_of_summaryStateEquivalent hSC8 hC8Valid
  let sMiddle :=
    V1.slotSummaryStateFromWith s8.1 sortedMiddle s8.2
  let cMiddle :=
    V1.slotSummaryStateFromWith c8.1 canonicalMiddle c8.2
  let sCanonicalMiddle :=
    V1.slotSummaryStateFromWith s8.1 canonicalMiddle s8.2
  have hMiddleAtS : V1.SummaryStateEquivalent sMiddle sCanonicalMiddle :=
    plannerBetween8And4_equivalent s8.1 s8.2 hS8Valid
  have hMiddleContinued :
      V1.SummaryStateEquivalent sCanonicalMiddle cMiddle :=
    V1.continueCanonicalSegment canonicalMiddle
      (canonicalFiltered_wellFormed _) hC8Valid hSC8
  have hSCMiddle : V1.SummaryStateEquivalent sMiddle cMiddle :=
    hMiddleAtS.trans hMiddleContinued
  have hCMiddleValid : cMiddle.2.Valid :=
    V1.slotSummaryStateFromWith_valid c8.1 canonicalMiddle c8.2
      (canonicalFiltered_wellFormed _) hC8Valid
  let r8 := V1.slotSummaryStateFromWith rAbove.1 canonical8 rAbove.2
  have hRAboveValid : rAbove.2.Valid :=
    V1.AllocationView.Represents.valid hRAboveRepresents hViewAboveValid
  have hCR8 : V1.SummaryStateEquivalent c8 r8 :=
    V1.continueCanonicalSegment canonical8
      (canonicalFiltered_wellFormed _) hRAboveValid hCRAbove
  have hR8Valid : r8.2.Valid :=
    V1.slotSummaryStateFromWith_valid rAbove.1 canonical8 rAbove.2
      (canonicalFiltered_wellFormed _) hRAboveValid
  let rCanonicalMiddle :=
    V1.slotSummaryStateFromWith r8.1 canonicalMiddle r8.2
  let rMiddle := V1.slotSummaryStateFromWith r8.1
    (V1.PlannedSummaryBlock.summaries actionBetween8And4PlannerTrace) r8.2
  have hCRCanonicalMiddle :
      V1.SummaryStateEquivalent cMiddle rCanonicalMiddle :=
    V1.continueCanonicalSegment canonicalMiddle
      (canonicalFiltered_wellFormed _) hR8Valid hCR8
  have hRMiddleReplace :
      V1.SummaryStateEquivalent rCanonicalMiddle rMiddle :=
    actionBetween8And4PlannerTrace_equivalent r8.1 r8.2 hR8Valid
  have hCRMiddle : V1.SummaryStateEquivalent cMiddle rMiddle :=
    hCRCanonicalMiddle.trans hRMiddleReplace
  let viewBefore4 := V1.PlannedSummaryBlock.finalView
    V1.AllocationView.empty (actionCanonicalPlannerTrace.take 78)
  have hPrefix78Lawful := V1.PlannedSummaryBlock.Lawful.take
    actionCanonicalPlannerTrace_lawful 78
  have hViewBefore4Valid : viewBefore4.Valid :=
    V1.PlannedSummaryBlock.Lawful.finalView_valid hPrefix78Lawful
      V1.AllocationView.empty_valid
  have hRMiddleRepresents : viewBefore4.Represents rMiddle.2 := by
    have hResult :=
      V1.PlannedSummaryBlock.slotSummaryStateFromWith_summaries_result
        (actionCanonicalPlannerTrace.take 78) 0
        (∅ : CircuitAllocations) V1.AllocationView.empty
        V1.AllocationView.empty_represents_empty V1.AllocationView.empty_valid
        hPrefix78Lawful
    rw [actionCanonicalPlannerTrace_take78_summaries] at hResult
    simpa only [viewBefore4, rMiddle, r8, rAbove,
      referenceAboveSummaries, canonical8,
      V1.slotSummaryStateFromWith_append] using hResult.2
  have hCMiddleRepresents : viewBefore4.Represents cMiddle.2 :=
    V1.AllocationView.Represents.of_equivalent hRMiddleRepresents hCRMiddle.2
  have hSMiddleRepresents : viewBefore4.Represents sMiddle.2 :=
    V1.AllocationView.Represents.of_equivalent hCMiddleRepresents hSCMiddle.2
  let s4 := V1.slotSummaryStateFromWith sMiddle.1 sorted4 sMiddle.2
  let c4 := V1.slotSummaryStateFromWith cMiddle.1 canonical4 cMiddle.2
  obtain ⟨order4, hOrder4, hSorted4⟩ := actionSortedKey4_exists_trace
  have hSpecial4 :=
    V1.PlannedSummaryBlock.slotSummaryStateFromWith_equivalent_of_traces_of_represents
      sorted4 (actionKey4PlannerTrace order4) (actionKey4PlannerTrace 0)
      hSorted4 sMiddle.1 cMiddle.1 sMiddle.2 cMiddle.2 viewBefore4
      hSMiddleRepresents hCMiddleRepresents hViewBefore4Valid
      (actionKey4PlannerTrace_lawful_after_canonicalPrefix order4 hOrder4)
      (actionKey4PlannerTrace_lawful_after_canonicalPrefix 0 (by norm_num))
      (by rw [actionKey4PlannerTrace_endpointFrom _ order4 hOrder4,
          actionKey4PlannerTrace_endpointFrom _ 0 (by norm_num),
          hSCMiddle.1])
      (actionKey4PlannerTrace_finalView viewBefore4 order4 hOrder4)
  have hSC4 : V1.SummaryStateEquivalent s4 c4 := by
    simpa only [s4, c4, sorted4, canonical4,
      actionKey4PlannerTrace0_summaries] using hSpecial4
  have hC4Valid : c4.2.Valid :=
    V1.slotSummaryStateFromWith_valid cMiddle.1 canonical4 cMiddle.2
      (canonicalFiltered_wellFormed _) hCMiddleValid
  have hS4Valid : s4.2.Valid :=
    V1.allocationsValid_of_summaryStateEquivalent hSC4 hC4Valid
  let sBelow := V1.slotSummaryStateFromWith s4.1 sortedBelow s4.2
  let cBelow := V1.slotSummaryStateFromWith c4.1 canonicalBelow c4.2
  let sCanonicalBelow :=
    V1.slotSummaryStateFromWith s4.1 canonicalBelow s4.2
  have hBelowAtS : V1.SummaryStateEquivalent sBelow sCanonicalBelow :=
    plannerBelow4_equivalent s4.1 s4.2 hS4Valid
  have hBelowContinued :
      V1.SummaryStateEquivalent sCanonicalBelow cBelow :=
    V1.continueCanonicalSegment canonicalBelow
      (canonicalFiltered_wellFormed _) hC4Valid hSC4
  have hSCBelow : V1.SummaryStateEquivalent sBelow cBelow :=
    hBelowAtS.trans hBelowContinued
  rw [plannerSegments_eq actionSortedPlannerSummaries
      actionSortedPlannerSummaries_key_sorted,
    plannerSegments_eq actionCanonicalPlannerSummaries
      actionCanonicalPlannerSummaries_key_sorted]
  simp only [V1.slotSummaryStateFromWith_append]
  simpa only [sortedAbove, canonicalAbove, sorted8, canonical8,
    sortedMiddle, canonicalMiddle, sorted4, canonical4, sortedBelow,
    canonicalBelow, sAbove, cAbove, s8, c8, sMiddle, cMiddle,
    sCanonicalMiddle, s4, c4, sBelow, cBelow, sCanonicalBelow,
    V1.slotSummaryStateFromWith_append] using hSCBelow

end Zcash.Circuits.Action
