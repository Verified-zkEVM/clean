import Clean.Halo2.Keygen.FloorPlanner.V1Correctness

namespace Halo2.FloorPlanner.V1

def aboveKey (threshold : ℕ)
    (summaries : List RegionShapeSummary) : List RegionShapeSummary :=
  summaries.filter fun summary => decide (threshold < summary.key)

def atMostKey (threshold : ℕ)
    (summaries : List RegionShapeSummary) : List RegionShapeSummary :=
  summaries.filter fun summary => decide (summary.key ≤ threshold)

theorem sorted_eq_aboveKey_append_atMostKey
    (threshold : ℕ) (summaries : List RegionShapeSummary)
    (hSorted :
      (summaries.map fun summary =>
        (summary.key : OrderDual ℕ)).SortedLE) :
    summaries = aboveKey threshold summaries ++ atMostKey threshold summaries := by
  induction summaries with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      rw [List.sortedLE_iff_pairwise, List.map_cons,
        List.pairwise_cons] at hSorted
      by_cases hAbove : threshold < head.key
      · rw [aboveKey, List.filter_cons_of_pos (by simp [hAbove]),
          atMostKey, List.filter_cons_of_neg (by simp [hAbove])]
        apply congrArg (List.cons head)
        apply inductionHypothesis
        rw [List.sortedLE_iff_pairwise]
        exact hSorted.2
      · have hTailAtMost : ∀ summary ∈ tail, summary.key ≤ threshold := by
          intro summary hSummary
          have hDescending : summary.key ≤ head.key :=
            hSorted.1 (summary.key : OrderDual ℕ)
              (List.mem_map.mpr ⟨summary, hSummary, rfl⟩)
          omega
        have hTailAbove : aboveKey threshold tail = [] := by
          rw [aboveKey, List.filter_eq_nil_iff]
          intro summary hSummary
          simp only [Bool.not_eq_true, decide_eq_false_iff_not]
          exact Nat.not_lt.mpr (hTailAtMost summary hSummary)
        have hTailAtMostEq : atMostKey threshold tail = tail := by
          rw [atMostKey, List.filter_eq_self]
          intro summary hSummary
          simp only [decide_eq_true_eq]
          exact hTailAtMost summary hSummary
        have hHeadAtMost : head.key ≤ threshold := by omega
        rw [show aboveKey threshold (head :: tail) = [] by
            rw [aboveKey, List.filter_cons_of_neg (by simp [hAbove])]
            exact hTailAbove,
          show atMostKey threshold (head :: tail) = head :: tail by
            rw [atMostKey,
              List.filter_cons_of_pos (by simp [hHeadAtMost])]
            exact congrArg (List.cons head) hTailAtMostEq,
          List.nil_append]

theorem filter_key_sorted
    (predicate : RegionShapeSummary → Bool)
    (summaries : List RegionShapeSummary)
    (hSorted :
      (summaries.map fun summary =>
        (summary.key : OrderDual ℕ)).SortedLE) :
    (((summaries.filter predicate).map fun summary =>
      (summary.key : OrderDual ℕ))).SortedLE := by
  rw [List.sortedLE_iff_pairwise, List.pairwise_map] at hSorted ⊢
  exact hSorted.filter predicate

theorem perm_replicate_append_singleton_iff
    {T : Type} [DecidableEq T] {items : List T} {repeated singleton : T}
    (hNe : repeated ≠ singleton) (count : ℕ) :
    items.Perm (List.replicate count repeated ++ [singleton]) ↔
      ∃ before after, before + after = count ∧
        items = List.replicate before repeated ++
          singleton :: List.replicate after repeated := by
  constructor
  · intro hPerm
    have hSingleton : singleton ∈ items :=
      hPerm.symm.subset (by simp)
    obtain ⟨beforeItems, afterItems, hItems⟩ :=
      List.mem_iff_append.mp hSingleton
    have hCounts := (List.perm_replicate_append_replicate
      (l := items) (a := repeated) (b := singleton)
      (m := count) (n := 1) hNe).mp hPerm
    have hBeforeOnly : ∀ item ∈ beforeItems, item = repeated := by
      intro item hItem
      have hMember := hCounts.2.2 (hItems ▸
        List.mem_append.mpr (Or.inl hItem))
      rw [List.mem_cons, List.mem_singleton] at hMember
      rcases hMember with hRepeat | hSingle
      · exact hRepeat
      · have hSingletonCount : items.count singleton = 1 := hCounts.2.1
        rw [hItems, List.count_append, List.count_cons] at hSingletonCount
        simp only [BEq.beq, decide_true, if_true] at hSingletonCount
        have hBeforeZero : beforeItems.count singleton = 0 := by omega
        exact (List.count_eq_zero.mp hBeforeZero (hSingle ▸ hItem)).elim
    have hAfterOnly : ∀ item ∈ afterItems, item = repeated := by
      intro item hItem
      have hMember := hCounts.2.2 (hItems ▸
        List.mem_append.mpr (Or.inr (List.mem_cons_of_mem singleton hItem)))
      rw [List.mem_cons, List.mem_singleton] at hMember
      rcases hMember with hRepeat | hSingle
      · exact hRepeat
      · have hSingletonCount : items.count singleton = 1 := hCounts.2.1
        rw [hItems, List.count_append, List.count_cons] at hSingletonCount
        simp only [BEq.beq, decide_true, if_true] at hSingletonCount
        have hAfterZero : afterItems.count singleton = 0 := by omega
        exact (List.count_eq_zero.mp hAfterZero (hSingle ▸ hItem)).elim
    have hBefore := List.eq_replicate_length.mpr hBeforeOnly
    have hAfter := List.eq_replicate_length.mpr hAfterOnly
    refine ⟨beforeItems.length, afterItems.length, ?_, ?_⟩
    · have hLength := hPerm.length_eq
      rw [hItems] at hLength
      simp only [List.length_append, List.length_cons,
        List.length_replicate, List.length_nil] at hLength
      omega
    · exact hItems.trans (congrArg₂ (fun left right =>
        left ++ singleton :: right) hBefore hAfter)
  · rintro ⟨before, after, hCount, rfl⟩
    have hPerm := (List.perm_replicate_append_replicate
      (l := List.replicate before repeated ++
        singleton :: List.replicate after repeated)
      (a := repeated) (b := singleton) (m := count) (n := 1) hNe).mpr
        (by
          refine ⟨by simp [Ne.symm hNe, hCount], ?_, ?_⟩
          · rw [List.count_append, List.count_cons,
              List.count_replicate, List.count_replicate]
            simp [hNe]
          rw [List.append_subset, List.cons_subset]
          refine ⟨?_, by simp, ?_⟩ <;>
            intro item hItem <;>
            rw [List.mem_replicate] at hItem <;>
            simp [hItem.2])
    simpa [List.replicate_succ] using hPerm

/-- A permutation of two copies each of two distinct values is one of the six
possible interleavings. -/
theorem perm_two_replicates_iff
    {T : Type} [DecidableEq T] {items : List T} {left right : T}
    (hNe : left ≠ right) :
    items.Perm ([left, left, right, right]) ↔
      items = [left, left, right, right] ∨
      items = [left, right, left, right] ∨
      items = [left, right, right, left] ∨
      items = [right, left, left, right] ∨
      items = [right, left, right, left] ∨
      items = [right, right, left, left] := by
  constructor
  · intro hPerm
    have hLength := hPerm.length_eq
    have hMembers := hPerm.subset
    have hLeftCount := hPerm.count left
    have hRightCount := hPerm.count right
    rcases items with _ | ⟨first, items⟩ <;> simp_all
    rcases items with _ | ⟨second, items⟩ <;> simp_all
    rcases items with _ | ⟨third, items⟩ <;> simp_all
    rcases items with _ | ⟨fourth, items⟩ <;> simp_all
    rcases items with _ | ⟨fifth, items⟩ <;> simp_all
    rcases hMembers.1 with rfl | rfl <;>
    rcases hMembers.2.1 with rfl | rfl <;>
    rcases hMembers.2.2.1 with rfl | rfl <;>
    rcases hMembers.2.2.2 with rfl | rfl <;>
    simp_all [eq_comm]
  · rintro (rfl | rfl | rfl | rfl | rfl | rfl) <;>
      rw [List.perm_iff_count] <;>
      intro item <;>
      by_cases hLeft : item = left <;>
      by_cases hRight : item = right <;>
      simp_all [eq_comm]

/-- Expand a compact list of multiplicities and physical region shapes. -/
def expandPlannerBlocks
    (blocks : List (ℕ × RegionShapeSummary)) : List RegionShapeSummary :=
  blocks.flatMap fun block => List.replicate block.1 block.2

theorem expandPlannerBlocks_keySorted
    {K : Type} [LinearOrder K] (key : RegionShapeSummary → K)
    (blocks : List (ℕ × RegionShapeSummary))
    (hSorted : (blocks.map fun block => key block.2).SortedLE) :
    ((expandPlannerBlocks blocks).map key).SortedLE := by
  induction blocks with
  | nil =>
      rw [List.sortedLE_iff_pairwise]
      exact List.Pairwise.nil
  | cons block rest inductionHypothesis =>
      rw [List.sortedLE_iff_pairwise, List.map_cons,
        List.pairwise_cons] at hSorted
      rw [expandPlannerBlocks, List.flatMap_cons, List.map_append,
        List.sortedLE_iff_pairwise, List.pairwise_append]
      refine ⟨?_, ?_, ?_⟩
      · rw [← List.sortedLE_iff_pairwise]
        simpa only [List.map_replicate] using
          List.sortedLE_replicate (a := key block.2) block.1
      · have hRest := inductionHypothesis (by
          rw [List.sortedLE_iff_pairwise]
          exact hSorted.2)
        rw [List.sortedLE_iff_pairwise] at hRest
        exact hRest
      · intro left hLeft right hRight
        rw [List.mem_map] at hLeft hRight
        obtain ⟨leftSummary, hLeftSummary, rfl⟩ := hLeft
        obtain ⟨rightSummary, hRightSummary, rfl⟩ := hRight
        rw [List.mem_replicate] at hLeftSummary
        rcases hLeftSummary with ⟨_, hLeftSummary⟩
        subst leftSummary
        apply hSorted.1
        rw [List.mem_flatMap] at hRightSummary
        obtain ⟨rightBlock, hRightBlock, hRightSummary⟩ := hRightSummary
        rw [List.mem_replicate] at hRightSummary
        rcases hRightSummary with ⟨_, rfl⟩
        exact List.mem_map.mpr ⟨rightBlock, hRightBlock, rfl⟩

theorem expandPlannerBlocks_wellFormed
    (blocks : List (ℕ × RegionShapeSummary))
    (hBlocks : blocks.Forall fun block => block.2.WellFormed) :
    (expandPlannerBlocks blocks).Forall RegionShapeSummary.WellFormed := by
  rw [List.forall_iff_forall_mem]
  intro summary hSummary
  rw [expandPlannerBlocks, List.mem_flatMap] at hSummary
  obtain ⟨block, hBlock, hSummary⟩ := hSummary
  rw [List.mem_replicate] at hSummary
  exact hSummary.2 ▸
    List.forall_iff_forall_mem.mp hBlocks block hBlock

/-- The multiset represented by compact multiplicity/shape blocks. -/
def plannerBlockMultiset
    (blocks : List (ℕ × RegionShapeSummary)) : Multiset RegionShapeSummary :=
  blocks.foldr (fun block result => block.1 • {block.2} + result) 0

theorem listCoe_cons {T : Type} (head : T) (tail : List T) :
    (↑(head :: tail) : Multiset T) = head ::ₘ (↑tail : Multiset T) := rfl

theorem multisetCons_eq_add {T : Type} (head : T)
    (tail : Multiset T) : head ::ₘ tail = {head} + tail :=
  (Multiset.singleton_add head tail).symm

private theorem coe_replicate_eq_nsmul {T : Type}
    (count : ℕ) (item : T) :
    (List.replicate count item : Multiset T) = count • {item} := by
  induction count with
  | zero => rfl
  | succ count inductionHypothesis =>
      rw [List.replicate_succ, listCoe_cons, multisetCons_eq_add,
        inductionHypothesis, succ_nsmul]
      ac_rfl

theorem coe_expandPlannerBlocks
    (blocks : List (ℕ × RegionShapeSummary)) :
    (expandPlannerBlocks blocks : Multiset RegionShapeSummary) =
      plannerBlockMultiset blocks := by
  induction blocks with
  | nil => rfl
  | cons block blocks inductionHypothesis =>
      rw [show expandPlannerBlocks (block :: blocks) =
        List.replicate block.1 block.2 ++ expandPlannerBlocks blocks by
          simp [expandPlannerBlocks]]
      change (List.replicate block.1 block.2 : Multiset RegionShapeSummary) +
        (expandPlannerBlocks blocks : Multiset RegionShapeSummary) = _
      rw [coe_replicate_eq_nsmul, inductionHypothesis]
      rfl

theorem filter_expandPlannerBlocks
    (predicate : RegionShapeSummary → Bool)
    (blocks : List (ℕ × RegionShapeSummary)) :
    (expandPlannerBlocks blocks).filter predicate =
      expandPlannerBlocks (blocks.filter fun block => predicate block.2) := by
  induction blocks with
  | nil => rfl
  | cons block rest inductionHypothesis =>
      rw [expandPlannerBlocks, List.flatMap_cons, List.filter_append,
        show List.filter predicate
            (List.flatMap (fun block => List.replicate block.1 block.2) rest) =
          expandPlannerBlocks
            (List.filter (fun block => predicate block.2) rest) from
          inductionHypothesis]
      by_cases hPredicate : predicate block.2 = true
      · rw [show (block :: rest).filter (fun block => predicate block.2) =
            block :: rest.filter (fun block => predicate block.2) by
              simp [hPredicate],
          show expandPlannerBlocks
              (block :: rest.filter (fun block => predicate block.2)) =
            List.replicate block.1 block.2 ++
              expandPlannerBlocks
                (rest.filter (fun block => predicate block.2)) by
            rfl]
        simp [hPredicate]
      · rw [show (block :: rest).filter (fun block => predicate block.2) =
            rest.filter (fun block => predicate block.2) by simp [hPredicate]]
        simp [hPredicate]

namespace PlannedSummaryBlock

/-- The expanded region-summary sequence represented by a compact trace. -/
def summaries (trace : List PlannedSummaryBlock) : List RegionShapeSummary :=
  (blocks trace).flatMap fun block => List.replicate block.1 block.2

theorem slotShapeSummariesFrom_summaries
    (trace : List PlannedSummaryBlock)
    (allocations : CircuitAllocations) :
    slotShapeSummariesFrom (summaries trace) allocations =
      slotShapeSummaryBlocks (blocks trace) allocations := by
  exact slotShapeSummariesFrom_flatMap_replicate (blocks trace) allocations

theorem slotSummaryStateFromWith_summaries
    (trace : List PlannedSummaryBlock) (initial : Nat)
    (allocations : CircuitAllocations) :
    slotSummaryStateFromWith initial (summaries trace) allocations =
      slotSummaryBlocksState (blocks trace) initial allocations := by
  exact slotSummaryStateFromWith_flatMap_replicate
    (blocks trace) initial allocations

theorem slotSummaryStateFromWith_summaries_result
    (trace : List PlannedSummaryBlock) (initial : Nat)
    (allocations : CircuitAllocations) (view : AllocationView)
    (hRepresents : view.Represents allocations) (hValid : view.Valid)
    (hLawful : Lawful view trace) :
    let result := slotSummaryStateFromWith initial (summaries trace) allocations
    result.1 = endpointFrom initial trace ∧
      (finalView view trace).Represents result.2 := by
  rw [slotSummaryStateFromWith_summaries]
  exact slotSummaryBlocksState_eq trace initial allocations view
    hRepresents hValid hLawful

theorem summaries_append (left right : List PlannedSummaryBlock) :
    summaries (left ++ right) = summaries left ++ summaries right := by
  simp [summaries, blocks]

theorem summaries_singleton (block : PlannedSummaryBlock) :
    summaries [block] = List.replicate block.count block.summary := by
  simp [summaries, blocks]

theorem Lawful.summaries_wellFormed
    {initial : AllocationView} {trace : List PlannedSummaryBlock}
    (hLawful : Lawful initial trace) :
    (summaries trace).Forall RegionShapeSummary.WellFormed := by
  induction trace generalizing initial with
  | nil => simp [summaries, blocks]
  | cons block rest inductionHypothesis =>
      rw [summaries, blocks, List.map_cons, List.flatMap_cons,
        List.forall_append]
      constructor
      · induction block.count with
        | zero => simp
        | succ count inductionHypothesis =>
            rw [List.replicate_succ, List.forall_cons]
            exact ⟨hLawful.2.1, inductionHypothesis⟩
      · exact inductionHypothesis hLawful.2.2.2.2.2

/-- A compact run, omitting its entry when the multiplicity is zero. -/
def run (count : ℕ) (summary : RegionShapeSummary)
    (start : ℕ) : List PlannedSummaryBlock :=
  if count = 0 then [] else [{ count, summary, start }]

theorem summaries_run (count : Nat) (summary : RegionShapeSummary)
    (start : Nat) :
    summaries (run count summary start) = List.replicate count summary := by
  by_cases hCount : count = 0
  · subst count
    rfl
  · simp [run, hCount, summaries, blocks]

theorem finalView_run (view : AllocationView) (count : Nat)
    (summary : RegionShapeSummary) (start : Nat) :
    finalView view (run count summary start) =
      view.insertRepeated (sortRegionColumns summary.columns) start
        summary.rowCount count := by
  by_cases hCount : count = 0
  · simp [run, hCount, finalView, AllocationView.insertRepeated]
  · simp [run, hCount, finalView]

theorem endpointFrom_append (initial : Nat)
    (left right : List PlannedSummaryBlock) :
    endpointFrom initial (left ++ right) =
      endpointFrom (endpointFrom initial left) right := by
  induction left generalizing initial with
  | nil => rfl
  | cons block rest inductionHypothesis =>
      simp only [List.cons_append, endpointFrom]
      exact inductionHypothesis _

theorem endpointFrom_run (initial count : Nat)
    (summary : RegionShapeSummary) (start : Nat) (hCount : 0 < count) :
    endpointFrom initial (run count summary start) =
      max initial (start + count * summary.rowCount) := by
  simp [run, Nat.ne_of_gt hCount, endpointFrom]

/-- A summary stream represented by one lawful compact trace has the same
planner state as another lawful trace with the same endpoint and final view. -/
theorem slotSummaryStateFromWith_equivalent_of_traces
    (summaries : List RegionShapeSummary)
    (left right : List PlannedSummaryBlock)
    (hSummaries : List.Forall₂ RegionShapeSummary.PlacementEquivalent
      summaries (PlannedSummaryBlock.summaries left))
    (initial : Nat) (allocations : CircuitAllocations)
    (view : AllocationView) (hRepresents : view.Represents allocations)
    (hValid : view.Valid) (hLeft : Lawful view left)
    (hRight : Lawful view right)
    (hEndpoint : endpointFrom initial left = endpointFrom initial right)
    (hFinalView : finalView view left = finalView view right) :
    SummaryStateEquivalent
      (slotSummaryStateFromWith initial summaries allocations)
      (slotSummaryStateFromWith initial
        (PlannedSummaryBlock.summaries right) allocations) := by
  rw [slotSummaryStateFromWith_eq_of_forall₂_placementEquivalent
    hSummaries]
  rw [PlannedSummaryBlock.slotSummaryStateFromWith_summaries,
    PlannedSummaryBlock.slotSummaryStateFromWith_summaries]
  exact PlannedSummaryBlock.slotSummaryBlocksState_equivalent
    left right initial allocations view hRepresents hValid hLeft hRight
      hEndpoint hFinalView

/-- Variant for equivalent incoming states represented by the same allocation
view. -/
theorem slotSummaryStateFromWith_equivalent_of_traces_of_represents
    (summaries : List RegionShapeSummary)
    (left right : List PlannedSummaryBlock)
    (hSummaries : List.Forall₂ RegionShapeSummary.PlacementEquivalent
      summaries (PlannedSummaryBlock.summaries left))
    (leftInitial rightInitial : Nat)
    (leftAllocations rightAllocations : CircuitAllocations)
    (view : AllocationView)
    (hLeftRepresents : view.Represents leftAllocations)
    (hRightRepresents : view.Represents rightAllocations)
    (hValid : view.Valid) (hLeft : Lawful view left)
    (hRight : Lawful view right)
    (hEndpoint : endpointFrom leftInitial left =
      endpointFrom rightInitial right)
    (hFinalView : finalView view left = finalView view right) :
    SummaryStateEquivalent
      (slotSummaryStateFromWith leftInitial summaries leftAllocations)
      (slotSummaryStateFromWith rightInitial
        (PlannedSummaryBlock.summaries right) rightAllocations) := by
  rw [slotSummaryStateFromWith_eq_of_forall₂_placementEquivalent
    hSummaries]
  rw [PlannedSummaryBlock.slotSummaryStateFromWith_summaries,
    PlannedSummaryBlock.slotSummaryStateFromWith_summaries]
  exact PlannedSummaryBlock.slotSummaryBlocksState_equivalent_of_represents
    left right leftInitial rightInitial leftAllocations rightAllocations view
      hLeftRepresents hRightRepresents hValid hLeft hRight hEndpoint hFinalView

end PlannedSummaryBlock

theorem allocationsValid_of_summaryStateEquivalent
    {left right : ℕ × CircuitAllocations}
    (hEquivalent : SummaryStateEquivalent left right)
    (hRightValid : right.2.Valid) : left.2.Valid := by
  intro column
  rw [hEquivalent.2 column]
  exact hRightValid column

theorem continueCanonicalSegment
    (summaries : List RegionShapeSummary)
    (hWellFormed : summaries.Forall RegionShapeSummary.WellFormed)
    {left right : ℕ × CircuitAllocations}
    (hRightValid : right.2.Valid)
    (hEquivalent : SummaryStateEquivalent left right) :
    SummaryStateEquivalent
      (slotSummaryStateFromWith left.1 summaries left.2)
      (slotSummaryStateFromWith right.1 summaries right.2) :=
  slotSummaryStateFromWith_equivalent summaries hWellFormed
    (allocationsValid_of_summaryStateEquivalent hEquivalent hRightValid)
    hRightValid hEquivalent

end Halo2.FloorPlanner.V1

namespace Halo2

/-- Advance one concrete compact planner-trace entry. Callers provide the
definitions needed to normalize their reduced region shapes. -/
macro "planner_trace_step"
    " [" definitions:Lean.Parser.Tactic.simpLemma,* "]" : tactic => do
  let traceLawfulAfter :=
    Lean.mkIdent ``Halo2.FloorPlanner.V1.PlannedSummaryBlock.TraceLawfulAfter
  let wellFormed :=
    Lean.mkIdent ``Halo2.FloorPlanner.RegionShapeSummary.WellFormed
  let fitsAfterAt :=
    Lean.mkIdent ``Halo2.FloorPlanner.V1.PlannedSummaryBlock.FitsAfterAt
  let rowIntervalsDisjoint :=
    Lean.mkIdent ``Halo2.FloorPlanner.RowIntervalsDisjoint
  let nilAppend := Lean.mkIdent ``List.nil_append
  let consAppend := Lean.mkIdent ``List.cons_append
  let appendNil := Lean.mkIdent ``List.append_nil
  let appendAssoc := Lean.mkIdent ``List.append_assoc
  `(tactic|
    (unfold $traceLawfulAfter:ident
     refine ⟨by first | omega | norm_num,
       by simp [$wellFormed:ident, $definitions,*],
       by simp [$definitions,*], ?_, ?_, ?_⟩
     · simp [$fitsAfterAt:ident, $definitions,*,
         $rowIntervalsDisjoint:ident] <;> omega
     · intro candidate hFits
       simp [$fitsAfterAt:ident, $definitions,*,
         $rowIntervalsDisjoint:ident] at hFits
       try norm_num at hFits ⊢
       try omega
     simp only [$nilAppend:ident, $consAppend:ident, $appendNil:ident,
       $appendAssoc:ident]))

end Halo2
