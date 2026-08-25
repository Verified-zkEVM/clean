import Clean.Halo2.Keygen.PdqsortCorrectness

namespace Halo2.FloorPlanner.V1

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

private theorem listCoe_cons {T : Type} (head : T) (tail : List T) :
    (↑(head :: tail) : Multiset T) = head ::ₘ (↑tail : Multiset T) := rfl

private theorem multisetCons_eq_add {T : Type} (head : T)
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

theorem summaries_append (left right : List PlannedSummaryBlock) :
    summaries (left ++ right) = summaries left ++ summaries right := by
  simp [summaries, blocks]

/-- A compact run, omitting its entry when the multiplicity is zero. -/
def run (count : ℕ) (summary : RegionShapeSummary)
    (start : ℕ) : List PlannedSummaryBlock :=
  if count = 0 then [] else [{ count, summary, start }]

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
