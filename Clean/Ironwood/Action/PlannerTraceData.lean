import Clean.Ironwood.Action.Planner
import Clean.Halo2.Keygen.PdqsortCorrectness

namespace Zcash.Circuits.Action

open Halo2 FloorPlanner

private def aboveKey (threshold : ℕ)
    (summaries : List RegionShapeSummary) : List RegionShapeSummary :=
  summaries.filter fun summary => decide (threshold < summary.key)

private def atMostKey (threshold : ℕ)
    (summaries : List RegionShapeSummary) : List RegionShapeSummary :=
  summaries.filter fun summary => decide (summary.key ≤ threshold)

private theorem sorted_eq_aboveKey_append_atMostKey
    (threshold : ℕ) (summaries : List RegionShapeSummary)
    (hsorted :
      (summaries.map fun summary =>
        (summary.key : OrderDual ℕ)).SortedLE) :
    summaries = aboveKey threshold summaries ++ atMostKey threshold summaries := by
  induction summaries with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      rw [List.sortedLE_iff_pairwise, List.map_cons,
        List.pairwise_cons] at hsorted
      by_cases habove : threshold < head.key
      · rw [aboveKey, List.filter_cons_of_pos (by simp [habove]),
          atMostKey, List.filter_cons_of_neg (by simp [habove])]
        apply congrArg (List.cons head)
        apply inductionHypothesis
        rw [List.sortedLE_iff_pairwise]
        exact hsorted.2
      · have htailAtMost : ∀ summary ∈ tail, summary.key ≤ threshold := by
          intro summary hsummary
          have hdescending : summary.key ≤ head.key :=
            hsorted.1 (summary.key : OrderDual ℕ)
              (List.mem_map.mpr ⟨summary, hsummary, rfl⟩)
          omega
        have htailAbove : aboveKey threshold tail = [] := by
          rw [aboveKey, List.filter_eq_nil_iff]
          intro summary hsummary
          simp only [Bool.not_eq_true, decide_eq_false_iff_not]
          exact Nat.not_lt.mpr (htailAtMost summary hsummary)
        have htailAtMostEq : atMostKey threshold tail = tail := by
          rw [atMostKey, List.filter_eq_self]
          intro summary hsummary
          simp only [decide_eq_true_eq]
          exact htailAtMost summary hsummary
        have hheadAtMost : head.key ≤ threshold := by omega
        rw [show aboveKey threshold (head :: tail) = [] by
            rw [aboveKey, List.filter_cons_of_neg (by simp [habove])]
            exact htailAbove,
          show atMostKey threshold (head :: tail) = head :: tail by
            rw [atMostKey,
              List.filter_cons_of_pos (by simp [hheadAtMost])]
            exact congrArg (List.cons head) htailAtMostEq,
          List.nil_append]

private theorem filter_key_sorted
    (predicate : RegionShapeSummary → Bool)
    (summaries : List RegionShapeSummary)
    (hsorted :
      (summaries.map fun summary =>
        (summary.key : OrderDual ℕ)).SortedLE) :
    (((summaries.filter predicate).map fun summary =>
      (summary.key : OrderDual ℕ))).SortedLE := by
  rw [List.sortedLE_iff_pairwise, List.pairwise_map] at hsorted ⊢
  exact hsorted.filter predicate

private theorem perm_replicate_append_singleton_iff
    {T : Type} [DecidableEq T] {items : List T} {repeated singleton : T}
    (hne : repeated ≠ singleton) (count : ℕ) :
    items.Perm (List.replicate count repeated ++ [singleton]) ↔
      ∃ before after, before + after = count ∧
        items = List.replicate before repeated ++
          singleton :: List.replicate after repeated := by
  constructor
  · intro hperm
    have hsingleton : singleton ∈ items :=
      hperm.symm.subset (by simp)
    obtain ⟨beforeItems, afterItems, hitems⟩ :=
      List.mem_iff_append.mp hsingleton
    have hcounts := (List.perm_replicate_append_replicate
      (l := items) (a := repeated) (b := singleton)
      (m := count) (n := 1) hne).mp hperm
    have hbeforeOnly : ∀ item ∈ beforeItems, item = repeated := by
      intro item hitem
      have hmember := hcounts.2.2 (hitems ▸
        List.mem_append.mpr (Or.inl hitem))
      rw [List.mem_cons, List.mem_singleton] at hmember
      rcases hmember with hrepeat | hsingle
      · exact hrepeat
      · have hitemSingleton : singleton ∈ beforeItems := hsingle ▸ hitem
        have hsingletonCount : items.count singleton = 1 := hcounts.2.1
        rw [hitems, List.count_append, List.count_cons] at hsingletonCount
        simp only [BEq.beq, decide_true, if_true] at hsingletonCount
        have hbeforeZero : beforeItems.count singleton = 0 := by omega
        exact (List.count_eq_zero.mp hbeforeZero hitemSingleton).elim
    have hafterOnly : ∀ item ∈ afterItems, item = repeated := by
      intro item hitem
      have hmember := hcounts.2.2 (hitems ▸
        List.mem_append.mpr (Or.inr (List.mem_cons_of_mem singleton hitem)))
      rw [List.mem_cons, List.mem_singleton] at hmember
      rcases hmember with hrepeat | hsingle
      · exact hrepeat
      · have hitemSingleton : singleton ∈ afterItems := hsingle ▸ hitem
        have hsingletonCount : items.count singleton = 1 := hcounts.2.1
        rw [hitems, List.count_append, List.count_cons] at hsingletonCount
        simp only [BEq.beq, decide_true, if_true] at hsingletonCount
        have hafterZero : afterItems.count singleton = 0 := by omega
        exact (List.count_eq_zero.mp hafterZero hitemSingleton).elim
    have hbefore := List.eq_replicate_length.mpr hbeforeOnly
    have hafter := List.eq_replicate_length.mpr hafterOnly
    refine ⟨beforeItems.length, afterItems.length, ?_, ?_⟩
    · have hlength := hperm.length_eq
      rw [hitems] at hlength
      simp only [List.length_append, List.length_cons,
        List.length_replicate, List.length_nil] at hlength
      omega
    · exact hitems.trans (congrArg₂ (fun left right =>
        left ++ singleton :: right) hbefore hafter)
  · rintro ⟨before, after, hcount, rfl⟩
    have hperm := (List.perm_replicate_append_replicate
      (l := List.replicate before repeated ++
        singleton :: List.replicate after repeated)
      (a := repeated) (b := singleton) (m := count) (n := 1) hne).mpr
        (by
          refine ⟨by simp [Ne.symm hne, hcount],
            ?_, ?_⟩
          · rw [List.count_append, List.count_cons,
              List.count_replicate, List.count_replicate]
            simp [hne]
          rw [List.append_subset, List.cons_subset]
          refine ⟨?_, by simp, ?_⟩ <;>
            intro item hitem <;>
            rw [List.mem_replicate] at hitem <;>
            simp [hitem.2])
    simpa [List.replicate_succ] using hperm

private theorem listCoe_cons {T : Type} (head : T) (tail : List T) :
    (↑(head :: tail) : Multiset T) = head ::ₘ (↑tail : Multiset T) := rfl

private theorem multisetCons_eq_add {T : Type} (head : T)
    (tail : Multiset T) : head ::ₘ tail = {head} + tail :=
  (Multiset.singleton_add head tail).symm

/-- A concise physical region shape for Action's ten advice columns and selected
fixed columns. -/
def plannerShape (advice : List ℕ) (rows : ℕ)
    (fixed : List ℕ := []) : RegionShapeSummary :=
  { columns := advice.map (.column .advice) ++ fixed.map (.column .fixed)
    rowCount := rows }

/-- Action's 33 canonical physical shape blocks in descending planner-key order. -/
def actionPlannerBlocks : List (ℕ × RegionShapeSummary) :=
  [(1, plannerShape [0,1,2,3,4,5,6,7,8,9] 137),
    (1, plannerShape [0,1,2,3,4] 110 [3,12]),
    (1, plannerShape [5,6,7,8,9] 110 [4,13]),
    (1, plannerShape [0,1,2,3,4,5] 86 [3,4,5,6,7,8,9,10,11]),
    (5, plannerShape [0,1,2,3,4,5] 85 [3,4,5,6,7,8,9,10,11]),
    (16, plannerShape [0,1,2,3,4] 53 [3,12]),
    (16, plannerShape [5,6,7,8,9] 53 [4,13]),
    (1, plannerShape [0,1,2,3,4] 52 [3,12]),
    (1, plannerShape [5,6,7,8] 37 [5,6,7,8,9,10]),
    (1, plannerShape [0,1,2,3,4,5] 23 [3,4,5,6,7,8,9,10,11]),
    (1, plannerShape [0,1,2,3,4,5,6,7,8,9] 4),
    (4, plannerShape [9] 26),
    (14, plannerShape [0,1,2,3,4,5,6,7,8] 2),
    (5, plannerShape [9] 15), (11, plannerShape [9] 14),
    (16, plannerShape [0,1,2,3,4] 2),
    (20, plannerShape [5,6,7,8,9] 2),
    (3, plannerShape [6,7,8] 3),
    (8, plannerShape [6,7,8,9] 2),
    (1, plannerShape [0,1,2,3,4,5,6,7] 1),
    (4, plannerShape [6,7,8] 2),
    (16, plannerShape [0,1,2,3,4] 1),
    (16, plannerShape [5,6,7,8,9] 1),
    (2, plannerShape [6,7] 2),
    (2, plannerShape [6,7,8,9] 1),
    (89, plannerShape [9] 3),
    (6, plannerShape [6,7,8] 1),
    (6, plannerShape [0,1] 1), (2, plannerShape [9] 1),
    (61, plannerShape [6] 1), (6, plannerShape [0] 1),
    (56, plannerShape [7] 1), (2, plannerShape [] 0)]

/-- Action's canonical V1 input, retaining repeated blocks symbolically rather
than expanding the 395-region synthesis trace. -/
def actionCanonicalPlannerSummaries : List RegionShapeSummary :=
  actionPlannerBlocks.flatMap fun block =>
    List.replicate block.1 block.2

private def witnessPlannerBlocks : List (ℕ × RegionShapeSummary) :=
  [(2, plannerShape [0] 1),
    (3, plannerShape [0,1] 1),
    (3, plannerShape [0] 1)]

private def crossAddressPlannerBlocks : List (ℕ × RegionShapeSummary) :=
  [(1, plannerShape [0,1,2,3,4,5,6,7,8,9] 4)]

private def checksPlannerBlocks : List (ℕ × RegionShapeSummary) :=
  [(1, plannerShape [0,1,2,3,4,5,6,7,8,9] 137),
    (1, plannerShape [0,1,2,3,4,5] 86 [3,4,5,6,7,8,9,10,11]),
    (3, plannerShape [0,1,2,3,4,5] 85 [3,4,5,6,7,8,9,10,11]),
    (16, plannerShape [0,1,2,3,4] 53 [3,12]),
    (16, plannerShape [5,6,7,8,9] 53 [4,13]),
    (1, plannerShape [0,1,2,3,4] 52 [3,12]),
    (1, plannerShape [5,6,7,8] 37 [5,6,7,8,9,10]),
    (1, plannerShape [0,1,2,3,4,5] 23 [3,4,5,6,7,8,9,10,11]),
    (10, plannerShape [0,1,2,3,4,5,6,7,8] 2),
    (1, plannerShape [9] 15), (3, plannerShape [9] 14),
    (16, plannerShape [0,1,2,3,4] 2),
    (16, plannerShape [5,6,7,8,9] 2),
    (3, plannerShape [6,7,8] 3),
    (16, plannerShape [0,1,2,3,4] 1),
    (16, plannerShape [5,6,7,8,9] 1),
    (67, plannerShape [9] 3),
    (2, plannerShape [6,7,8] 1),
    (1, plannerShape [0,1] 1), (2, plannerShape [9] 1),
    (53, plannerShape [6] 1),
    (48, plannerShape [7] 1), (1, plannerShape [] 0)]

private def notesPlannerBlocks : List (ℕ × RegionShapeSummary) :=
  [(1, plannerShape [0,1,2,3,4] 110 [3,12]),
    (1, plannerShape [5,6,7,8,9] 110 [4,13]),
    (2, plannerShape [0,1,2,3,4,5] 85 [3,4,5,6,7,8,9,10,11]),
    (4, plannerShape [9] 26),
    (4, plannerShape [0,1,2,3,4,5,6,7,8] 2),
    (4, plannerShape [9] 15), (8, plannerShape [9] 14),
    (4, plannerShape [5,6,7,8,9] 2),
    (8, plannerShape [6,7,8,9] 2),
    (1, plannerShape [0,1,2,3,4,5,6,7] 1),
    (4, plannerShape [6,7,8] 2),
    (2, plannerShape [6,7] 2),
    (2, plannerShape [6,7,8,9] 1),
    (22, plannerShape [9] 3),
    (4, plannerShape [6,7,8] 1),
    (2, plannerShape [0,1] 1),
    (8, plannerShape [6] 1), (1, plannerShape [0] 1),
    (8, plannerShape [7] 1), (1, plannerShape [] 0)]

private def expandPlannerBlocks
    (blocks : List (ℕ × RegionShapeSummary)) : List RegionShapeSummary :=
  blocks.flatMap fun block => List.replicate block.1 block.2

private theorem expandPlannerBlocks_key_sorted
    {K : Type} [LinearOrder K] (key : RegionShapeSummary → K)
    (blocks : List (ℕ × RegionShapeSummary))
    (hsorted : (blocks.map fun block => key block.2).SortedLE) :
    ((expandPlannerBlocks blocks).map key).SortedLE := by
  induction blocks with
  | nil =>
      rw [List.sortedLE_iff_pairwise]
      exact List.Pairwise.nil
  | cons block rest inductionHypothesis =>
      rw [List.sortedLE_iff_pairwise, List.map_cons,
        List.pairwise_cons] at hsorted
      rw [expandPlannerBlocks, List.flatMap_cons, List.map_append,
        List.sortedLE_iff_pairwise, List.pairwise_append]
      refine ⟨?_, ?_, ?_⟩
      · rw [← List.sortedLE_iff_pairwise]
        simpa only [List.map_replicate] using
          List.sortedLE_replicate (a := key block.2) block.1
      · have hrest := inductionHypothesis (by
          rw [List.sortedLE_iff_pairwise]
          exact hsorted.2)
        rw [List.sortedLE_iff_pairwise] at hrest
        exact hrest
      · intro left hleft right hright
        rw [List.mem_map] at hleft hright
        obtain ⟨leftSummary, hleftSummary, rfl⟩ := hleft
        obtain ⟨rightSummary, hrightSummary, rfl⟩ := hright
        rw [List.mem_replicate] at hleftSummary
        rcases hleftSummary with ⟨_, hleftSummary⟩
        subst leftSummary
        apply hsorted.1
        rw [List.mem_flatMap] at hrightSummary
        obtain ⟨rightBlock, hrightBlock, hrightSummary⟩ := hrightSummary
        rw [List.mem_replicate] at hrightSummary
        rcases hrightSummary with ⟨_, rfl⟩
        exact List.mem_map.mpr ⟨rightBlock, hrightBlock, rfl⟩

private theorem actionCanonicalPlannerSummaries_key_sorted :
    ((actionCanonicalPlannerSummaries.map fun summary =>
      (summary.key : OrderDual ℕ))).SortedLE := by
  rw [show actionCanonicalPlannerSummaries =
      expandPlannerBlocks actionPlannerBlocks by rfl]
  apply expandPlannerBlocks_key_sorted
  unfold actionPlannerBlocks plannerShape RegionShapeSummary.key
    RegionShapeSummary.adviceCols RegionColumn.isAdvice
  decide

private theorem actionSortedPlannerSummaries_key_sorted :
    ((actionSortedPlannerSummaries.map fun summary =>
      (summary.key : OrderDual ℕ))).SortedLE := by
  have hsorted :=
    V1.sortedSummaryOrder_key_sorted actionOperations
  rw [List.sortedLE_iff_pairwise, List.pairwise_map] at hsorted ⊢
  simpa only [actionSortedPlannerSummaries, List.pairwise_map,
    RegionShapeSummary.withoutSelectors_key] using hsorted

private theorem actionPlannerBlocks_wellFormed :
    actionPlannerBlocks.Forall fun block => block.2.WellFormed := by
  unfold actionPlannerBlocks plannerShape RegionShapeSummary.WellFormed
  decide

private theorem expandPlannerBlocks_wellFormed
    (blocks : List (ℕ × RegionShapeSummary))
    (hblocks : blocks.Forall fun block => block.2.WellFormed) :
    (expandPlannerBlocks blocks).Forall RegionShapeSummary.WellFormed := by
  rw [List.forall_iff_forall_mem]
  intro summary hsummary
  rw [expandPlannerBlocks, List.mem_flatMap] at hsummary
  obtain ⟨block, hblock, hsummary⟩ := hsummary
  rw [List.mem_replicate] at hsummary
  exact hsummary.2 ▸
    List.forall_iff_forall_mem.mp hblocks block hblock

private theorem actionCanonicalPlannerSummaries_wellFormed :
    actionCanonicalPlannerSummaries.Forall RegionShapeSummary.WellFormed := by
  rw [show actionCanonicalPlannerSummaries =
      expandPlannerBlocks actionPlannerBlocks by rfl]
  exact expandPlannerBlocks_wellFormed actionPlannerBlocks
    actionPlannerBlocks_wellFormed

private theorem actionPlannerBlocks_regular_ties :
    actionPlannerBlocks.Forall fun first =>
      actionPlannerBlocks.Forall fun second =>
        first.2.key = second.2.key → first.2.key ≠ 8 →
          first.2.key ≠ 4 →
            (sortRegionColumns first.2.columns =
                sortRegionColumns second.2.columns ∧
              first.2.rowCount = second.2.rowCount) ∨
              (first.2.columns.all fun column =>
                decide (column ∉ second.2.columns)) = true := by
  unfold actionPlannerBlocks plannerShape RegionShapeSummary.key
    RegionShapeSummary.adviceCols RegionColumn.isAdvice
  decide

private theorem actionCanonicalPlannerSummaries_regular_ties
    {first second : RegionShapeSummary}
    (hfirst : first ∈ actionCanonicalPlannerSummaries)
    (hsecond : second ∈ actionCanonicalPlannerSummaries)
    (hkey : first.key = second.key)
    (hne8 : first.key ≠ 8) (hne4 : first.key ≠ 4) :
    first.PlacementEquivalent second ∨
      List.Disjoint first.columns second.columns := by
  rw [actionCanonicalPlannerSummaries, List.mem_flatMap] at hfirst hsecond
  obtain ⟨firstBlock, hfirstBlock, hfirst⟩ := hfirst
  obtain ⟨secondBlock, hsecondBlock, hsecond⟩ := hsecond
  rw [List.mem_replicate] at hfirst hsecond
  have hfirstLaw := List.forall_iff_forall_mem.mp
    actionPlannerBlocks_regular_ties firstBlock hfirstBlock
  have hresult := List.forall_iff_forall_mem.mp hfirstLaw secondBlock
    hsecondBlock (by simpa only [hfirst.2, hsecond.2] using hkey)
    (by simpa only [hfirst.2] using hne8)
    (by simpa only [hfirst.2] using hne4)
  rcases hresult with hequivalent | hdisjoint
  · exact Or.inl (by simpa only [hfirst.2, hsecond.2] using hequivalent)
  · right
    rw [List.disjoint_left]
    intro column hfirstColumn hsecondColumn
    have hnotSecond := List.all_eq_true.mp hdisjoint column
      (by simpa only [hfirst.2] using hfirstColumn)
    simp only [decide_eq_true_eq] at hnotSecond
    exact hnotSecond (by simpa only [hsecond.2] using hsecondColumn)

private def plannerAbove8 (summaries : List RegionShapeSummary) :=
  aboveKey 8 summaries

private def plannerKey8 (summaries : List RegionShapeSummary) :=
  summaries.filter fun summary => decide (summary.key = 8)

private def plannerBetween8And4 (summaries : List RegionShapeSummary) :=
  summaries.filter fun summary => decide (4 < summary.key ∧ summary.key < 8)

private def plannerKey4 (summaries : List RegionShapeSummary) :=
  summaries.filter fun summary => decide (summary.key = 4)

private def plannerBelow4 (summaries : List RegionShapeSummary) :=
  summaries.filter fun summary => decide (summary.key < 4)

private theorem plannerSegments_eq
    (summaries : List RegionShapeSummary)
    (hsorted :
      (summaries.map fun summary =>
        (summary.key : OrderDual ℕ)).SortedLE) :
    summaries =
      plannerAbove8 summaries ++ plannerKey8 summaries ++
        plannerBetween8And4 summaries ++ plannerKey4 summaries ++
          plannerBelow4 summaries := by
  have hsplit8 := sorted_eq_aboveKey_append_atMostKey 8 summaries hsorted
  have hsorted8 := filter_key_sorted
    (fun summary => decide (summary.key ≤ 8)) summaries hsorted
  have hsplit7 := sorted_eq_aboveKey_append_atMostKey 7
    (atMostKey 8 summaries) hsorted8
  have hsorted7 := filter_key_sorted
    (fun summary => decide (summary.key ≤ 7)) (atMostKey 8 summaries)
    hsorted8
  have hsplit4 := sorted_eq_aboveKey_append_atMostKey 4
    (atMostKey 7 (atMostKey 8 summaries)) hsorted7
  have hsorted4 := filter_key_sorted
    (fun summary => decide (summary.key ≤ 4))
    (atMostKey 7 (atMostKey 8 summaries)) hsorted7
  have hsplit3 := sorted_eq_aboveKey_append_atMostKey 3
    (atMostKey 4 (atMostKey 7 (atMostKey 8 summaries))) hsorted4
  have hkey8 :
      aboveKey 7 (atMostKey 8 summaries) = plannerKey8 summaries := by
    unfold aboveKey atMostKey plannerKey8
    rw [List.filter_filter]
    apply List.filter_congr
    intro summary _
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    omega
  have hmiddle :
      aboveKey 4 (atMostKey 7 (atMostKey 8 summaries)) =
        plannerBetween8And4 summaries := by
    unfold aboveKey atMostKey plannerBetween8And4
    rw [List.filter_filter, List.filter_filter]
    apply List.filter_congr
    intro summary _
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    omega
  have hkey4 :
      aboveKey 3 (atMostKey 4 (atMostKey 7 (atMostKey 8 summaries))) =
        plannerKey4 summaries := by
    unfold aboveKey atMostKey plannerKey4
    rw [List.filter_filter, List.filter_filter, List.filter_filter]
    apply List.filter_congr
    intro summary _
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    omega
  have hbelow :
      atMostKey 3 (atMostKey 4 (atMostKey 7 (atMostKey 8 summaries))) =
        plannerBelow4 summaries := by
    unfold atMostKey plannerBelow4
    rw [List.filter_filter, List.filter_filter, List.filter_filter]
    apply List.filter_congr
    intro summary _
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    omega
  calc
    summaries = aboveKey 8 summaries ++ atMostKey 8 summaries := hsplit8
    _ = aboveKey 8 summaries ++
        (aboveKey 7 (atMostKey 8 summaries) ++
          atMostKey 7 (atMostKey 8 summaries)) :=
      congrArg (fun tail => aboveKey 8 summaries ++ tail) hsplit7
    _ = aboveKey 8 summaries ++
        (aboveKey 7 (atMostKey 8 summaries) ++
          (aboveKey 4 (atMostKey 7 (atMostKey 8 summaries)) ++
            atMostKey 4 (atMostKey 7 (atMostKey 8 summaries)))) :=
      congrArg
        (fun tail => aboveKey 8 summaries ++
          (aboveKey 7 (atMostKey 8 summaries) ++ tail)) hsplit4
    _ = aboveKey 8 summaries ++
        (aboveKey 7 (atMostKey 8 summaries) ++
          (aboveKey 4 (atMostKey 7 (atMostKey 8 summaries)) ++
            (aboveKey 3
                (atMostKey 4 (atMostKey 7 (atMostKey 8 summaries))) ++
              atMostKey 3
                (atMostKey 4 (atMostKey 7 (atMostKey 8 summaries)))))) :=
      congrArg
        (fun tail => aboveKey 8 summaries ++
          (aboveKey 7 (atMostKey 8 summaries) ++
            (aboveKey 4 (atMostKey 7 (atMostKey 8 summaries)) ++ tail)))
        hsplit3
    _ = plannerAbove8 summaries ++ plannerKey8 summaries ++
        plannerBetween8And4 summaries ++ plannerKey4 summaries ++
          plannerBelow4 summaries := by
      rw [hkey8, hmiddle, hkey4, hbelow]
      simp only [plannerAbove8, List.append_assoc]

private def plannerBlockMultiset
    (blocks : List (ℕ × RegionShapeSummary)) : Multiset RegionShapeSummary :=
  blocks.foldr (fun block result => block.1 • {block.2} + result) 0

private theorem coe_replicate_eq_nsmul {T : Type} (count : ℕ) (item : T) :
    (List.replicate count item : Multiset T) = count • {item} := by
  induction count with
  | zero => rfl
  | succ count inductionHypothesis =>
      rw [List.replicate_succ, listCoe_cons, multisetCons_eq_add,
        inductionHypothesis, succ_nsmul]
      ac_rfl

private theorem coe_expandPlannerBlocks
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

private theorem witnessPlannerBlocks_correct :
    ((Circuit.synthWitnessSynthesisSummary actionConfig).physicalRegionShapes.map
      RegionShapeSummary.normalized : Multiset RegionShapeSummary) =
        plannerBlockMultiset witnessPlannerBlocks := by
  rw [Circuit.synthWitnessSynthesisSummary_physicalRegionShapes]
  simp [witnessPlannerBlocks, plannerBlockMultiset,
    Sinsemilla.loadSynthesisSummary, Circuit.loadPrivateSynthesisSummary,
    Ecc.WitnessPoint.pointSynthesisSummary,
    Ecc.WitnessPoint.pointNonIdSynthesisSummary,
    SynthesisSummary.physicalRegionShapes, SynthesisSummary.ofRegion,
    RegionSynthesisSummary.ofColumns,
    RegionSynthesisSummary.toRegionShapeSummary,
    RegionShapeSummary.withoutSelectors, physicalColumns,
    unionColumns, addColumn,
    RegionShapeSummary.normalized, plannerShape,
    sortRegionColumns,
    RegionColumn.lt, RegionColumn.ordKey, RegionColumn.kindRank,
    actionConfig, Circuit.configure, Circuit.configureBase,
    Circuit.configureChips, Circuit.configureShared,
    Circuit.configureAdvices, Circuit.configureAdviceEqualitiesLow,
    Circuit.configureAdviceEqualitiesHigh, Circuit.configureEqualities,
    Circuit.configureLagrange, AddChip.configure, Ecc.configure,
    LookupRangeCheck.configure, Poseidon.configure,
    Sinsemilla.HashPiece.configure, Sinsemilla.Merkle.configure,
    CondSwap.configure, Ecc.Add.add, Ecc.AddIncomplete.add,
    Ecc.Mul.configure, Ecc.MulFixed.BaseFieldElem.configure,
    Ecc.MulFixed.FullWidth.configure, Ecc.MulFixed.Short.configure,
    Ecc.MulFixed.configure, Ecc.WitnessPoint.configure,
    Ecc.MulComplete.configure, Ecc.MulIncomplete.configure,
    Ecc.MulOverflow.configure, Sinsemilla.Merkle.Gate.configure,
    lookupTableColumn, Configure.run_fst, keygen_norm]
  simp only [listCoe_cons, multisetCons_eq_add, Multiset.coe_nil]
  abel

private theorem crossAddressPlannerBlocks_correct :
    ((Circuit.synthCrossAddressChecksSynthesisSummary
      actionConfig).physicalRegionShapes.map
        RegionShapeSummary.normalized : Multiset RegionShapeSummary) =
      plannerBlockMultiset crossAddressPlannerBlocks := by
  simp [Circuit.synthCrossAddressChecksSynthesisSummary,
    Circuit.crossAddressColumns, crossAddressPlannerBlocks,
    plannerBlockMultiset, SynthesisSummary.physicalRegionShapes,
    SynthesisSummary.ofRegion,
    RegionSynthesisSummary.toRegionShapeSummary,
    RegionShapeSummary.withoutSelectors, physicalColumns,
    RegionShapeSummary.normalized, plannerShape,
    sortRegionColumns, List.insertionSort,
    RegionColumn.lt, RegionColumn.ordKey, RegionColumn.kindRank,
    actionConfig, Circuit.configure, Circuit.configureBase,
    Circuit.configureChips, Circuit.configureShared,
    Circuit.configureAdvices, Circuit.configureAdviceEqualitiesLow,
    Circuit.configureAdviceEqualitiesHigh, Circuit.configureEqualities,
    Circuit.configureLagrange, AddChip.configure, Ecc.configure,
    LookupRangeCheck.configure, Poseidon.configure,
    Sinsemilla.HashPiece.configure, Sinsemilla.Merkle.configure,
    CondSwap.configure, Ecc.Add.add, Ecc.AddIncomplete.add,
    Ecc.Mul.configure, Ecc.MulFixed.BaseFieldElem.configure,
    Ecc.MulFixed.FullWidth.configure, Ecc.MulFixed.Short.configure,
    Ecc.MulFixed.configure, Ecc.WitnessPoint.configure,
    Ecc.MulComplete.configure, Ecc.MulIncomplete.configure,
    Ecc.MulOverflow.configure, Sinsemilla.Merkle.Gate.configure,
    lookupTableColumn, Configure.run_fst, keygen_norm]
  decide

private theorem shortPhysicalShapes :
    (Ecc.MulFixed.Short.circuitSynthesisSummary
      actionConfig.eccConfig.mulFixedShort).physicalRegionShapes.map
        RegionShapeSummary.normalized =
      [plannerShape [0,1,2,3,4,5] 23 [3,4,5,6,7,8,9,10,11],
        plannerShape [0,1,2,3,4,5,6,7,8] 2] := by
  simp only [Ecc.MulFixed.Short.circuitSynthesisSummary,
    Ecc.MulFixed.Short.innerRegionSynthesisSummary,
    Ecc.MulFixed.Short.mswRegionSynthesisSummary,
    Ecc.MulFixed.fixedConstantsLoopSynthesisSummary,
    Ecc.MulFixed.windowChainSynthesisSummary,
    Ecc.MulFixed.processWindowSynthesisSummary,
    DecomposeRunningSum.copyDecomposeSynthesisSummary,
    DecomposeRunningSum.assignLoopSynthesisSummary,
    DecomposeRunningSum.enableLoopSynthesisSummary,
    Ecc.MulFixed.windowStepColumns,
    Ecc.AddIncomplete.synthesisSummary, RegionSynthesisSummary.combine,
    RegionSynthesisSummary.repeatColumns, RegionSynthesisSummary.ofColumns,
    SynthesisSummary.physicalRegionShapes,
    SynthesisSummary.combine_regionShapes,
    SynthesisSummary.ofRegion_regionShapes]
  rw [show actionConfig.eccConfig.mulFixedShort.superConfig.runningSumConfig.z.index = 4 by rfl,
    show (actionConfig.eccConfig.mulFixedShort.superConfig.lagrangeCoeffs 0).index = 3 by rfl,
    show (actionConfig.eccConfig.mulFixedShort.superConfig.lagrangeCoeffs 1).index = 4 by rfl,
    show (actionConfig.eccConfig.mulFixedShort.superConfig.lagrangeCoeffs 2).index = 5 by rfl,
    show (actionConfig.eccConfig.mulFixedShort.superConfig.lagrangeCoeffs 3).index = 6 by rfl,
    show (actionConfig.eccConfig.mulFixedShort.superConfig.lagrangeCoeffs 4).index = 7 by rfl,
    show (actionConfig.eccConfig.mulFixedShort.superConfig.lagrangeCoeffs 5).index = 8 by rfl,
    show (actionConfig.eccConfig.mulFixedShort.superConfig.lagrangeCoeffs 6).index = 9 by rfl,
    show (actionConfig.eccConfig.mulFixedShort.superConfig.lagrangeCoeffs 7).index = 10 by rfl,
    show actionConfig.eccConfig.mulFixedShort.superConfig.window.index = 4 by rfl,
    show actionConfig.eccConfig.mulFixedShort.superConfig.u.index = 5 by rfl,
    show actionConfig.eccConfig.mulFixedShort.superConfig.fixedZ.index = 11 by rfl,
    show actionConfig.eccConfig.mulFixedShort.superConfig.addConfig.xP.index = 0 by rfl,
    show actionConfig.eccConfig.mulFixedShort.superConfig.addConfig.yP.index = 1 by rfl,
    show actionConfig.eccConfig.mulFixedShort.superConfig.runningSumConfig.qRangeCheck.index = 18 by rfl,
    show actionConfig.eccConfig.mulFixedShort.qMulFixedShort.index = 20 by rfl,
    show actionConfig.eccConfig.mulFixedShort.superConfig.addIncompleteConfig.qAddIncomplete.index = 7 by rfl,
    show actionConfig.eccConfig.mulFixedShort.superConfig.addIncompleteConfig.xP.index = 0 by rfl,
    show actionConfig.eccConfig.mulFixedShort.superConfig.addIncompleteConfig.yP.index = 1 by rfl,
    show actionConfig.eccConfig.mulFixedShort.superConfig.addIncompleteConfig.xQR.index = 2 by rfl,
    show actionConfig.eccConfig.mulFixedShort.superConfig.addIncompleteConfig.yQR.index = 3 by rfl]
  simp [RegionShapeSummary.normalized, unionColumns, addColumn,
    sortRegionColumns, RegionColumn.lt, RegionColumn.ordKey,
    RegionColumn.kindRank, plannerShape]
  decide

set_option maxRecDepth 10000 in
private theorem fullWidthPhysicalShapes :
    (Ecc.MulFixed.FullWidth.circuitSynthesisSummary
      actionConfig.eccConfig.mulFixedFull).physicalRegionShapes.map
        RegionShapeSummary.normalized =
      [plannerShape [0,1,2,3,4,5] 85 [3,4,5,6,7,8,9,10,11],
        plannerShape [0,1,2,3,4,5,6,7,8] 2] := by
  simp only [Ecc.MulFixed.FullWidth.circuitSynthesisSummary,
    Ecc.MulFixed.FullWidth.innerRegionSynthesisSummary,
    Ecc.MulFixed.FullWidth.witnessScalarLoopSynthesisSummary,
    Ecc.MulFixed.fixedConstantsLoopSynthesisSummary,
    Ecc.MulFixed.windowChainSynthesisSummary,
    Ecc.MulFixed.processWindowSynthesisSummary,
    Ecc.MulFixed.windowStepColumns,
    Ecc.AddIncomplete.synthesisSummary, Ecc.Add.synthesisSummary,
    RegionSynthesisSummary.combine, RegionSynthesisSummary.repeatColumns,
    RegionSynthesisSummary.ofColumns,
    SynthesisSummary.physicalRegionShapes,
    SynthesisSummary.combine_regionShapes,
    SynthesisSummary.ofRegion_regionShapes]
  rw [show (actionConfig.eccConfig.mulFixedFull.superConfig.lagrangeCoeffs 0).index = 3 by rfl,
    show (actionConfig.eccConfig.mulFixedFull.superConfig.lagrangeCoeffs 1).index = 4 by rfl,
    show (actionConfig.eccConfig.mulFixedFull.superConfig.lagrangeCoeffs 2).index = 5 by rfl,
    show (actionConfig.eccConfig.mulFixedFull.superConfig.lagrangeCoeffs 3).index = 6 by rfl,
    show (actionConfig.eccConfig.mulFixedFull.superConfig.lagrangeCoeffs 4).index = 7 by rfl,
    show (actionConfig.eccConfig.mulFixedFull.superConfig.lagrangeCoeffs 5).index = 8 by rfl,
    show (actionConfig.eccConfig.mulFixedFull.superConfig.lagrangeCoeffs 6).index = 9 by rfl,
    show (actionConfig.eccConfig.mulFixedFull.superConfig.lagrangeCoeffs 7).index = 10 by rfl,
    show actionConfig.eccConfig.mulFixedFull.superConfig.window.index = 4 by rfl,
    show actionConfig.eccConfig.mulFixedFull.superConfig.u.index = 5 by rfl,
    show actionConfig.eccConfig.mulFixedFull.superConfig.fixedZ.index = 11 by rfl,
    show actionConfig.eccConfig.mulFixedFull.superConfig.addConfig.xP.index = 0 by rfl,
    show actionConfig.eccConfig.mulFixedFull.superConfig.addConfig.yP.index = 1 by rfl,
    show actionConfig.eccConfig.mulFixedFull.qMulFixedFull.index = 19 by rfl,
    show actionConfig.eccConfig.mulFixedFull.superConfig.addIncompleteConfig.qAddIncomplete.index = 7 by rfl,
    show actionConfig.eccConfig.mulFixedFull.superConfig.addIncompleteConfig.xP.index = 0 by rfl,
    show actionConfig.eccConfig.mulFixedFull.superConfig.addIncompleteConfig.yP.index = 1 by rfl,
    show actionConfig.eccConfig.mulFixedFull.superConfig.addIncompleteConfig.xQR.index = 2 by rfl,
    show actionConfig.eccConfig.mulFixedFull.superConfig.addIncompleteConfig.yQR.index = 3 by rfl,
    show actionConfig.eccConfig.mulFixedFull.superConfig.addConfig.qAdd.index = 8 by rfl,
    show actionConfig.eccConfig.mulFixedFull.superConfig.addConfig.xQR.index = 2 by rfl,
    show actionConfig.eccConfig.mulFixedFull.superConfig.addConfig.yQR.index = 3 by rfl,
    show actionConfig.eccConfig.mulFixedFull.superConfig.addConfig.lambda.index = 4 by rfl,
    show actionConfig.eccConfig.mulFixedFull.superConfig.addConfig.alpha.index = 5 by rfl,
    show actionConfig.eccConfig.mulFixedFull.superConfig.addConfig.beta.index = 6 by rfl,
    show actionConfig.eccConfig.mulFixedFull.superConfig.addConfig.gamma.index = 7 by rfl,
    show actionConfig.eccConfig.mulFixedFull.superConfig.addConfig.delta.index = 8 by rfl]
  simp [RegionShapeSummary.normalized, unionColumns, addColumn,
    sortRegionColumns, RegionColumn.lt, RegionColumn.ordKey,
    RegionColumn.kindRank, plannerShape]
  decide

set_option maxRecDepth 10000 in
private theorem baseFieldPhysicalShapes :
    (Ecc.MulFixed.BaseFieldElem.circuitSynthesisSummary
      actionConfig.eccConfig.mulFixedBaseField).physicalRegionShapes.map
        RegionShapeSummary.normalized =
      [plannerShape [0,1,2,3,4,5] 86 [3,4,5,6,7,8,9,10,11],
        plannerShape [0,1,2,3,4,5,6,7,8] 2,
        plannerShape [9] 14, plannerShape [6,7,8] 3] := by
  simp only [Ecc.MulFixed.BaseFieldElem.circuitSynthesisSummary,
    Ecc.MulFixed.BaseFieldElem.innerRegionSynthesisSummary,
    Ecc.MulFixed.BaseFieldElem.witnessCheck13SynthesisSummary,
    Ecc.MulFixed.BaseFieldElem.canonicityRegionSynthesisSummary,
    Ecc.MulFixed.fixedConstantsLoopSynthesisSummary,
    Ecc.MulFixed.windowChainSynthesisSummary,
    Ecc.MulFixed.processWindowSynthesisSummary,
    DecomposeRunningSum.copyDecomposeSynthesisSummary,
    DecomposeRunningSum.assignLoopSynthesisSummary,
    DecomposeRunningSum.enableLoopSynthesisSummary,
    Ecc.MulFixed.windowStepColumns,
    Ecc.AddIncomplete.synthesisSummary, Ecc.Add.synthesisSummary,
    LookupRangeCheck.witnessCheckSynthesisSummary,
    RegionSynthesisSummary.combine, RegionSynthesisSummary.repeatColumns,
    RegionSynthesisSummary.ofColumns,
    SynthesisSummary.physicalRegionShapes,
    SynthesisSummary.combine_regionShapes,
    SynthesisSummary.ofRegion_regionShapes]
  rw [show actionConfig.eccConfig.mulFixedBaseField.superConfig.runningSumConfig.z.index = 4 by rfl,
    show (actionConfig.eccConfig.mulFixedBaseField.superConfig.lagrangeCoeffs 0).index = 3 by rfl,
    show (actionConfig.eccConfig.mulFixedBaseField.superConfig.lagrangeCoeffs 1).index = 4 by rfl,
    show (actionConfig.eccConfig.mulFixedBaseField.superConfig.lagrangeCoeffs 2).index = 5 by rfl,
    show (actionConfig.eccConfig.mulFixedBaseField.superConfig.lagrangeCoeffs 3).index = 6 by rfl,
    show (actionConfig.eccConfig.mulFixedBaseField.superConfig.lagrangeCoeffs 4).index = 7 by rfl,
    show (actionConfig.eccConfig.mulFixedBaseField.superConfig.lagrangeCoeffs 5).index = 8 by rfl,
    show (actionConfig.eccConfig.mulFixedBaseField.superConfig.lagrangeCoeffs 6).index = 9 by rfl,
    show (actionConfig.eccConfig.mulFixedBaseField.superConfig.lagrangeCoeffs 7).index = 10 by rfl,
    show actionConfig.eccConfig.mulFixedBaseField.superConfig.u.index = 5 by rfl,
    show actionConfig.eccConfig.mulFixedBaseField.superConfig.fixedZ.index = 11 by rfl,
    show actionConfig.eccConfig.mulFixedBaseField.superConfig.addConfig.xP.index = 0 by rfl,
    show actionConfig.eccConfig.mulFixedBaseField.superConfig.addConfig.yP.index = 1 by rfl,
    show actionConfig.eccConfig.mulFixedBaseField.superConfig.runningSumConfig.qRangeCheck.index = 18 by rfl,
    show actionConfig.eccConfig.mulFixedBaseField.superConfig.addIncompleteConfig.qAddIncomplete.index = 7 by rfl,
    show actionConfig.eccConfig.mulFixedBaseField.superConfig.addIncompleteConfig.xP.index = 0 by rfl,
    show actionConfig.eccConfig.mulFixedBaseField.superConfig.addIncompleteConfig.yP.index = 1 by rfl,
    show actionConfig.eccConfig.mulFixedBaseField.superConfig.addIncompleteConfig.xQR.index = 2 by rfl,
    show actionConfig.eccConfig.mulFixedBaseField.superConfig.addIncompleteConfig.yQR.index = 3 by rfl]
  simp [RegionShapeSummary.normalized, unionColumns, addColumn,
    sortRegionColumns, RegionColumn.lt, RegionColumn.ordKey,
    RegionColumn.kindRank, plannerShape]
  decide

set_option maxRecDepth 10000 in
private theorem merkle1HashPhysicalShape :
    (Sinsemilla.Merkle.HashLayer.hashPhysicalShape
      actionConfig.merkle1.sinsemilla).normalized =
      plannerShape [0,1,2,3,4] 53 [3,12] := by
  simp only [Sinsemilla.Merkle.HashLayer.hashPhysicalShape_eq,
    Sinsemilla.HashToPoint.hashRegionSynthesisSummary,
    Sinsemilla.Chain.circuitSynthesisSummary,
    Sinsemilla.Chain.slotIterationSynthesisSummary,
    Sinsemilla.Chain.slotSynthesisSummary,
    Sinsemilla.HashPiece.circuitSynthesisSummary,
    Sinsemilla.HashPiece.loopSynthesisSummary,
    RegionSynthesisSummary.combine,
    RegionSynthesisSummary.ofColumns,
    RegionSynthesisSummary.toRegionShapeSummary,
    RegionShapeSummary.withoutSelectors,
    Sinsemilla.HashPiece.roundColumns]
  rw [show actionConfig.merkle1.sinsemilla.fixedYQ.index = 3 by rfl,
    show actionConfig.merkle1.sinsemilla.qS2.index = 12 by rfl,
    show actionConfig.merkle1.sinsemilla.xA.index = 0 by rfl,
    show actionConfig.merkle1.sinsemilla.bits.index = 2 by rfl,
    show actionConfig.merkle1.sinsemilla.xP.index = 1 by rfl,
    show actionConfig.merkle1.sinsemilla.lambda1.index = 3 by rfl,
    show actionConfig.merkle1.sinsemilla.lambda2.index = 4 by rfl]
  simp [RegionShapeSummary.normalized, physicalColumns, unionColumns, addColumn,
    sortRegionColumns, RegionColumn.lt, RegionColumn.ordKey,
    RegionColumn.kindRank, plannerShape]
  decide

set_option maxRecDepth 10000 in
private theorem merkle2HashPhysicalShape :
    (Sinsemilla.Merkle.HashLayer.hashPhysicalShape
      actionConfig.merkle2.sinsemilla).normalized =
      plannerShape [5,6,7,8,9] 53 [4,13] := by
  simp only [Sinsemilla.Merkle.HashLayer.hashPhysicalShape_eq,
    Sinsemilla.HashToPoint.hashRegionSynthesisSummary,
    Sinsemilla.Chain.circuitSynthesisSummary,
    Sinsemilla.Chain.slotIterationSynthesisSummary,
    Sinsemilla.Chain.slotSynthesisSummary,
    Sinsemilla.HashPiece.circuitSynthesisSummary,
    Sinsemilla.HashPiece.loopSynthesisSummary,
    RegionSynthesisSummary.combine,
    RegionSynthesisSummary.ofColumns,
    RegionSynthesisSummary.toRegionShapeSummary,
    RegionShapeSummary.withoutSelectors,
    Sinsemilla.HashPiece.roundColumns]
  rw [show actionConfig.merkle2.sinsemilla.fixedYQ.index = 4 by rfl,
    show actionConfig.merkle2.sinsemilla.qS2.index = 13 by rfl,
    show actionConfig.merkle2.sinsemilla.xA.index = 5 by rfl,
    show actionConfig.merkle2.sinsemilla.bits.index = 7 by rfl,
    show actionConfig.merkle2.sinsemilla.xP.index = 6 by rfl,
    show actionConfig.merkle2.sinsemilla.lambda1.index = 8 by rfl,
    show actionConfig.merkle2.sinsemilla.lambda2.index = 9 by rfl]
  simp [RegionShapeSummary.normalized, physicalColumns, unionColumns, addColumn,
    sortRegionColumns, RegionColumn.lt, RegionColumn.ordKey,
    RegionColumn.kindRank, plannerShape]
  decide

set_option maxRecDepth 10000 in
private theorem noteCommitOldHashPhysicalShape :
    (Sinsemilla.HashToPoint.hashPhysicalShape NoteCommit.Main.ns
      actionConfig.sinsemilla1).normalized =
        plannerShape [0,1,2,3,4] 110 [3,12] := by
  simp only [Sinsemilla.HashToPoint.hashPhysicalShape_eq,
    Sinsemilla.HashToPoint.hashRegionSynthesisSummary,
    Sinsemilla.Chain.circuitSynthesisSummary,
    Sinsemilla.Chain.slotIterationSynthesisSummary,
    Sinsemilla.Chain.slotSynthesisSummary,
    Sinsemilla.HashPiece.circuitSynthesisSummary,
    Sinsemilla.HashPiece.loopSynthesisSummary,
    RegionSynthesisSummary.combine,
    RegionSynthesisSummary.ofColumns,
    RegionSynthesisSummary.toRegionShapeSummary,
    RegionShapeSummary.withoutSelectors,
    Sinsemilla.HashPiece.roundColumns]
  rw [show actionConfig.sinsemilla1.fixedYQ.index = 3 by rfl,
    show actionConfig.sinsemilla1.qS2.index = 12 by rfl,
    show actionConfig.sinsemilla1.xA.index = 0 by rfl,
    show actionConfig.sinsemilla1.bits.index = 2 by rfl,
    show actionConfig.sinsemilla1.xP.index = 1 by rfl,
    show actionConfig.sinsemilla1.lambda1.index = 3 by rfl,
    show actionConfig.sinsemilla1.lambda2.index = 4 by rfl]
  simp [NoteCommit.Main.ns, Sinsemilla.Chain.prefixRows,
    RegionShapeSummary.normalized, physicalColumns, unionColumns, addColumn,
    sortRegionColumns, RegionColumn.lt, RegionColumn.ordKey,
    RegionColumn.kindRank, plannerShape]
  decide

set_option maxRecDepth 10000 in
private theorem noteCommitNewHashPhysicalShape :
    (Sinsemilla.HashToPoint.hashPhysicalShape NoteCommit.Main.ns
      actionConfig.sinsemilla2).normalized =
        plannerShape [5,6,7,8,9] 110 [4,13] := by
  simp only [Sinsemilla.HashToPoint.hashPhysicalShape_eq,
    Sinsemilla.HashToPoint.hashRegionSynthesisSummary,
    Sinsemilla.Chain.circuitSynthesisSummary,
    Sinsemilla.Chain.slotIterationSynthesisSummary,
    Sinsemilla.Chain.slotSynthesisSummary,
    Sinsemilla.HashPiece.circuitSynthesisSummary,
    Sinsemilla.HashPiece.loopSynthesisSummary,
    RegionSynthesisSummary.combine,
    RegionSynthesisSummary.ofColumns,
    RegionSynthesisSummary.toRegionShapeSummary,
    RegionShapeSummary.withoutSelectors,
    Sinsemilla.HashPiece.roundColumns]
  rw [show actionConfig.sinsemilla2.fixedYQ.index = 4 by rfl,
    show actionConfig.sinsemilla2.qS2.index = 13 by rfl,
    show actionConfig.sinsemilla2.xA.index = 5 by rfl,
    show actionConfig.sinsemilla2.bits.index = 7 by rfl,
    show actionConfig.sinsemilla2.xP.index = 6 by rfl,
    show actionConfig.sinsemilla2.lambda1.index = 8 by rfl,
    show actionConfig.sinsemilla2.lambda2.index = 9 by rfl]
  simp [NoteCommit.Main.ns, Sinsemilla.Chain.prefixRows,
    RegionShapeSummary.normalized, physicalColumns, unionColumns, addColumn,
    sortRegionColumns, RegionColumn.lt, RegionColumn.ordKey,
    RegionColumn.kindRank, plannerShape]
  decide

set_option maxRecDepth 10000 in
private theorem commitIvkHashPhysicalShape :
    (Sinsemilla.HashToPoint.hashPhysicalShape CommitIvk.Main.ns
      actionConfig.sinsemilla1).normalized =
        plannerShape [0,1,2,3,4] 52 [3,12] := by
  simp only [Sinsemilla.HashToPoint.hashPhysicalShape_eq,
    Sinsemilla.HashToPoint.hashRegionSynthesisSummary,
    Sinsemilla.Chain.circuitSynthesisSummary,
    Sinsemilla.Chain.slotIterationSynthesisSummary,
    Sinsemilla.Chain.slotSynthesisSummary,
    Sinsemilla.HashPiece.circuitSynthesisSummary,
    Sinsemilla.HashPiece.loopSynthesisSummary,
    RegionSynthesisSummary.combine,
    RegionSynthesisSummary.ofColumns,
    RegionSynthesisSummary.toRegionShapeSummary,
    RegionShapeSummary.withoutSelectors,
    Sinsemilla.HashPiece.roundColumns]
  rw [show actionConfig.sinsemilla1.fixedYQ.index = 3 by rfl,
    show actionConfig.sinsemilla1.qS2.index = 12 by rfl,
    show actionConfig.sinsemilla1.xA.index = 0 by rfl,
    show actionConfig.sinsemilla1.bits.index = 2 by rfl,
    show actionConfig.sinsemilla1.xP.index = 1 by rfl,
    show actionConfig.sinsemilla1.lambda1.index = 3 by rfl,
    show actionConfig.sinsemilla1.lambda2.index = 4 by rfl]
  simp [CommitIvk.Main.ns, Sinsemilla.Chain.prefixRows,
    RegionShapeSummary.normalized, physicalColumns, unionColumns, addColumn,
    sortRegionColumns, RegionColumn.lt, RegionColumn.ordKey,
    RegionColumn.kindRank, plannerShape]
  decide

set_option maxRecDepth 10000 in
private theorem variableBaseMulPhysicalShape :
    ({ columns := physicalColumns
          (Ecc.Mul.mainCircuitSynthesisSummary actionConfig.eccConfig.mul).columns
       rowCount :=
          (Ecc.Mul.mainCircuitSynthesisSummary actionConfig.eccConfig.mul).rowCount } :
      RegionShapeSummary).normalized =
      plannerShape [0,1,2,3,4,5,6,7,8,9] 137 := by
  simp [Ecc.Mul.mainCircuitSynthesisSummary,
    Ecc.MulComplete.circuitSynthesisSummary,
    Ecc.MulIncomplete.doubleAndAddSynthesisSummary,
    Ecc.MulIncomplete.loopSynthesisSummary,
    Ecc.Add.synthesisSummary,
    RegionSynthesisSummary.combine, RegionSynthesisSummary.ofColumns,
    RegionShapeSummary.normalized,
    physicalColumns, unionColumns, addColumn, sortRegionColumns,
    RegionColumn.lt, RegionColumn.ordKey, RegionColumn.kindRank,
    plannerShape, actionConfig, Circuit.configure,
    Circuit.configureBase, Circuit.configureChips, Circuit.configureShared,
    Circuit.configureAdvices, Circuit.configureAdviceEqualitiesLow,
    Circuit.configureAdviceEqualitiesHigh, Circuit.configureEqualities,
    Circuit.configureLagrange, AddChip.configure, Ecc.configure,
    LookupRangeCheck.configure, Poseidon.configure,
    Sinsemilla.HashPiece.configure, Sinsemilla.Merkle.configure,
    CondSwap.configure, Ecc.Add.add, Ecc.AddIncomplete.add,
    Ecc.Mul.configure, Ecc.MulFixed.BaseFieldElem.configure,
    Ecc.MulFixed.FullWidth.configure, Ecc.MulFixed.Short.configure,
    Ecc.MulFixed.configure, Ecc.WitnessPoint.configure,
    Ecc.MulComplete.configure, Ecc.MulIncomplete.configure,
    Ecc.MulOverflow.configure, Sinsemilla.Merkle.Gate.configure,
    lookupTableColumn, Configure.run_fst, keygen_norm]
  decide

set_option maxRecDepth 10000 in
private theorem checksPlannerBlocks_correct :
    ((Circuit.synthChecksSynthesisSummary actionConfig).physicalRegionShapes.map
      RegionShapeSummary.normalized : Multiset RegionShapeSummary) =
        plannerBlockMultiset checksPlannerBlocks := by
  let merkle1Shape := Sinsemilla.Merkle.HashLayer.hashPhysicalShape
    actionConfig.merkle1.sinsemilla
  have hmerkle1Shape :
      Sinsemilla.Merkle.HashLayer.hashPhysicalShape
        actionConfig.merkle1.sinsemilla = merkle1Shape := rfl
  clear_value merkle1Shape
  let merkle2Shape := Sinsemilla.Merkle.HashLayer.hashPhysicalShape
    actionConfig.merkle2.sinsemilla
  have hmerkle2Shape :
      Sinsemilla.Merkle.HashLayer.hashPhysicalShape
        actionConfig.merkle2.sinsemilla = merkle2Shape := rfl
  clear_value merkle2Shape
  have hmerkle1Normalized : merkle1Shape.normalized =
      plannerShape [0,1,2,3,4] 53 [3,12] := by
    rw [← hmerkle1Shape]
    exact merkle1HashPhysicalShape
  have hmerkle2Normalized : merkle2Shape.normalized =
      plannerShape [5,6,7,8,9] 53 [4,13] := by
    rw [← hmerkle2Shape]
    exact merkle2HashPhysicalShape
  let ivkHashShape := Sinsemilla.HashToPoint.hashPhysicalShape
    CommitIvk.Main.ns actionConfig.sinsemilla1
  have hivkHashShape :
      Sinsemilla.HashToPoint.hashPhysicalShape CommitIvk.Main.ns
        actionConfig.sinsemilla1 = ivkHashShape := rfl
  clear_value ivkHashShape
  have hivkHashNormalized : ivkHashShape.normalized =
      plannerShape [0,1,2,3,4] 52 [3,12] := by
    rw [← hivkHashShape]
    exact commitIvkHashPhysicalShape
  rw [Circuit.synthChecksSynthesisSummary_physicalRegionShapes]
  unfold checksPlannerBlocks plannerBlockMultiset
  simp only [List.flatMap_cons, List.flatMap_nil]
  rw [Sinsemilla.Merkle.CalculateRoot.synthesisSummary_physicalShapes_eq,
    Sinsemilla.Merkle.CalculateRoot.synthesisSummary_physicalShapes_eq,
    Sinsemilla.Merkle.Layer.synthesisSummary_physicalShapes_eq,
    Sinsemilla.Merkle.Layer.synthesisSummary_physicalShapes_eq,
    Sinsemilla.Merkle.HashLayer.synthesisSummary_physicalShapes_eq,
    Sinsemilla.Merkle.HashLayer.synthesisSummary_physicalShapes_eq,
    hmerkle1Shape, hmerkle2Shape]
  simp only [synthesis_summary_norm, List.map_append, List.map_nil]
  simp only [
    ValueCommit.synthesisSummary, DeriveNullifier.synthesisSummary,
    SpendAuthority.synthesisSummary, CommitIvk.Main.synthesisSummary,
    AddressIntegrity.synthesisSummary,
    CommitIvk.Main.synthPiecesSynthesisSummary,
    CommitIvk.Canonicity.circuitSynthesisSummary,
    Sinsemilla.CommitDomain.commitSynthesisSummary,
    Poseidon.hashSynthesisSummary, Ecc.Mul.mulSynthesisSummary,
    Ecc.Add.synthesisSummary, CommitIvk.synthesisSummary,
    LookupRangeCheck.witnessCheckSynthesisSummary,
    Ecc.MulOverflow.circuitSynthesisSummary,
    Poseidon.addInputRegionSynthesisSummary,
    Poseidon.initRegionSynthesisSummary,
    Poseidon.permuteSynthesisSummary,
    Sinsemilla.HashToPoint.hashCircuitSynthesisSummary_physicalShapes_eq,
    hivkHashShape,
    RegionSynthesisSummary.withSelectorActivations_toRegionShapeSummary,
    SynthesisSummary.combine_physicalRegionShapes,
    SynthesisSummary.ofRegion_physicalRegionShapes,
    SynthesisSummary.foldr_combine_physicalRegionShapes,
    Circuit.loadPrivateSynthesisSummary,
    Sinsemilla.Merkle.Gate.synthesisSummary,
    LookupRangeCheck.witnessShortCheckSynthesisSummary,
    Sinsemilla.HashToPoint.witnessMessagePieceSynthesisSummary,
    List.map_append]
  rw [shortPhysicalShapes, fullWidthPhysicalShapes,
    baseFieldPhysicalShapes]
  simp only [← Multiset.map_coe, ← Multiset.coe_add,
    Multiset.map_add, Multiset.coe_flatten_replicate,
    Multiset.map_nsmul, Multiset.coe_singleton, Multiset.map_singleton]
  simp only [AddChip.synthesisSummary,
    RegionSynthesisSummary.ofColumns,
    RegionSynthesisSummary.toRegionShapeSummary,
    RegionShapeSummary.withoutSelectors, unionColumns]
  simp only [variableBaseMulPhysicalShape]
  simp [Ecc.WitnessPoint.pointNonIdSynthesisSummary,
    RegionSynthesisSummary.combine,
    actionConfig, Circuit.configure,
    Circuit.configureBase, Circuit.configureChips, Circuit.configureShared,
    Circuit.configureAdvices, Circuit.configureAdviceEqualitiesLow,
    Circuit.configureAdviceEqualitiesHigh, Circuit.configureEqualities,
    Circuit.configureLagrange, AddChip.configure, Ecc.configure,
    CommitIvk.configure, LookupRangeCheck.configure, Poseidon.configure,
    Sinsemilla.HashPiece.configure, Sinsemilla.Merkle.configure,
    CondSwap.configure, Ecc.Add.add, Ecc.AddIncomplete.add,
    Ecc.Mul.configure, Ecc.MulFixed.BaseFieldElem.configure,
    Ecc.MulFixed.FullWidth.configure, Ecc.MulFixed.Short.configure,
    Ecc.MulFixed.configure, Ecc.WitnessPoint.configure,
    Ecc.MulComplete.configure, Ecc.MulIncomplete.configure,
    Ecc.MulOverflow.configure, Sinsemilla.Merkle.Gate.configure,
    lookupTableColumn, Configure.run_fst, keygen_norm]
  simp only [hmerkle1Normalized, hmerkle2Normalized,
    hivkHashNormalized]
  simp [plannerShape, synthesis_summary_norm,
    SynthesisSummary.physicalRegionShapes,
    SynthesisSummary.ofRegion,
    LookupRangeCheck.copyCheckSynthesisSummary,
    LookupRangeCheck.shortRangeCheckSynthesisSummary,
    LookupRangeCheck.rangeCheckSynthesisSummary,
    Ecc.MulOverflow.numWords,
    RegionSynthesisSummary.ofColumns,
    RegionSynthesisSummary.toRegionShapeSummary,
    RegionShapeSummary.withoutSelectors,
    RegionShapeSummary.normalized, physicalColumns, unionColumns,
    addColumn, sortRegionColumns, List.insertionSort, List.orderedInsert,
    RegionColumn.lt, RegionColumn.ordKey, RegionColumn.kindRank]
  simp only [listCoe_cons, Multiset.coe_nil]
  letI : DecidableEq RegionShapeSummary := Classical.decEq _
  rw [Multiset.ext]
  intro summary
  simp only [Multiset.count_cons, Multiset.count_add,
    Multiset.count_nsmul, Multiset.count_singleton,
    Multiset.count_zero]
  ring_nf

set_option maxRecDepth 10000 in
private theorem notesPlannerBlocks_correct :
    ((Circuit.synthNotesSynthesisSummary actionConfig).physicalRegionShapes.map
      RegionShapeSummary.normalized : Multiset RegionShapeSummary) =
        plannerBlockMultiset notesPlannerBlocks := by
  let oldHashShape :=
    Sinsemilla.HashToPoint.hashPhysicalShape NoteCommit.Main.ns
      actionConfig.sinsemilla1
  have holdHashShape :
      Sinsemilla.HashToPoint.hashPhysicalShape NoteCommit.Main.ns
        actionConfig.sinsemilla1 = oldHashShape := rfl
  clear_value oldHashShape
  let newHashShape :=
    Sinsemilla.HashToPoint.hashPhysicalShape NoteCommit.Main.ns
      actionConfig.sinsemilla2
  have hnewHashShape :
      Sinsemilla.HashToPoint.hashPhysicalShape NoteCommit.Main.ns
        actionConfig.sinsemilla2 = newHashShape := rfl
  clear_value newHashShape
  have holdHashNormalized : oldHashShape.normalized =
      plannerShape [0,1,2,3,4] 110 [3,12] := by
    rw [← holdHashShape]
    exact noteCommitOldHashPhysicalShape
  have hnewHashNormalized : newHashShape.normalized =
      plannerShape [5,6,7,8,9] 110 [4,13] := by
    rw [← hnewHashShape]
    exact noteCommitNewHashPhysicalShape
  rw [Circuit.synthNotesSynthesisSummary_physicalRegionShapes]
  unfold notesPlannerBlocks plannerBlockMultiset
  simp only [List.flatMap_cons, List.flatMap_nil, synthesis_summary_norm,
    NoteCommit.Main.synthesisSummary,
    NoteCommit.Main.synthPiecesSynthesisSummary,
    NoteCommit.Main.synthChecksSynthesisSummary,
    NoteCommit.Main.synthGatesSynthesisSummary,
    NoteCommit.DecomposeB.synthesisSummary,
    NoteCommit.DecomposeD.synthesisSummary,
    NoteCommit.DecomposeE.synthesisSummary,
    NoteCommit.DecomposeG.synthesisSummary,
    NoteCommit.DecomposeH.synthesisSummary,
    NoteCommit.GdCanonicity.synthesisSummary,
    NoteCommit.PkdCanonicity.synthesisSummary,
    NoteCommit.RhoCanonicity.synthesisSummary,
    NoteCommit.ValueCanonicity.synthesisSummary,
    NoteCommit.YCanonicityCheck.synthesisSummary,
    NoteCommit.YCanonicity.synthesisSummary,
    NoteCommit.PsiCanonicity.synthesisSummary,
    Circuit.orchardChecksRegionSynthesisSummary,
    Circuit.orchardChecksSynthesisSummary,
    Sinsemilla.CommitDomain.commitSynthesisSummary,
    Ecc.Add.synthesisSummary,
    LookupRangeCheck.witnessCheckSynthesisSummary,
    LookupRangeCheck.witnessShortCheckSynthesisSummary,
    LookupRangeCheck.witnessCheckDecomposedSynthesisSummary,
    LookupRangeCheck.shortRangeCheckSynthesisSummary,
    LookupRangeCheck.rangeCheckSynthesisSummary,
    LookupRangeCheck.rangeCheckAtDecomposedSynthesisSummary,
    RegionSynthesisSummary.withSelectorActivations_toRegionShapeSummary,
    Sinsemilla.HashToPoint.hashCircuitSynthesisSummary_physicalShapes_eq,
    holdHashShape, hnewHashShape,
    SynthesisSummary.combine_physicalRegionShapes,
    SynthesisSummary.ofRegion_physicalRegionShapes,
    SynthesisSummary.foldr_combine_physicalRegionShapes,
    Circuit.loadPrivateSynthesisSummary,
    Ecc.WitnessPoint.pointNonIdSynthesisSummary,
    Sinsemilla.HashToPoint.witnessMessagePieceSynthesisSummary,
    List.map_append]
  rw [fullWidthPhysicalShapes]
  simp only [← Multiset.map_coe, ← Multiset.coe_add,
    Multiset.coe_singleton, Multiset.map_singleton]
  simp only [
    RegionSynthesisSummary.combine_columns,
    RegionSynthesisSummary.combine_rowCount,
    RegionSynthesisSummary.ofColumns,
    RegionSynthesisSummary.toRegionShapeSummary,
    RegionShapeSummary.withoutSelectors, unionColumns]
  simp [synthesis_summary_norm,
    actionConfig, Circuit.configure,
    Circuit.configureBase, Circuit.configureChips, Circuit.configureShared,
    Circuit.configureAdvices, Circuit.configureAdviceEqualitiesLow,
    Circuit.configureAdviceEqualitiesHigh, Circuit.configureEqualities,
    Circuit.configureLagrange, AddChip.configure, Ecc.configure,
    NoteCommit.configure, NoteCommit.DecomposeB.configure,
    NoteCommit.DecomposeD.configure, NoteCommit.DecomposeE.configure,
    NoteCommit.DecomposeG.configure, NoteCommit.DecomposeH.configure,
    NoteCommit.GdCanonicity.configure, NoteCommit.PkdCanonicity.configure,
    NoteCommit.PsiCanonicity.configure, NoteCommit.RhoCanonicity.configure,
    NoteCommit.ValueCanonicity.configure, NoteCommit.YCanonicity.configure,
    LookupRangeCheck.configure, Poseidon.configure,
    Sinsemilla.HashPiece.configure, Sinsemilla.Merkle.configure,
    CondSwap.configure, Ecc.Add.add, Ecc.AddIncomplete.add,
    Ecc.Mul.configure, Ecc.MulFixed.BaseFieldElem.configure,
    Ecc.MulFixed.FullWidth.configure, Ecc.MulFixed.Short.configure,
    Ecc.MulFixed.configure, Ecc.WitnessPoint.configure,
    Ecc.MulComplete.configure, Ecc.MulIncomplete.configure,
    Ecc.MulOverflow.configure, Sinsemilla.Merkle.Gate.configure,
    lookupTableColumn, Configure.run_fst, keygen_norm]
  simp only [holdHashNormalized, hnewHashNormalized]
  simp [plannerShape,
    RegionShapeSummary.normalized, physicalColumns,
    addColumn, sortRegionColumns, List.insertionSort, List.orderedInsert,
    RegionColumn.lt, RegionColumn.ordKey, RegionColumn.kindRank]
  simp only [listCoe_cons, Multiset.coe_nil]
  letI : DecidableEq RegionShapeSummary := Classical.decEq _
  rw [Multiset.ext]
  intro summary
  simp only [Multiset.count_cons, Multiset.count_add,
    Multiset.count_nsmul, Multiset.count_singleton,
    Multiset.count_zero]
  ring

set_option maxRecDepth 10000 in
private theorem actionOwnerPlannerBlocks_eq :
    plannerBlockMultiset witnessPlannerBlocks +
        plannerBlockMultiset checksPlannerBlocks +
        plannerBlockMultiset notesPlannerBlocks +
        plannerBlockMultiset crossAddressPlannerBlocks =
      plannerBlockMultiset actionPlannerBlocks := by
  unfold witnessPlannerBlocks checksPlannerBlocks notesPlannerBlocks
    crossAddressPlannerBlocks actionPlannerBlocks plannerBlockMultiset
  simp only [List.foldr_cons, List.foldr_nil]
  abel

set_option maxRecDepth 10000 in
private theorem actionCanonicalPlannerSummaries_normalized :
    (actionCanonicalPlannerSummaries.map RegionShapeSummary.normalized :
      Multiset RegionShapeSummary) =
      plannerBlockMultiset actionPlannerBlocks := by
  rw [show actionCanonicalPlannerSummaries =
      expandPlannerBlocks actionPlannerBlocks by rfl,
    ← Multiset.map_coe, coe_expandPlannerBlocks]
  unfold actionPlannerBlocks plannerBlockMultiset
  simp only [List.foldr_cons, List.foldr_nil, Multiset.map_add,
    Multiset.map_nsmul, Multiset.map_singleton, Multiset.map_zero]
  simp [plannerShape, RegionShapeSummary.normalized, sortRegionColumns,
    List.insertionSort, RegionColumn.lt,
    RegionColumn.ordKey, RegionColumn.kindRank]

/-- The Action circuit's reduced synthesis summary contains exactly the compact
planner blocks, modulo the irrelevant order of columns within each region. -/
theorem actionPlannerSummaries_normalized_multiset :
    (actionPlannerSummaries.map RegionShapeSummary.normalized :
      Multiset RegionShapeSummary) =
    (actionCanonicalPlannerSummaries.map RegionShapeSummary.normalized :
      Multiset RegionShapeSummary) := by
  rw [actionPlannerSummaries_eq_physicalRegionShapes,
    show actionSynthesisSummary =
      Circuit.mainPostSynthesisSummary actionConfig by rfl,
    Circuit.mainPostSynthesisSummary_physicalRegionShapes]
  simp only [List.map_append, ← Multiset.coe_add]
  rw [witnessPlannerBlocks_correct, checksPlannerBlocks_correct,
    notesPlannerBlocks_correct, crossAddressPlannerBlocks_correct,
    actionOwnerPlannerBlocks_eq,
    actionCanonicalPlannerSummaries_normalized]

private theorem actionSortedPlannerSummaries_normalized_perm :
    (actionSortedPlannerSummaries.map RegionShapeSummary.normalized).Perm
      (actionCanonicalPlannerSummaries.map
        RegionShapeSummary.normalized) := by
  have hsorted : actionSortedPlannerSummaries.Perm
      actionPlannerSummaries := by
    have hperm :=
      V1.sortedSummaryOrder_perm_synthesisSummary actionOperations |>.map
        RegionShapeSummary.withoutSelectors
    simpa only [actionSortedPlannerSummaries, actionPlannerSummaries,
      actionSynthesisSummary_eq_operations] using hperm
  have hcanonical :
      (actionPlannerSummaries.map RegionShapeSummary.normalized).Perm
        (actionCanonicalPlannerSummaries.map
          RegionShapeSummary.normalized) :=
    Multiset.coe_eq_coe.mp actionPlannerSummaries_normalized_multiset
  exact (hsorted.map RegionShapeSummary.normalized).trans hcanonical

private theorem normalized_filter_perm
    (predicate : RegionShapeSummary → Bool)
    (hstable : ∀ summary,
      predicate summary.normalized = predicate summary) :
    ((actionSortedPlannerSummaries.filter predicate).map
        RegionShapeSummary.normalized).Perm
      ((actionCanonicalPlannerSummaries.filter predicate).map
        RegionShapeSummary.normalized) := by
  have hfiltered := actionSortedPlannerSummaries_normalized_perm.filter predicate
  rw [List.filter_map, List.filter_map] at hfiltered
  have hsimplify (summaries : List RegionShapeSummary) :
      summaries.filter (predicate ∘ RegionShapeSummary.normalized) =
        summaries.filter predicate := by
    apply List.filter_congr
    intro summary _
    exact hstable summary
  rw [hsimplify, hsimplify] at hfiltered
  exact hfiltered

private theorem plannerAbove8_normalized_perm :
    ((plannerAbove8 actionSortedPlannerSummaries).map
        RegionShapeSummary.normalized).Perm
      ((plannerAbove8 actionCanonicalPlannerSummaries).map
        RegionShapeSummary.normalized) := by
  apply normalized_filter_perm
  intro summary
  simp only [RegionShapeSummary.normalized_key_eq]

private theorem plannerKey8_normalized_perm :
    ((plannerKey8 actionSortedPlannerSummaries).map
        RegionShapeSummary.normalized).Perm
      ((plannerKey8 actionCanonicalPlannerSummaries).map
        RegionShapeSummary.normalized) := by
  apply normalized_filter_perm
  intro summary
  simp only [RegionShapeSummary.normalized_key_eq]

private theorem plannerBetween8And4_normalized_perm :
    ((plannerBetween8And4 actionSortedPlannerSummaries).map
        RegionShapeSummary.normalized).Perm
      ((plannerBetween8And4 actionCanonicalPlannerSummaries).map
        RegionShapeSummary.normalized) := by
  apply normalized_filter_perm
  intro summary
  simp only [RegionShapeSummary.normalized_key_eq]

private theorem plannerKey4_normalized_perm :
    ((plannerKey4 actionSortedPlannerSummaries).map
        RegionShapeSummary.normalized).Perm
      ((plannerKey4 actionCanonicalPlannerSummaries).map
        RegionShapeSummary.normalized) := by
  apply normalized_filter_perm
  intro summary
  simp only [RegionShapeSummary.normalized_key_eq]

private theorem plannerBelow4_normalized_perm :
    ((plannerBelow4 actionSortedPlannerSummaries).map
        RegionShapeSummary.normalized).Perm
      ((plannerBelow4 actionCanonicalPlannerSummaries).map
        RegionShapeSummary.normalized) := by
  apply normalized_filter_perm
  intro summary
  simp only [RegionShapeSummary.normalized_key_eq]

private def planner8Wide : RegionShapeSummary :=
  plannerShape [6,7,8,9] 2

private def planner8Short : RegionShapeSummary :=
  plannerShape [0,1,2,3,4,5,6,7] 1

private def planner4Narrow : RegionShapeSummary :=
  plannerShape [6,7] 2

private def planner4Wide : RegionShapeSummary :=
  plannerShape [6,7,8,9] 1

private theorem filter_expandPlannerBlocks
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
      by_cases hpredicate : predicate block.2 = true
      · rw [show (block :: rest).filter (fun block =>
            predicate block.2) = block :: rest.filter (fun block =>
              predicate block.2) by simp [hpredicate],
          show expandPlannerBlocks
              (block :: rest.filter (fun block => predicate block.2)) =
            List.replicate block.1 block.2 ++
              expandPlannerBlocks
                (rest.filter (fun block => predicate block.2)) by
            rfl]
        simp [hpredicate]
      · rw [show (block :: rest).filter (fun block =>
            predicate block.2) = rest.filter (fun block =>
              predicate block.2) by simp [hpredicate]]
        simp [hpredicate]

private theorem plannerKey8_canonical_eq :
    plannerKey8 actionCanonicalPlannerSummaries =
      List.replicate 8 planner8Wide ++ [planner8Short] := by
  rw [show actionCanonicalPlannerSummaries =
      expandPlannerBlocks actionPlannerBlocks by rfl,
    plannerKey8, filter_expandPlannerBlocks]
  have hblocks :
      actionPlannerBlocks.filter
          (fun block => decide (block.2.key = 8)) =
        [(8, planner8Wide), (1, planner8Short)] := by
    unfold actionPlannerBlocks planner8Wide planner8Short plannerShape
      RegionShapeSummary.key RegionShapeSummary.adviceCols
      RegionColumn.isAdvice
    simp
  rw [hblocks]
  rfl

private theorem plannerKey4_canonical_eq :
    plannerKey4 actionCanonicalPlannerSummaries =
      List.replicate 2 planner4Narrow ++
        List.replicate 2 planner4Wide := by
  rw [show actionCanonicalPlannerSummaries =
      expandPlannerBlocks actionPlannerBlocks by rfl,
    plannerKey4, filter_expandPlannerBlocks]
  have hblocks :
      actionPlannerBlocks.filter
          (fun block => decide (block.2.key = 4)) =
        [(2, planner4Narrow), (2, planner4Wide)] := by
    unfold actionPlannerBlocks planner4Narrow planner4Wide plannerShape
      RegionShapeSummary.key RegionShapeSummary.adviceCols
      RegionColumn.isAdvice
    simp
  rw [hblocks]
  rfl

private theorem regularPlannerSegment_equivalent
    (predicate : RegionShapeSummary → Bool)
    (hnormalized :
      ((actionSortedPlannerSummaries.filter predicate).map
          RegionShapeSummary.normalized).Perm
        ((actionCanonicalPlannerSummaries.filter predicate).map
          RegionShapeSummary.normalized))
    (hregular : ∀ summary, predicate summary = true →
      summary.key ≠ 8 ∧ summary.key ≠ 4)
    (initial : ℕ) (allocations : CircuitAllocations)
    (hvalid : allocations.Valid) :
    V1.SummaryStateEquivalent
      (V1.slotSummaryStateFromWith initial
        (actionSortedPlannerSummaries.filter predicate) allocations)
      (V1.slotSummaryStateFromWith initial
        (actionCanonicalPlannerSummaries.filter predicate) allocations) := by
  apply V1.slotSummaryStateFromWith_eq_of_normalized_perm hnormalized
  · exact filter_key_sorted predicate actionSortedPlannerSummaries
      actionSortedPlannerSummaries_key_sorted
  · exact filter_key_sorted predicate actionCanonicalPlannerSummaries
      actionCanonicalPlannerSummaries_key_sorted
  · rw [List.forall_iff_forall_mem]
    intro summary hsummary
    rw [List.mem_filter] at hsummary
    exact List.forall_iff_forall_mem.mp
      actionCanonicalPlannerSummaries_wellFormed summary hsummary.1
  · intro first hfirst second hsecond hkey
    rw [List.mem_filter] at hfirst hsecond
    have hkeys := hregular first hfirst.2
    exact actionCanonicalPlannerSummaries_regular_ties hfirst.1 hsecond.1
      hkey hkeys.1 hkeys.2
  · exact hvalid

private theorem canonicalFiltered_wellFormed
    (predicate : RegionShapeSummary → Bool) :
    (actionCanonicalPlannerSummaries.filter predicate).Forall
      RegionShapeSummary.WellFormed := by
  rw [List.forall_iff_forall_mem]
  intro summary hsummary
  rw [List.mem_filter] at hsummary
  exact List.forall_iff_forall_mem.mp
    actionCanonicalPlannerSummaries_wellFormed summary hsummary.1

private theorem allocationsValid_of_summaryStateEquivalent
    {left right : ℕ × CircuitAllocations}
    (hequivalent : V1.SummaryStateEquivalent left right)
    (hrightValid : right.2.Valid) : left.2.Valid := by
  intro column
  rw [hequivalent.2 column]
  exact hrightValid column

private theorem continueCanonicalSegment
    (summaries : List RegionShapeSummary)
    (hwellFormed : summaries.Forall RegionShapeSummary.WellFormed)
    {left right : ℕ × CircuitAllocations}
    (hrightValid : right.2.Valid)
    (hequivalent : V1.SummaryStateEquivalent left right) :
    V1.SummaryStateEquivalent
      (V1.slotSummaryStateFromWith left.1 summaries left.2)
      (V1.slotSummaryStateFromWith right.1 summaries right.2) :=
  V1.slotSummaryStateFromWith_equivalent summaries hwellFormed
    (allocationsValid_of_summaryStateEquivalent hequivalent hrightValid)
    hrightValid hequivalent

private theorem plannerAbove8_equivalent
    (initial : ℕ) (allocations : CircuitAllocations)
    (hvalid : allocations.Valid) :
    V1.SummaryStateEquivalent
      (V1.slotSummaryStateFromWith initial
        (plannerAbove8 actionSortedPlannerSummaries) allocations)
      (V1.slotSummaryStateFromWith initial
        (plannerAbove8 actionCanonicalPlannerSummaries) allocations) := by
  apply regularPlannerSegment_equivalent
    (predicate := fun summary => decide (8 < summary.key))
    (hnormalized := plannerAbove8_normalized_perm)
    (initial := initial) (allocations := allocations) (hvalid := hvalid)
  intro summary hsummary
  simp only [decide_eq_true_eq] at hsummary
  omega

private theorem plannerBetween8And4_equivalent
    (initial : ℕ) (allocations : CircuitAllocations)
    (hvalid : allocations.Valid) :
    V1.SummaryStateEquivalent
      (V1.slotSummaryStateFromWith initial
        (plannerBetween8And4 actionSortedPlannerSummaries) allocations)
      (V1.slotSummaryStateFromWith initial
        (plannerBetween8And4 actionCanonicalPlannerSummaries) allocations) := by
  apply regularPlannerSegment_equivalent
    (predicate := fun summary =>
      decide (4 < summary.key ∧ summary.key < 8))
    (hnormalized := plannerBetween8And4_normalized_perm)
    (initial := initial) (allocations := allocations) (hvalid := hvalid)
  intro summary hsummary
  simp only [decide_eq_true_eq] at hsummary
  omega

private theorem plannerBelow4_equivalent
    (initial : ℕ) (allocations : CircuitAllocations)
    (hvalid : allocations.Valid) :
    V1.SummaryStateEquivalent
      (V1.slotSummaryStateFromWith initial
        (plannerBelow4 actionSortedPlannerSummaries) allocations)
      (V1.slotSummaryStateFromWith initial
        (plannerBelow4 actionCanonicalPlannerSummaries) allocations) := by
  apply regularPlannerSegment_equivalent
    (predicate := fun summary => decide (summary.key < 4))
    (hnormalized := plannerBelow4_normalized_perm)
    (initial := initial) (allocations := allocations) (hvalid := hvalid)
  intro summary hsummary
  simp only [decide_eq_true_eq] at hsummary
  omega

/-- The same canonical order, split only where one equal-shape run crosses an
occupied interval. Each entry can therefore use the symbolic consecutive-run
planner theorem. Zero-row summaries are omitted because they change neither
the allocation state nor its endpoint. -/
structure ActionPlannerRun where
  count : Nat
  block : Nat
  start : Nat

/-- Exact Action placement compressed to consecutive runs of equal physical shapes. -/
def actionExactPlannerTrace : List V1.PlannedSummaryBlock := (
  [{ count := 1, block := 0, start := 0 },
   { count := 1, block := 1, start := 137 },
   { count := 1, block := 2, start := 137 },
   { count := 1, block := 3, start := 247 },
   { count := 5, block := 4, start := 333 },
   { count := 1, block := 6, start := 758 },
   { count := 2, block := 5, start := 758 },
   { count := 2, block := 6, start := 811 },
   { count := 2, block := 5, start := 864 },
   { count := 2, block := 6, start := 917 },
   { count := 1, block := 5, start := 970 },
   { count := 1, block := 6, start := 1023 },
   { count := 2, block := 5, start := 1023 },
   { count := 3, block := 6, start := 1076 },
   { count := 1, block := 5, start := 1129 },
   { count := 5, block := 6, start := 1235 },
   { count := 1, block := 5, start := 1182 },
   { count := 1, block := 6, start := 1500 },
   { count := 5, block := 5, start := 1235 },
   { count := 1, block := 6, start := 1553 },
   { count := 2, block := 5, start := 1500 },
   { count := 1, block := 7, start := 1606 },
   { count := 1, block := 8, start := 1606 },
   { count := 1, block := 9, start := 1658 },
   { count := 1, block := 10, start := 1681 },
   { count := 4, block := 11, start := 247 },
   { count := 14, block := 12, start := 1685 },
   { count := 5, block := 13, start := 351 },
   { count := 11, block := 14, start := 426 },
   { count := 1, block := 15, start := 1713 },
   { count := 4, block := 16, start := 1643 },
   { count := 1, block := 15, start := 1715 },
   { count := 2, block := 16, start := 1651 },
   { count := 2, block := 15, start := 1717 },
   { count := 1, block := 16, start := 1655 },
   { count := 4, block := 16, start := 1713 },
   { count := 1, block := 15, start := 1721 },
   { count := 2, block := 16, start := 1721 },
   { count := 1, block := 15, start := 1723 },
   { count := 1, block := 16, start := 1725 },
   { count := 1, block := 15, start := 1725 },
   { count := 1, block := 16, start := 1727 },
   { count := 1, block := 15, start := 1727 },
   { count := 1, block := 16, start := 1729 },
   { count := 1, block := 15, start := 1729 },
   { count := 1, block := 16, start := 1731 },
   { count := 2, block := 15, start := 1731 },
   { count := 1, block := 16, start := 1733 },
   { count := 2, block := 15, start := 1735 },
   { count := 2, block := 16, start := 1735 },
   { count := 3, block := 15, start := 1739 },
   { count := 3, block := 17, start := 247 },
   { count := 1, block := 18, start := 580 },
   { count := 1, block := 19, start := 1745 },
   { count := 7, block := 18, start := 582 },
   { count := 4, block := 20, start := 256 },
   { count := 1, block := 21, start := 1746 },
   { count := 1, block := 22, start := 1657 },
   { count := 1, block := 21, start := 1747 },
   { count := 1, block := 22, start := 1739 },
   { count := 1, block := 21, start := 1748 },
   { count := 1, block := 22, start := 1740 },
   { count := 1, block := 21, start := 1749 },
   { count := 3, block := 22, start := 1741 },
   { count := 3, block := 21, start := 1750 },
   { count := 1, block := 22, start := 1744 },
   { count := 1, block := 22, start := 1746 },
   { count := 2, block := 21, start := 1753 },
   { count := 1, block := 22, start := 1747 },
   { count := 1, block := 21, start := 1755 },
   { count := 1, block := 22, start := 1748 },
   { count := 2, block := 21, start := 1756 },
   { count := 2, block := 22, start := 1749 },
   { count := 2, block := 21, start := 1758 },
   { count := 1, block := 22, start := 1751 },
   { count := 1, block := 21, start := 1760 },
   { count := 2, block := 22, start := 1752 },
   { count := 1, block := 21, start := 1761 },
   { count := 1, block := 22, start := 1754 },
   { count := 2, block := 24, start := 596 },
   { count := 2, block := 23, start := 264 },
   { count := 2, block := 25, start := 598 },
   { count := 1, block := 26, start := 268 },
   { count := 1, block := 25, start := 604 },
   { count := 1, block := 26, start := 269 },
   { count := 50, block := 25, start := 607 },
   { count := 12, block := 25, start := 1606 },
   { count := 2, block := 25, start := 1658 },
   { count := 1, block := 26, start := 270 },
   { count := 5, block := 25, start := 1664 },
   { count := 2, block := 25, start := 1685 },
   { count := 3, block := 26, start := 271 },
   { count := 7, block := 25, start := 1691 },
   { count := 8, block := 25, start := 1755 },
   { count := 6, block := 27, start := 1762 },
   { count := 1, block := 31, start := 274 },
   { count := 2, block := 29, start := 274 },
   { count := 2, block := 31, start := 275 },
   { count := 1, block := 29, start := 276 },
   { count := 3, block := 31, start := 277 },
   { count := 2, block := 29, start := 277 },
   { count := 2, block := 31, start := 280 },
   { count := 1, block := 29, start := 279 },
   { count := 3, block := 31, start := 282 },
   { count := 2, block := 29, start := 280 },
   { count := 2, block := 31, start := 285 },
   { count := 1, block := 29, start := 282 },
   { count := 3, block := 31, start := 287 },
   { count := 2, block := 29, start := 283 },
   { count := 1, block := 31, start := 290 },
   { count := 1, block := 30, start := 1768 },
   { count := 1, block := 29, start := 285 },
   { count := 3, block := 31, start := 291 },
   { count := 2, block := 29, start := 286 },
   { count := 2, block := 31, start := 294 },
   { count := 1, block := 29, start := 288 },
   { count := 3, block := 31, start := 296 },
   { count := 2, block := 29, start := 289 },
   { count := 2, block := 31, start := 299 },
   { count := 1, block := 29, start := 291 },
   { count := 3, block := 31, start := 301 },
   { count := 2, block := 29, start := 292 },
   { count := 2, block := 31, start := 304 },
   { count := 1, block := 29, start := 294 },
   { count := 3, block := 31, start := 306 },
   { count := 1, block := 29, start := 295 },
   { count := 1, block := 30, start := 1769 },
   { count := 3, block := 29, start := 296 },
   { count := 3, block := 31, start := 309 },
   { count := 2, block := 29, start := 299 },
   { count := 2, block := 31, start := 312 },
   { count := 1, block := 29, start := 301 },
   { count := 2, block := 31, start := 314 },
   { count := 1, block := 28, start := 757 },
   { count := 2, block := 29, start := 302 },
   { count := 1, block := 28, start := 1642 },
   { count := 8, block := 29, start := 304 },
   { count := 2, block := 31, start := 316 },
   { count := 13, block := 29, start := 312 },
   { count := 1, block := 30, start := 1770 },
   { count := 2, block := 29, start := 325 },
   { count := 2, block := 31, start := 318 },
   { count := 1, block := 29, start := 327 },
   { count := 1, block := 31, start := 320 },
   { count := 1, block := 30, start := 1771 },
   { count := 2, block := 29, start := 328 },
   { count := 2, block := 31, start := 321 },
   { count := 1, block := 29, start := 330 },
   { count := 3, block := 31, start := 323 },
   { count := 2, block := 29, start := 331 },
   { count := 2, block := 31, start := 326 },
   { count := 1, block := 29, start := 333 },
   { count := 1, block := 31, start := 328 },
   { count := 2, block := 30, start := 1772 },
   { count := 1, block := 29, start := 334 },
   { count := 1, block := 31, start := 329 },
  ] : List ActionPlannerRun).map fun item =>
    { count := item.count
      summary := (actionPlannerBlocks.getD item.block
        (0, { columns := [], rowCount := 0 })).2
      start := item.start }

/-- The end row of each run in the reduced placement trace. -/
def actionExactPlannerEndpoints : List ℕ :=
  [137, 247, 247, 333, 758, 811, 864, 917, 970, 1023, 1023, 1076, 1129,
   1235, 1182, 1500, 1235, 1553, 1500, 1606, 1606, 1658, 1643, 1681,
   1685, 351, 1713, 426, 580, 1715, 1651, 1717, 1655, 1721, 1657, 1721,
   1723, 1725, 1725, 1727, 1727, 1729, 1729, 1731, 1731, 1733, 1735,
   1735, 1739, 1739, 1745, 256, 582, 1746, 596, 264, 1747, 1658, 1748,
   1740, 1749, 1741, 1750, 1744, 1753, 1745, 1747, 1755, 1748, 1756,
   1749, 1758, 1751, 1760, 1752, 1761, 1754, 1762, 1755, 598, 268, 604,
   269, 607, 270, 757, 1642, 1664, 271, 1679, 1691, 274, 1712, 1779,
   1768, 275, 276, 277, 277, 280, 279, 282, 280, 285, 282, 287, 283, 290,
   285, 291, 1769, 286, 294, 288, 296, 289, 299, 291, 301, 292, 304, 294,
   306, 295, 309, 296, 1770, 299, 312, 301, 314, 302, 316, 758, 304,
   1643, 312, 318, 325, 1771, 327, 320, 328, 321, 1772, 330, 323, 331,
   326, 333, 328, 334, 329, 1774, 335, 330]

/-- The literal endpoint summary faithfully reduces the compact placement trace. -/
theorem actionExactPlannerTrace_endpoints_eq :
    (actionExactPlannerTrace.map fun block =>
      block.start + block.count * block.summary.rowCount) =
      actionExactPlannerEndpoints := by
  unfold actionExactPlannerTrace actionPlannerBlocks plannerShape
    actionExactPlannerEndpoints
  decide +kernel

end Zcash.Circuits.Action

