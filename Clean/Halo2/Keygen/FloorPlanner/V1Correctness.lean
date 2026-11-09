import Clean.Halo2.Keygen.FloorPlanner.SelectorPlacement
import Clean.Halo2.Keygen.FloorPlanner.V1
import Clean.Halo2.Keygen.PdqsortCorrectness

namespace Halo2.FloorPlanner

open Halo2

variable {F : Type}

/-! # Correctness theory for the V1 floor planner -/

namespace V1

theorem sortPairsByIndex_perm (pairs : List (ℕ × ℕ)) :
    (sortPairsByIndex pairs).Perm pairs := by
  exact List.perm_insertionSort
    (r := fun left right : ℕ × ℕ => left.1 ≤ right.1) pairs

private theorem sortPairsByIndex_fst_sorted (pairs : List (ℕ × ℕ)) :
    (sortPairsByIndex pairs).map (·.1) |>.SortedLE := by
  have hpairs := List.pairwise_insertionSort
    (r := fun left right : ℕ × ℕ => left.1 ≤ right.1) pairs
  have general : ∀ items : List (ℕ × ℕ),
      items.Pairwise (fun left right => left.1 ≤ right.1) →
        (items.map (·.1)).Pairwise (· ≤ ·) := by
    intro items hitems
    induction items with
    | nil => simp
    | cons head rest inductionHypothesis =>
        rw [List.pairwise_cons] at hitems
        rw [List.map_cons, List.pairwise_cons]
        constructor
        · intro item hitem
          rw [List.mem_map] at hitem
          obtain ⟨pair, hpair, rfl⟩ := hitem
          exact hitems.1 pair hpair
        · exact inductionHypothesis hitems.2
  rw [List.sortedLE_iff_pairwise]
  exact general _ hpairs

private theorem range_sortedLE (count : ℕ) :
    (List.range count).SortedLE := by
  rw [List.sortedLE_iff_pairwise]
  induction count with
  | zero => simp
  | succ count inductionHypothesis =>
      rw [List.range_succ, List.pairwise_append]
      exact ⟨inductionHypothesis, by simp, by
        intro left hleft right hright
        simp only [List.mem_singleton] at hright
        subst right
        exact Nat.le_of_lt (List.mem_range.mp hleft)⟩

private theorem sortPairsByIndex_fst_eq_range
    (pairs : List (ℕ × ℕ)) (count : ℕ)
    (hindices : (pairs.map (·.1)).Perm (List.range count)) :
    (sortPairsByIndex pairs).map (·.1) = List.range count := by
  apply List.Perm.eq_of_sortedLE
    (sortPairsByIndex_fst_sorted pairs)
    (range_sortedLE count)
  exact (sortPairsByIndex_perm pairs).map (·.1) |>.trans hindices

private theorem getD_of_mem_range_zip
    (values : List ℕ) {index value : ℕ}
    (hmember : (index, value) ∈
      (List.range values.length).zip values) :
    values.getD index 0 = value := by
  induction values generalizing index value with
  | nil => simp at hmember
  | cons head rest inductionHypothesis =>
      rw [List.length_cons, List.range_succ_eq_map,
        List.zip_cons_cons, List.mem_cons] at hmember
      rcases hmember with hhead | htail
      · have hindex : index = 0 := congrArg Prod.fst hhead
        have hvalue : value = head := congrArg Prod.snd hhead
        subst index
        subst value
        rfl
      · rw [List.zip_map_left, List.mem_map] at htail
        obtain ⟨pair, hpair, heq⟩ := htail
        rcases pair with ⟨restIndex, restValue⟩
        have hindex : restIndex + 1 = index := congrArg Prod.fst heq
        have hvalue : restValue = value := congrArg Prod.snd heq
        rw [← hindex, ← hvalue]
        exact inductionHypothesis hpair

private theorem starts_getD_of_pair_mem
    (pairs : List (ℕ × ℕ)) (count : ℕ)
    (hindices :
      (sortPairsByIndex pairs).map (·.1) = List.range count)
    {index start : ℕ}
    (hpair : (index, start) ∈ pairs) :
    ((sortPairsByIndex pairs).map (·.2)).getD index 0 = start := by
  let sorted := sortPairsByIndex pairs
  have hsortedPair : (index, start) ∈ sorted :=
    (sortPairsByIndex_perm pairs).mem_iff.mpr hpair
  have hzip : sorted =
      (List.range count).zip (sorted.map (·.2)) := by
    exact List.zip_of_prod hindices rfl
  have hlength : (sorted.map (·.2)).length = count := by
    have := congrArg List.length hindices
    simpa using this
  apply getD_of_mem_range_zip (sorted.map (·.2))
  rw [hlength, ← hzip]
  exact hsortedPair

/-- V1's actual first-fit candidate separates every pair of shared columns. -/
theorem planCandidate_measureRegions_sharedColumnIntervalsDisjoint
    (operations : Operations F) :
    SharedColumnIntervalsDisjoint
      (measureRegions operations)
      (planCandidate (measureRegions operations)).1 := by
  let shapes := measureRegions operations
  let sortedArray :=
    (Pdqsort.quicksort shapes.toArray
      (fun left right => left.key < right.key)).reverse
  let sortedShapes := sortedArray.toList
  have hsorted : sortedShapes.Perm shapes := by
    have hquick := Pdqsort.quicksort_perm shapes.toArray
      (fun left right => left.key < right.key)
    exact (by
      simpa [sortedShapes, sortedArray] using
        (List.reverse_perm
          (Pdqsort.quicksort shapes.toArray
            (fun left right => left.key < right.key)).toList).trans hquick)
  have hwellFormed : sortedShapes.Forall RegionShape.WellFormed := by
    rw [List.forall_iff_forall_mem]
    intro shape hshape
    have hshape' : shape ∈ measureRegions operations := by
      exact hsorted.mem_iff.mp hshape
    exact (List.forall_iff_forall_mem.mp
      (measureRegions_wellFormed operations)) shape hshape'
  let slotted := slotIn sortedShapes
  let pairs := slotted.1
  have hslot : SlotInLaw (∅ : CircuitAllocations) sortedShapes slotted := by
    exact slotInFrom_law sortedShapes ∅ CircuitAllocations.Valid.empty
      hwellFormed
  have hpairsRange : (pairs.map (·.1)).Perm
      (List.range operations.regionCount) := by
    rw [hslot.indices]
    have hindices := hsorted.map RegionShape.index
    change (sortedShapes.map RegionShape.index).Perm
      ((measureRegions operations).map RegionShape.index) at hindices
    rw [measureRegions_indices_eq_range] at hindices
    exact hindices
  have hsortedIndices :
      (sortPairsByIndex pairs).map (·.1) =
        List.range operations.regionCount :=
    sortPairsByIndex_fst_eq_range pairs operations.regionCount
      hpairsRange
  have hplanStarts :
      (planCandidate (measureRegions operations)).1 =
        (sortPairsByIndex pairs).map (·.2) := by
    rfl
  intro left right hleft hright hindices column
    hleftColumn hrightColumn
  have hleftSorted : left ∈ sortedShapes := hsorted.mem_iff.mpr hleft
  have hrightSorted : right ∈ sortedShapes := hsorted.mem_iff.mpr hright
  obtain ⟨leftStart, hleftPlaced⟩ :=
    placedShapes_exists_of_mem sortedShapes pairs hslot.indices hleftSorted
  obtain ⟨rightStart, hrightPlaced⟩ :=
    placedShapes_exists_of_mem sortedShapes pairs hslot.indices hrightSorted
  have hleftPair : (left.index, leftStart) ∈ pairs :=
    pair_mem_of_mem_placedShapes sortedShapes pairs hslot.indices hleftPlaced
  have hrightPair : (right.index, rightStart) ∈ pairs :=
    pair_mem_of_mem_placedShapes sortedShapes pairs hslot.indices hrightPlaced
  have hleftStart :
      ((sortPairsByIndex pairs).map (·.2)).getD left.index 0 =
        leftStart :=
    starts_getD_of_pair_mem pairs operations.regionCount
      hsortedIndices hleftPair
  have hrightStart :
      ((sortPairsByIndex pairs).map (·.2)).getD right.index 0 =
        rightStart :=
    starts_getD_of_pair_mem pairs operations.regionCount
      hsortedIndices hrightPair
  have hplacedNe : (left, leftStart) ≠ (right, rightStart) := by
    intro heq
    apply hindices
    exact congrArg (fun placed : RegionShape × ℕ => placed.1.index) heq
  rcases rel_or_reverse_of_pairwise_of_mem hslot.disjoint
      hleftPlaced hrightPlaced hplacedNe with hforward | hreverse
  · rw [hplanStarts, hleftStart, hrightStart]
    exact hforward column hleftColumn hrightColumn
  · have hdisjoint := hreverse column hrightColumn hleftColumn
    rw [hplanStarts, hleftStart, hrightStart]
    exact hdisjoint.elim Or.inr Or.inl
def placementEndFrom (shapes : List RegionShape) (regionStarts : List ℕ) : ℕ :=
  shapes.map (fun shape =>
    regionStarts.getD shape.index 0 + shape.rowCount)
    |>.foldl max 0

/-- One past the final row in slotting order. Unlike `placementEndFrom`, this
projection does not restore region-index order and therefore forgets indices entirely. -/
def slottedEndFrom (shapes : List RegionShape)
    (pairs : List (ℕ × ℕ)) : ℕ :=
  (placedShapes shapes pairs).map (fun placed =>
    placed.2 + placed.1.rowCount) |>.foldl max 0

/-- The same endpoint projection directly over the index-free synthesis summary. -/
def slottedSummaryEndFrom (summaries : List RegionShapeSummary)
    (starts : List ℕ) : ℕ :=
  (summaries.zip starts).map (fun placed =>
    placed.2 + placed.1.rowCount) |>.foldl max 0

/-- Erasing selector columns preserves the endpoint projection for any fixed
start-row sequence. -/
theorem slottedSummaryEndFrom_map_withoutSelectors
    (summaries : List RegionShapeSummary) (starts : List ℕ) :
    slottedSummaryEndFrom
        (summaries.map RegionShapeSummary.withoutSelectors) starts =
      slottedSummaryEndFrom summaries starts := by
  unfold slottedSummaryEndFrom
  apply congrArg (List.foldl max 0)
  induction summaries generalizing starts with
  | nil => rfl
  | cons summary rest inductionHypothesis =>
      cases starts with
      | nil => rfl
      | cons start starts =>
          simp only [List.map_cons, List.zip_cons_cons,
            RegionShapeSummary.withoutSelectors]
          rw [inductionHypothesis]

/-- When selector allocations are dominated by physical anchor columns, erasing
selectors preserves the exact endpoint as well as every chosen start row. -/
theorem slotSummaryEndFrom_eq_withoutSelectors
    (summaries : List RegionShapeSummary)
    (left right : CircuitAllocations)
    (hwellFormed : summaries.Forall RegionShapeSummary.WellFormed)
    (hvalidLeft : left.Valid) (hvalidRight : right.Valid)
    {anchor : ℕ → RegionColumn}
    (hphysical : CircuitAllocations.PhysicalEquivalent left right)
    (hselectors : SelectorAllocationsDominatedBy left anchor)
    (hanchors : SelectorAnchoredBy summaries anchor) :
    slottedSummaryEndFrom summaries
        (slotShapeSummariesFrom summaries left).1 =
      slottedSummaryEndFrom
        (summaries.map RegionShapeSummary.withoutSelectors)
        (slotShapeSummariesFrom
          (summaries.map RegionShapeSummary.withoutSelectors) right).1 := by
  have hstarts := (slotShapeSummariesFrom_eq_withoutSelectors summaries
    left right hwellFormed hvalidLeft hvalidRight hphysical hselectors
    hanchors).1
  rw [← hstarts, slottedSummaryEndFrom_map_withoutSelectors]

/-- Exact end row obtained by slotting an index-free reduced summary, folded
from an existing end row. -/
def slotSummaryEndFromWith (initial : ℕ)
    (summaries : List RegionShapeSummary)
    (allocations : CircuitAllocations) : ℕ :=
  (summaries.zip (slotShapeSummariesFrom summaries allocations).1).map
    (fun placed => placed.2 + placed.1.rowCount) |>.foldl max initial

/-- The endpoint and final allocation state produced by a summary sequence. Keeping
the two together makes compact block replacement compositional. -/
def slotSummaryStateFromWith (initial : ℕ)
    (summaries : List RegionShapeSummary)
    (allocations : CircuitAllocations) : ℕ × CircuitAllocations :=
  match summaries with
  | [] => (initial, allocations)
  | summary :: rest =>
      let placed := placeSummary summary allocations
      slotSummaryStateFromWith
        (max initial (placed.1.getD 0 + summary.rowCount)) rest placed.2

/-- Replacing every reduced region shape by a placement-equivalent shape preserves
the endpoint and final allocation state. -/
theorem slotSummaryStateFromWith_eq_of_forall₂_placementEquivalent
    {left right : List RegionShapeSummary}
    (hequivalent : List.Forall₂ RegionShapeSummary.PlacementEquivalent
      left right) (initial : ℕ) (allocations : CircuitAllocations) :
    slotSummaryStateFromWith initial left allocations =
      slotSummaryStateFromWith initial right allocations := by
  induction hequivalent generalizing initial allocations with
  | nil => rfl
  | @cons left right leftTail rightTail hhead _ inductionHypothesis =>
      simp only [slotSummaryStateFromWith]
      rw [placeSummary_eq_of_placementEquivalent hhead]
      rw [hhead.2]
      exact inductionHypothesis _ _

/-- A permutation after applying a projection can be lifted to a permutation of
the original list whose corresponding entries have equal projections. -/
theorem exists_perm_forall₂_of_map_perm {A B : Type} (project : A → B)
    {left right : List A}
    (hperm : (left.map project).Perm (right.map project)) :
    ∃ aligned, aligned.Perm right ∧
      List.Forall₂ (fun first second => project first = project second)
        left aligned := by
  have hcomposed :
      Relation.Comp (fun projected original => projected = original.map project)
        List.Perm (left.map project) right := by
    rw [List.eq_map_comp_perm]
    exact hperm
  obtain ⟨aligned, hprojected, haligned⟩ := hcomposed
  refine ⟨aligned, haligned, ?_⟩
  simpa only [← List.forall₂_map_left_iff,
    ← List.forall₂_map_right_iff, List.forall₂_eq_eq_eq] using hprojected

theorem slotSummaryStateFromWith_fst
    (initial : ℕ) (summaries : List RegionShapeSummary)
    (allocations : CircuitAllocations) :
    (slotSummaryStateFromWith initial summaries allocations).1 =
      slotSummaryEndFromWith initial summaries allocations := by
  induction summaries generalizing initial allocations with
  | nil => rfl
  | cons summary rest inductionHypothesis =>
      generalize hplaced : placeSummary summary allocations = placed
      rcases placed with ⟨row, updated⟩
      have hcons :
          slotSummaryEndFromWith initial (summary :: rest) allocations =
            slotSummaryEndFromWith
              (max initial (row.getD 0 + summary.rowCount)) rest updated := by
        unfold slotSummaryEndFromWith
        simp only [slotShapeSummariesFrom, hplaced, List.zip_cons_cons,
          List.map_cons, List.foldl_cons]
      rw [hcons]
      simp only [slotSummaryStateFromWith, hplaced]
      exact inductionHypothesis _ _

theorem slotSummaryStateFromWith_snd
    (initial : ℕ) (summaries : List RegionShapeSummary)
    (allocations : CircuitAllocations) :
    (slotSummaryStateFromWith initial summaries allocations).2 =
      (slotShapeSummariesFrom summaries allocations).2 := by
  induction summaries generalizing initial allocations with
  | nil => rfl
  | cons summary rest inductionHypothesis =>
      generalize hplaced : placeSummary summary allocations = placed
      rcases placed with ⟨row, updated⟩
      simp only [slotSummaryStateFromWith, slotShapeSummariesFrom, hplaced]
      exact inductionHypothesis _ _

/-- Slotting well-formed summaries preserves the allocation invariant. -/
theorem slotSummaryStateFromWith_valid
    (initial : ℕ) (summaries : List RegionShapeSummary)
    (allocations : CircuitAllocations)
    (hwellFormed : summaries.Forall RegionShapeSummary.WellFormed)
    (hvalid : allocations.Valid) :
    (slotSummaryStateFromWith initial summaries allocations).2.Valid := by
  induction summaries generalizing initial allocations with
  | nil => exact hvalid
  | cons summary rest inductionHypothesis =>
      rw [List.forall_cons] at hwellFormed
      generalize hplaced : placeSummary summary allocations = placed
      rcases placed with ⟨row, updated⟩
      have hupdated := placeSummary_valid summary allocations hvalid
        hwellFormed.1
      rw [hplaced] at hupdated
      simp only [slotSummaryStateFromWith, hplaced]
      exact inductionHypothesis _ _ hwellFormed.2 hupdated

/-- Planner states agree when their endpoints agree and their allocation maps
contain the same observable interval sequences. -/
def SummaryStateEquivalent
    (left right : ℕ × CircuitAllocations) : Prop :=
  left.1 = right.1 ∧ left.2.Equivalent right.2

theorem SummaryStateEquivalent.refl
    (state : ℕ × CircuitAllocations) :
    SummaryStateEquivalent state state :=
  ⟨rfl, CircuitAllocations.Equivalent.refl state.2⟩

theorem SummaryStateEquivalent.symm
    {left right : ℕ × CircuitAllocations}
    (hequivalent : SummaryStateEquivalent left right) :
    SummaryStateEquivalent right left :=
  ⟨hequivalent.1.symm, hequivalent.2.symm⟩

theorem SummaryStateEquivalent.trans
    {left middle right : ℕ × CircuitAllocations}
    (hleft : SummaryStateEquivalent left middle)
    (hright : SummaryStateEquivalent middle right) :
    SummaryStateEquivalent left right :=
  ⟨hleft.1.trans hright.1, hleft.2.trans hright.2⟩

/-- A well-formed suffix preserves equivalent planner states. -/
theorem slotSummaryStateFromWith_equivalent
    (summaries : List RegionShapeSummary)
    (hwellFormed : summaries.Forall RegionShapeSummary.WellFormed)
    {left right : ℕ × CircuitAllocations}
    (hvalidLeft : left.2.Valid) (hvalidRight : right.2.Valid)
    (hequivalent : SummaryStateEquivalent left right) :
    SummaryStateEquivalent
      (slotSummaryStateFromWith left.1 summaries left.2)
      (slotSummaryStateFromWith right.1 summaries right.2) := by
  have hslot := slotShapeSummariesFrom_equivalent summaries left.2 right.2
    hwellFormed hvalidLeft hvalidRight hequivalent.2
  constructor
  · rw [slotSummaryStateFromWith_fst,
      slotSummaryStateFromWith_fst]
    unfold slotSummaryEndFromWith
    rw [hslot.1, hequivalent.1]
  · rw [slotSummaryStateFromWith_snd,
      slotSummaryStateFromWith_snd]
    exact hslot.2

theorem slotSummaryStateFromWith_append
    (initial : ℕ) (left right : List RegionShapeSummary)
    (allocations : CircuitAllocations) :
    slotSummaryStateFromWith initial (left ++ right) allocations =
      let leftResult :=
        slotSummaryStateFromWith initial left allocations
      slotSummaryStateFromWith leftResult.1 right leftResult.2 := by
  induction left generalizing initial allocations with
  | nil => rfl
  | cons summary rest inductionHypothesis =>
      generalize hplaced : placeSummary summary allocations = placed
      rcases placed with ⟨row, updated⟩
      simp only [List.cons_append, slotSummaryStateFromWith, hplaced]
      exact inductionHypothesis _ _

/-- Repeatedly place one compact summary block while retaining its repetition
count. -/
def slotSummaryStateRepeated (count : ℕ)
    (summaries : List RegionShapeSummary) (initial : ℕ)
    (allocations : CircuitAllocations) : ℕ × CircuitAllocations :=
  match count with
  | 0 => (initial, allocations)
  | count + 1 =>
      let first := slotSummaryStateFromWith initial summaries allocations
      slotSummaryStateRepeated count summaries first.1 first.2

theorem slotSummaryStateFromWith_flatten_replicate
    (count : ℕ) (summaries : List RegionShapeSummary)
    (initial : ℕ) (allocations : CircuitAllocations) :
    slotSummaryStateFromWith initial
        (List.replicate count summaries).flatten allocations =
      slotSummaryStateRepeated count summaries initial allocations := by
  induction count generalizing initial allocations with
  | zero => rfl
  | succ count inductionHypothesis =>
      rw [List.replicate_succ, List.flatten_cons,
        slotSummaryStateFromWith_append]
      simp only [slotSummaryStateRepeated]
      rw [inductionHypothesis]

/-- Evaluate a sequence of repeated singleton-summary blocks without expanding
any block into a concrete list. -/
def slotSummaryBlocksState (blocks : List (ℕ × RegionShapeSummary))
    (initial : ℕ) (allocations : CircuitAllocations) :
    ℕ × CircuitAllocations :=
  match blocks with
  | [] => (initial, allocations)
  | (count, summary) :: rest =>
      let first := slotSummaryStateRepeated count [summary]
        initial allocations
      slotSummaryBlocksState rest first.1 first.2

theorem slotSummaryStateFromWith_flatMap_replicate
    (blocks : List (ℕ × RegionShapeSummary))
    (initial : ℕ) (allocations : CircuitAllocations) :
    slotSummaryStateFromWith initial
        (blocks.flatMap fun block =>
          List.replicate block.1 block.2) allocations =
      slotSummaryBlocksState blocks initial allocations := by
  induction blocks generalizing initial allocations with
  | nil => rfl
  | cons block rest inductionHypothesis =>
      rcases block with ⟨count, summary⟩
      rw [List.flatMap_cons, slotSummaryStateFromWith_append,
        ← List.flatten_replicate_singleton,
        slotSummaryStateFromWith_flatten_replicate]
      simp only [slotSummaryBlocksState]
      exact inductionHypothesis _ _

theorem slotSummaryStateFromWith_replicate_empty
    (count initial : ℕ) (allocations : CircuitAllocations) :
    slotSummaryStateFromWith initial
      (List.replicate count { columns := [], rowCount := 0 }) allocations =
        (initial, allocations) := by
  induction count generalizing initial allocations with
  | zero => rfl
  | succ count inductionHypothesis =>
      rw [List.replicate_succ]
      simp only [slotSummaryStateFromWith]
      simp [placeSummary, sortRegionColumns, firstFit]
      exact inductionHypothesis _ _

/-- If a free run begins at the current least fit, repeated copies of one
summary occupy that run consecutively. Besides the endpoint, expose an
extensional view of the resulting allocation state so consecutive compact
blocks can be composed without expanding the repetition. -/
theorem slotSummaryStateRepeated_single_eq
    (count : ℕ) (summary : RegionShapeSummary)
    (initial : ℕ) (allocations : CircuitAllocations)
    (view : AllocationView) (start : ℕ)
    (hrepresents : view.Represents allocations)
    (hvalid : view.Valid)
    (hnodup : summary.columns.Nodup)
    (hcolumns : summary.columns ≠ [])
    (hlength : 0 < summary.rowCount)
    (hleast : view.LeastFit (sortRegionColumns summary.columns)
      summary.rowCount start)
    (hfree : view.FitsColumns (sortRegionColumns summary.columns) start
      ((count + 1) * summary.rowCount)) :
    let result := slotSummaryStateRepeated (count + 1) [summary]
      initial allocations
    result.1 = max initial (start + (count + 1) * summary.rowCount) ∧
      (view.insertRepeated (sortRegionColumns summary.columns) start
        summary.rowCount (count + 1)).Represents result.2 := by
  induction count generalizing initial allocations view start with
  | zero =>
      obtain ⟨updated, hplaced, hupdatedRepresents⟩ :=
        view.placeSummary_eq_of_leastFit summary allocations start
          hrepresents hvalid hnodup hlength hleast
      simp only [slotSummaryStateRepeated, slotSummaryStateFromWith, hplaced,
        Option.getD_some, AllocationView.insertRepeated]
      exact ⟨by omega, hupdatedRepresents⟩
  | succ count inductionHypothesis =>
      let columns := sortRegionColumns summary.columns
      have hsortedColumns : columns ≠ [] := by
        intro hempty
        have hlengths := (sortRegionColumns_perm summary.columns).length_eq
        have : summary.columns.length = 0 := by
          simpa [columns, hempty] using hlengths.symm
        exact hcolumns (List.eq_nil_of_length_eq_zero this)
      obtain ⟨updated, hplaced, hupdatedRepresents⟩ :=
        view.placeSummary_eq_of_leastFit summary allocations start
          hrepresents hvalid hnodup hlength hleast
      have hactualValid : allocations.Valid := hrepresents.valid hvalid
      have hsummaryWellFormed : summary.WellFormed :=
        ⟨hnodup, fun _ => hlength⟩
      have hupdatedValidActual : updated.Valid := by
        have hresult := placeSummary_valid summary allocations hactualValid
          hsummaryWellFormed
        rw [hplaced] at hresult
        exact hresult
      have hupdatedValid :
          (view.insert columns start summary.rowCount).Valid := by
        intro column
        rw [← hupdatedRepresents column]
        exact hupdatedValidActual column
      have hnextLeast := view.leastFit_insert_next hsortedColumns hlength
        hleast hfree
      have htailFree := view.fitsColumns_insert_tail hfree
      have hrecursive := inductionHypothesis
        (max initial (start + summary.rowCount)) updated
        (view.insert columns start summary.rowCount)
        (start + summary.rowCount) hupdatedRepresents hupdatedValid
        hnextLeast htailFree
      rw [show count.succ + 1 = (count + 1) + 1 by omega,
        slotSummaryStateRepeated]
      simp only [slotSummaryStateFromWith, hplaced, Option.getD_some,
        AllocationView.insertRepeated]
      exact ⟨by
          simp only [Nat.add_mul] at hrecursive ⊢
          omega,
        hrecursive.2⟩

/-- Consecutive start rows for a compact run of equal-height regions. -/
def repeatedStarts (start length : ℕ) : ℕ → List ℕ
  | 0 => []
  | count + 1 => start :: repeatedStarts (start + length) length count

/-- Exact start rows and final allocation view for a compact run of one summary.
This is the list-valued companion of `slotSummaryStateRepeated_single_eq`. -/
theorem slotShapeSummariesRepeated_single_eq
    (count : ℕ) (summary : RegionShapeSummary)
    (allocations : CircuitAllocations)
    (view : AllocationView) (start : ℕ)
    (hrepresents : view.Represents allocations)
    (hvalid : view.Valid)
    (hnodup : summary.columns.Nodup)
    (hcolumns : summary.columns ≠ [])
    (hlength : 0 < summary.rowCount)
    (hleast : view.LeastFit (sortRegionColumns summary.columns)
      summary.rowCount start)
    (hfree : view.FitsColumns (sortRegionColumns summary.columns) start
      ((count + 1) * summary.rowCount)) :
    let result := slotShapeSummariesRepeated (count + 1) [summary] allocations
    result.1 = repeatedStarts start summary.rowCount (count + 1) ∧
      (view.insertRepeated (sortRegionColumns summary.columns) start
        summary.rowCount (count + 1)).Represents result.2 := by
  induction count generalizing allocations view start with
  | zero =>
      obtain ⟨updated, hplaced, hupdatedRepresents⟩ :=
        view.placeSummary_eq_of_leastFit summary allocations start
          hrepresents hvalid hnodup hlength hleast
      simp only [slotShapeSummariesRepeated, slotShapeSummariesFrom,
        hplaced, Option.getD_some, repeatedStarts,
        AllocationView.insertRepeated]
      exact ⟨rfl, hupdatedRepresents⟩
  | succ count inductionHypothesis =>
      let columns := sortRegionColumns summary.columns
      have hsortedColumns : columns ≠ [] := by
        intro hempty
        have hlengths := (sortRegionColumns_perm summary.columns).length_eq
        have : summary.columns.length = 0 := by
          simpa [columns, hempty] using hlengths.symm
        exact hcolumns (List.eq_nil_of_length_eq_zero this)
      obtain ⟨updated, hplaced, hupdatedRepresents⟩ :=
        view.placeSummary_eq_of_leastFit summary allocations start
          hrepresents hvalid hnodup hlength hleast
      have hupdatedValid :
          (view.insert columns start summary.rowCount).Valid := by
        have hactualValid : allocations.Valid := hrepresents.valid hvalid
        have hsummaryWellFormed : summary.WellFormed :=
          ⟨hnodup, fun _ => hlength⟩
        have hupdatedValidActual : updated.Valid := by
          have hresult := placeSummary_valid summary allocations hactualValid
            hsummaryWellFormed
          rw [hplaced] at hresult
          exact hresult
        intro column
        rw [← hupdatedRepresents column]
        exact hupdatedValidActual column
      have hnextLeast := view.leastFit_insert_next hsortedColumns hlength
        hleast hfree
      have htailFree := view.fitsColumns_insert_tail hfree
      have hrecursive := inductionHypothesis updated
        (view.insert columns start summary.rowCount)
        (start + summary.rowCount) hupdatedRepresents hupdatedValid
        hnextLeast htailFree
      rw [show count.succ + 1 = (count + 1) + 1 by omega,
        slotShapeSummariesRepeated]
      simp only [slotShapeSummariesFrom, hplaced, Option.getD_some,
        List.singleton_append, repeatedStarts,
        AllocationView.insertRepeated]
      constructor
      · exact congrArg (start :: ·) hrecursive.1
      · exact hrecursive.2

/-- Endpoint-only form of `slotSummaryStateRepeated_single_eq`. -/
theorem slotSummaryStateRepeated_single_fst_eq
    (count : ℕ) (summary : RegionShapeSummary)
    (initial : ℕ) (allocations : CircuitAllocations)
    (view : AllocationView) (start : ℕ)
    (hrepresents : view.Represents allocations)
    (hvalid : view.Valid)
    (hnodup : summary.columns.Nodup)
    (hcolumns : summary.columns ≠ [])
    (hlength : 0 < summary.rowCount)
    (hleast : view.LeastFit (sortRegionColumns summary.columns)
      summary.rowCount start)
    (hfree : view.FitsColumns (sortRegionColumns summary.columns) start
      ((count + 1) * summary.rowCount))
    (hinitial : initial ≤ start + summary.rowCount) :
    (slotSummaryStateRepeated (count + 1) [summary]
      initial allocations).1 = start + (count + 1) * summary.rowCount :=
  (slotSummaryStateRepeated_single_eq count summary initial allocations
    view start hrepresents hvalid hnodup hcolumns hlength hleast hfree).1.trans
      (max_eq_right (hinitial.trans (by
        exact Nat.add_le_add_left
          (Nat.le_mul_of_pos_left summary.rowCount (Nat.succ_pos count))
          start)))

/-- One compact, already-planned run of equal region summaries. -/
structure PlannedSummaryBlock where
  count : ℕ
  summary : RegionShapeSummary
  start : ℕ

namespace PlannedSummaryBlock

def blocks (trace : List PlannedSummaryBlock) :
    List (ℕ × RegionShapeSummary) :=
  trace.map fun block => (block.count, block.summary)

/-- Exact start sequence represented by a compact planned trace. -/
def starts (trace : List PlannedSummaryBlock) : List ℕ :=
  trace.flatMap fun block =>
    repeatedStarts block.start block.summary.rowCount block.count

def endpointFrom (initial : ℕ) : List PlannedSummaryBlock → ℕ
  | [] => initial
  | block :: rest =>
      endpointFrom
        (max initial (block.start + block.count * block.summary.rowCount))
        rest

/-- The endpoint computation observes only the end row of each planned block. -/
theorem endpointFrom_eq_foldl_max (initial : ℕ)
    (trace : List PlannedSummaryBlock) :
    endpointFrom initial trace =
      (trace.map fun block =>
        block.start + block.count * block.summary.rowCount).foldl max initial := by
  induction trace generalizing initial with
  | nil => rfl
  | cons block rest inductionHypothesis =>
      simp only [endpointFrom, List.map_cons, List.foldl_cons]
      exact inductionHypothesis _

def finalView (initial : AllocationView) :
    List PlannedSummaryBlock → AllocationView
  | [] => initial
  | block :: rest =>
      finalView
        (initial.insertRepeated (sortRegionColumns block.summary.columns)
          block.start block.summary.rowCount block.count)
        rest

def Lawful (initial : AllocationView) :
    List PlannedSummaryBlock → Prop
  | [] => True
  | block :: rest =>
      0 < block.count ∧
      block.summary.WellFormed ∧
      block.summary.columns ≠ [] ∧
      initial.LeastFit (sortRegionColumns block.summary.columns)
        block.summary.rowCount block.start ∧
      initial.FitsColumns (sortRegionColumns block.summary.columns)
        block.start (block.count * block.summary.rowCount) ∧
      Lawful
        (initial.insertRepeated (sortRegionColumns block.summary.columns)
          block.start block.summary.rowCount block.count)
        rest

theorem finalView_append (initial : AllocationView)
    (left right : List PlannedSummaryBlock) :
    finalView initial (left ++ right) =
      finalView (finalView initial left) right := by
  induction left generalizing initial with
  | nil => rfl
  | cons block rest inductionHypothesis =>
      simp only [List.cons_append, finalView]
      exact inductionHypothesis _

theorem lawful_append (initial : AllocationView)
    (left right : List PlannedSummaryBlock) :
    Lawful initial (left ++ right) ↔
      Lawful initial left ∧ Lawful (finalView initial left) right := by
  induction left generalizing initial with
  | nil => simp [Lawful, finalView]
  | cons block rest inductionHypothesis =>
      simp only [List.cons_append, Lawful, finalView,
        inductionHypothesis]
      tauto

theorem Lawful.take
    {initial : AllocationView} {trace : List PlannedSummaryBlock}
    (hLawful : Lawful initial trace) (count : Nat) :
    Lawful initial (trace.take count) := by
  have hSplit : Lawful initial (trace.take count ++ trace.drop count) := by
    rw [List.take_append_drop]
    exact hLawful
  exact (lawful_append initial (trace.take count) (trace.drop count)).mp
    hSplit |>.1

theorem Lawful.drop
    {initial : AllocationView} {trace : List PlannedSummaryBlock}
    (hLawful : Lawful initial trace) (count : Nat) :
    Lawful (finalView initial (trace.take count)) (trace.drop count) := by
  have hSplit : Lawful initial (trace.take count ++ trace.drop count) := by
    rw [List.take_append_drop]
    exact hLawful
  exact (lawful_append initial (trace.take count) (trace.drop count)).mp
    hSplit |>.2

theorem Lawful.counts
    {initial : AllocationView} {trace : List PlannedSummaryBlock}
    (hLawful : Lawful initial trace) :
    trace.Forall fun block => 0 < block.count := by
  induction trace generalizing initial with
  | nil => simp
  | cons block rest inductionHypothesis =>
      rw [List.forall_cons]
      exact ⟨hLawful.1, inductionHypothesis hLawful.2.2.2.2.2⟩

theorem Lawful.finalView_valid
    {initial : AllocationView} {trace : List PlannedSummaryBlock}
    (hlawful : Lawful initial trace) (hvalid : initial.Valid) :
    (finalView initial trace).Valid := by
  induction trace generalizing initial with
  | nil => exact hvalid
  | cons block rest inductionHypothesis =>
      rcases hlawful with
        ⟨hcount, hwellFormed, hcolumns, hleast, hfits, hrest⟩
      obtain ⟨count, hcountEq⟩ := Nat.exists_eq_succ_of_ne_zero
        (Nat.ne_of_gt hcount)
      simp only [finalView]
      apply inductionHypothesis hrest
      have hfits' : initial.FitsColumns
          (sortRegionColumns block.summary.columns) block.start
          ((count + 1) * block.summary.rowCount) := by
        simpa only [hcountEq] using hfits
      have hnext := initial.insertRepeated_valid count hvalid hfits'
        (hwellFormed.2 hcolumns)
      simpa only [hcountEq] using hnext

/-- Whether a proposed block at `start` avoids every compact block already
placed. The formulation uses finite `List.Forall` predicates so concrete
reduced traces can discharge it with the kernel evaluator. -/
def FitsAfterAt (placed : List PlannedSummaryBlock)
    (block : PlannedSummaryBlock) (start length : ℕ) : Prop :=
  placed.Forall fun earlier =>
    block.summary.columns.Forall fun column =>
      column ∈ earlier.summary.columns →
        RowIntervalsDisjoint start length earlier.start
          (earlier.count * earlier.summary.rowCount)

theorem FitsAfterAt.monoLength
    {placed : List PlannedSummaryBlock} {block : PlannedSummaryBlock}
    {start outerLength length : ℕ}
    (hfits : FitsAfterAt placed block start outerLength)
    (hlength : length ≤ outerLength) :
    FitsAfterAt placed block start length := by
  apply hfits.imp
  intro earlier hearlier
  apply hearlier.imp
  intro column hcolumn hmember
  have hdisjoint := hcolumn hmember
  unfold RowIntervalsDisjoint at hdisjoint ⊢
  omega

/-- A finite, compact certificate that every stated start is exactly the least
fit after the preceding blocks. -/
def TraceLawfulAfter (placed : List PlannedSummaryBlock) :
    List PlannedSummaryBlock → Prop
  | [] => True
  | block :: rest =>
      0 < block.count ∧
      block.summary.WellFormed ∧
      block.summary.columns ≠ [] ∧
      FitsAfterAt placed block block.start
        (block.count * block.summary.rowCount) ∧
      (∀ candidate,
        FitsAfterAt placed block candidate block.summary.rowCount →
          block.start ≤ candidate) ∧
      TraceLawfulAfter (placed ++ [block]) rest

theorem traceLawfulAfter_append
    (placed left right : List PlannedSummaryBlock) :
    TraceLawfulAfter placed (left ++ right) ↔
      TraceLawfulAfter placed left ∧
        TraceLawfulAfter (placed ++ left) right := by
  induction left generalizing placed with
  | nil => simp [TraceLawfulAfter]
  | cons block rest inductionHypothesis =>
      simp only [List.cons_append, TraceLawfulAfter,
        inductionHypothesis, List.append_assoc]
      tauto

/-- Any prefix of a lawful compact trace is lawful after the same placed
prefix. -/
theorem traceLawfulAfter_take
    {placed trace : List PlannedSummaryBlock}
    (hlawful : TraceLawfulAfter placed trace) (count : Nat) :
    TraceLawfulAfter placed (trace.take count) := by
  induction trace generalizing placed count with
  | nil => simp [TraceLawfulAfter]
  | cons block rest inductionHypothesis =>
      cases count with
      | zero => simp [TraceLawfulAfter]
      | succ count =>
          rcases hlawful with
            ⟨hcount, hwellFormed, hcolumns, hfits, hleast, hrest⟩
          simp only [List.take_succ_cons, TraceLawfulAfter]
          exact ⟨hcount, hwellFormed, hcolumns, hfits, hleast,
            inductionHypothesis hrest count⟩

/-- A compact trace is lawful when every entry is lawful after the exact prefix
preceding it. This lets large concrete traces certify bounded groups of entries
independently, without repeatedly normalizing the entire suffix. -/
theorem traceLawfulAfter_of_steps
    (trace : List PlannedSummaryBlock)
    (hsteps : ∀ index (hindex : index < trace.length),
      TraceLawfulAfter (trace.take index)
        [trace.get ⟨index, hindex⟩]) :
    TraceLawfulAfter [] trace := by
  have hprefix : ∀ count, count ≤ trace.length →
      TraceLawfulAfter [] (trace.take count) := by
    intro count hcount
    induction count with
    | zero => simp [TraceLawfulAfter]
    | succ count inductionHypothesis =>
        have hindex : count < trace.length := by omega
        rw [List.take_add_one, traceLawfulAfter_append]
        refine ⟨inductionHypothesis (by omega), ?_⟩
        simpa [hindex] using hsteps count hindex
  simpa using hprefix trace.length (Nat.le_refl _)

/-- Assemble a compact trace from one-step certificates after an existing
planned prefix. -/
theorem traceLawfulAfter_of_steps_after
    (placed trace : List PlannedSummaryBlock)
    (hsteps : ∀ index (hindex : index < trace.length),
      TraceLawfulAfter (placed ++ trace.take index)
        [trace.get ⟨index, hindex⟩]) :
    TraceLawfulAfter placed trace := by
  have hprefix : ∀ count, count ≤ trace.length →
      TraceLawfulAfter placed (trace.take count) := by
    intro count hcount
    induction count with
    | zero => simp [TraceLawfulAfter]
    | succ count inductionHypothesis =>
        have hindex : count < trace.length := by omega
        rw [List.take_add_one, traceLawfulAfter_append]
        refine ⟨inductionHypothesis (by omega), ?_⟩
        simpa [List.append_assoc, hindex] using hsteps count hindex
  simpa using hprefix trace.length (Nat.le_refl _)

private theorem fitsColumns_finalView_iff_fitsAfterAt
    (initial : AllocationView) (placed : List PlannedSummaryBlock)
    (block : PlannedSummaryBlock) (start length : ℕ)
    (hcounts : placed.Forall fun earlier => 0 < earlier.count)
    (hlength : 0 < length) :
    (finalView initial placed).FitsColumns
        (sortRegionColumns block.summary.columns) start length ↔
      initial.FitsColumns (sortRegionColumns block.summary.columns) start
          length ∧ FitsAfterAt placed block start length := by
  induction placed generalizing initial with
  | nil => simp [finalView, FitsAfterAt]
  | cons earlier rest inductionHypothesis =>
      rw [List.forall_cons] at hcounts
      simp only [finalView]
      rw [inductionHypothesis _ hcounts.2,
        AllocationView.fitsColumns_insertRepeated_iff_of_pos
          hcounts.1 hlength]
      simp [FitsAfterAt, List.forall_iff_forall_mem,
        mem_sortRegionColumns_iff]
      constructor
      · rintro ⟨⟨hinitial, hearlier⟩, hrest⟩
        exact ⟨hinitial, hearlier, hrest⟩
      · rintro ⟨hinitial, hearlier, hrest⟩
        exact ⟨⟨hinitial, hearlier⟩, hrest⟩

private theorem emptyPlannerView_fitsColumns
    (columns : List RegionColumn) (start length : ℕ) :
    AllocationView.empty.FitsColumns
      columns start length := by
  intro column hcolumn
  simp [AllocationView.empty, Allocations.Fits]

theorem lawful_of_traceLawfulAfter
    (placed trace : List PlannedSummaryBlock)
    (hcounts : placed.Forall fun earlier => 0 < earlier.count)
    (hlawful : TraceLawfulAfter placed trace) :
    Lawful
      (finalView AllocationView.empty placed)
      trace := by
  induction trace generalizing placed with
  | nil => trivial
  | cons block rest inductionHypothesis =>
      rcases hlawful with
        ⟨hcount, hwellFormed, hcolumns, hfits, hleast, hrest⟩
      unfold Lawful
      refine ⟨hcount, hwellFormed, hcolumns, ?_, ?_, ?_⟩
      · constructor
        · rw [fitsColumns_finalView_iff_fitsAfterAt _ _ _ _ _ hcounts
              (hwellFormed.2 hcolumns)]
          exact ⟨emptyPlannerView_fitsColumns _ _ _,
            hfits.monoLength (Nat.le_mul_of_pos_left _ hcount)⟩
        · intro candidate hcandidateFits
          apply hleast candidate
          rw [fitsColumns_finalView_iff_fitsAfterAt _ _ _ _ _ hcounts
              (hwellFormed.2 hcolumns)] at hcandidateFits
          exact hcandidateFits.2
      · rw [fitsColumns_finalView_iff_fitsAfterAt _ _ _ _ _ hcounts
            (Nat.mul_pos hcount (hwellFormed.2 hcolumns))]
        constructor
        · exact emptyPlannerView_fitsColumns _ _ _
        · exact hfits
      · simpa [finalView_append, finalView] using
          inductionHypothesis (placed ++ [block])
            (by simpa using And.intro hcounts hcount) hrest

theorem slotSummaryBlocksState_eq
    (trace : List PlannedSummaryBlock)
    (initial : ℕ) (allocations : CircuitAllocations)
    (view : AllocationView)
    (hrepresents : view.Represents allocations)
    (hvalid : view.Valid) (hlawful : Lawful view trace) :
    let result := slotSummaryBlocksState (blocks trace) initial allocations
    result.1 = endpointFrom initial trace ∧
      (finalView view trace).Represents result.2 := by
  induction trace generalizing initial allocations view with
  | nil => exact ⟨rfl, hrepresents⟩
  | cons block rest inductionHypothesis =>
      rcases block with ⟨blockCount, summary, start⟩
      rcases hlawful with
        ⟨hcount, hwellFormed, hcolumns, hleast, hfits, hrest⟩
      obtain ⟨count, rfl⟩ := Nat.exists_eq_succ_of_ne_zero
        (Nat.ne_of_gt hcount)
      let first := slotSummaryStateRepeated (count + 1) [summary]
        initial allocations
      have hfirst := slotSummaryStateRepeated_single_eq count summary
        initial allocations view start hrepresents hvalid
        hwellFormed.1 hcolumns (hwellFormed.2 hcolumns) hleast hfits
      have hnextValid := view.insertRepeated_valid count hvalid hfits
        (hwellFormed.2 hcolumns)
      have htail := inductionHypothesis first.1 first.2
        (view.insertRepeated (sortRegionColumns summary.columns)
          start summary.rowCount (count + 1))
        hfirst.2 hnextValid hrest
      simp only [blocks, List.map_cons, slotSummaryBlocksState,
        endpointFrom, finalView]
      exact ⟨by rw [← hfirst.1]; exact htail.1, htail.2⟩

/-- A lawful compact trace computes both the exact start sequence and final
allocation view of its expanded summary blocks. -/
theorem slotShapeSummaryBlocks_eq
    (trace : List PlannedSummaryBlock)
    (allocations : CircuitAllocations) (view : AllocationView)
    (hrepresents : view.Represents allocations)
    (hvalid : view.Valid) (hlawful : Lawful view trace) :
    let result := slotShapeSummaryBlocks (blocks trace) allocations
    result.1 = starts trace ∧
      (finalView view trace).Represents result.2 := by
  induction trace generalizing allocations view with
  | nil => exact ⟨rfl, hrepresents⟩
  | cons block rest inductionHypothesis =>
      rcases block with ⟨blockCount, summary, start⟩
      rcases hlawful with
        ⟨hcount, hwellFormed, hcolumns, hleast, hfits, hrest⟩
      obtain ⟨count, rfl⟩ := Nat.exists_eq_succ_of_ne_zero
        (Nat.ne_of_gt hcount)
      have hfirst := slotShapeSummariesRepeated_single_eq count summary
        allocations view start hrepresents hvalid hwellFormed.1 hcolumns
        (hwellFormed.2 hcolumns) hleast hfits
      have hnextValid := view.insertRepeated_valid count hvalid hfits
        (hwellFormed.2 hcolumns)
      have htail := inductionHypothesis
        (slotShapeSummariesRepeated (count + 1) [summary] allocations).2
        (view.insertRepeated (sortRegionColumns summary.columns)
          start summary.rowCount (count + 1))
        hfirst.2 hnextValid hrest
      have htailStarts :
          (slotShapeSummaryBlocks
            (rest.map fun block => (block.count, block.summary))
            (slotShapeSummariesRepeated (count + 1) [summary]
              allocations).2).1 =
            rest.flatMap fun block => repeatedStarts block.start
              block.summary.rowCount block.count := by
        simpa only [blocks, starts] using htail.1
      simp only [blocks, List.map_cons, slotShapeSummaryBlocks,
        starts, List.flatMap_cons, finalView]
      exact ⟨by rw [hfirst.1, htailStarts], htail.2⟩

/-- Two lawful compact traces with the same endpoint and final allocation view
produce extensionally equivalent planner states. -/
theorem slotSummaryBlocksState_equivalent
    (left right : List PlannedSummaryBlock)
    (initial : ℕ) (allocations : CircuitAllocations)
    (view : AllocationView)
    (hrepresents : view.Represents allocations)
    (hvalid : view.Valid) (hleft : Lawful view left)
    (hright : Lawful view right)
    (hendpoint : endpointFrom initial left = endpointFrom initial right)
    (hfinalView : finalView view left = finalView view right) :
    SummaryStateEquivalent
      (slotSummaryBlocksState (blocks left) initial allocations)
      (slotSummaryBlocksState (blocks right) initial allocations) := by
  have hleftResult := slotSummaryBlocksState_eq left initial allocations view
    hrepresents hvalid hleft
  have hrightResult := slotSummaryBlocksState_eq right initial allocations view
    hrepresents hvalid hright
  constructor
  · exact hleftResult.1.trans (hendpoint.trans hrightResult.1.symm)
  · intro column
    rw [hleftResult.2 column, hrightResult.2 column, hfinalView]

theorem slotSummaryBlocksState_equivalent_of_represents
    (left right : List PlannedSummaryBlock)
    (leftInitial rightInitial : ℕ)
    (leftAllocations rightAllocations : CircuitAllocations)
    (view : AllocationView)
    (hleftRepresents : view.Represents leftAllocations)
    (hrightRepresents : view.Represents rightAllocations)
    (hvalid : view.Valid) (hleft : Lawful view left)
    (hright : Lawful view right)
    (hendpoint : endpointFrom leftInitial left =
      endpointFrom rightInitial right)
    (hfinalView : finalView view left = finalView view right) :
    SummaryStateEquivalent
      (slotSummaryBlocksState (blocks left) leftInitial leftAllocations)
      (slotSummaryBlocksState (blocks right) rightInitial rightAllocations) := by
  have hleftResult := slotSummaryBlocksState_eq left leftInitial
    leftAllocations view hleftRepresents hvalid hleft
  have hrightResult := slotSummaryBlocksState_eq right rightInitial
    rightAllocations view hrightRepresents hvalid hright
  constructor
  · exact hleftResult.1.trans (hendpoint.trans hrightResult.1.symm)
  · intro column
    rw [hleftResult.2 column, hrightResult.2 column, hfinalView]

end PlannedSummaryBlock

theorem slotSummaryEndFromWith_cons
    (initial : ℕ) (head : RegionShapeSummary)
    (tail : List RegionShapeSummary)
    (allocations : CircuitAllocations) :
    slotSummaryEndFromWith initial (head :: tail) allocations =
      let placed := placeSummary head allocations
      slotSummaryEndFromWith
        (max initial (placed.1.getD 0 + head.rowCount)) tail placed.2 := by
  generalize hplaced : placeSummary head allocations = placed
  rcases placed with ⟨row, updated⟩
  unfold slotSummaryEndFromWith
  simp only [slotShapeSummariesFrom, hplaced, List.zip_cons_cons,
    List.map_cons, List.foldl_cons]

/-- Exact end row obtained by slotting an index-free reduced summary. -/
def slotSummaryEndFrom (summaries : List RegionShapeSummary)
    (allocations : CircuitAllocations) : ℕ :=
  slotSummaryEndFromWith 0 summaries allocations

/-- Placement-equivalent summaries may be exchanged without changing either the
endpoint or the allocator state seen by the suffix. -/
theorem slotSummaryEndFromWith_swap_of_placementEquivalent
    (initial : ℕ) (left right : RegionShapeSummary)
    (tail : List RegionShapeSummary) (allocations : CircuitAllocations)
    (hequivalent : left.PlacementEquivalent right) :
    slotSummaryEndFromWith initial (left :: right :: tail) allocations =
      slotSummaryEndFromWith initial (right :: left :: tail) allocations := by
  have hplace : ∀ current,
      placeSummary left current = placeSummary right current :=
    placeSummary_eq_of_placementEquivalent hequivalent
  simp only [slotSummaryEndFromWith_cons, hplace, hequivalent.2]

theorem slotSummaryStateFromWith_swap_of_placementEquivalent
    (initial : ℕ) (left right : RegionShapeSummary)
    (tail : List RegionShapeSummary) (allocations : CircuitAllocations)
    (hequivalent : left.PlacementEquivalent right) :
    slotSummaryStateFromWith initial (left :: right :: tail) allocations =
      slotSummaryStateFromWith initial (right :: left :: tail) allocations := by
  have hplace : ∀ current,
      placeSummary left current = placeSummary right current :=
    placeSummary_eq_of_placementEquivalent hequivalent
  simp only [slotSummaryStateFromWith, hplace, hequivalent.2]

/-- Swapping two disjoint regions changes neither their individual placements nor
the final endpoint, including the placement of every following region. -/
theorem slotSummaryEndFromWith_swap
    (initial : ℕ)
    (left right : RegionShapeSummary)
    (tail : List RegionShapeSummary)
    (allocations : CircuitAllocations)
    (hvalid : allocations.Valid)
    (hleftNodup : left.columns.Nodup)
    (hrightNodup : right.columns.Nodup)
    (hleftLength : 0 < left.rowCount)
    (hrightLength : 0 < right.rowCount)
    (hdisjoint : List.Disjoint left.columns right.columns)
    (htail : tail.Forall RegionShapeSummary.WellFormed) :
    slotSummaryEndFromWith initial (left :: right :: tail) allocations =
      slotSummaryEndFromWith initial (right :: left :: tail) allocations := by
  have hcommute := placeSummary_commute left right allocations hvalid
    hleftNodup hrightNodup hleftLength hrightLength hdisjoint
  generalize hleftFirst : placeSummary left allocations = leftFirst
    at hcommute
  rcases leftFirst with ⟨leftRow, leftAllocations⟩
  generalize hrightFirst : placeSummary right allocations = rightFirst
    at hcommute
  rcases rightFirst with ⟨rightRow, rightAllocations⟩
  generalize hleftThenRight :
    placeSummary right leftAllocations = leftThenRight at hcommute
  rcases leftThenRight with
    ⟨rightRowAfterLeft, leftThenRightAllocations⟩
  generalize hrightThenLeft :
    placeSummary left rightAllocations = rightThenLeft at hcommute
  rcases rightThenLeft with
    ⟨leftRowAfterRight, rightThenLeftAllocations⟩
  simp only [hleftThenRight, hrightThenLeft] at hcommute
  have hleftLaw := placeSummary_law left allocations hvalid
    hleftNodup hleftLength
  have hrightLaw := placeSummary_law right allocations hvalid
    hrightNodup hrightLength
  rw [hleftFirst] at hleftLaw
  rw [hrightFirst] at hrightLaw
  have hleftThenRightLaw := placeSummary_law right leftAllocations
    hleftLaw.1.valid hrightNodup hrightLength
  have hrightThenLeftLaw := placeSummary_law left rightAllocations
    hrightLaw.1.valid hleftNodup hleftLength
  rw [hleftThenRight] at hleftThenRightLaw
  rw [hrightThenLeft] at hrightThenLeftLaw
  have hsuffix := slotShapeSummariesFrom_equivalent tail
    leftThenRightAllocations rightThenLeftAllocations htail
    hleftThenRightLaw.1.valid hrightThenLeftLaw.1.valid hcommute.2.2
  unfold slotSummaryEndFromWith
  simp only [slotShapeSummariesFrom, hleftFirst, hrightFirst,
    hleftThenRight, hrightThenLeft]
  rw [hcommute.1, hcommute.2.1, hsuffix.1]
  simp only [List.zip_cons_cons, List.map_cons, List.foldl_cons]
  congr 1
  rw [Nat.max_assoc, Nat.max_assoc,
    Nat.max_comm (leftRowAfterRight.getD 0 + left.rowCount)
      (rightRowAfterLeft.getD 0 + right.rowCount)]

/-- Swapping two disjoint well-formed summaries preserves the complete planner
state up to extensional allocation-map equality. -/
theorem slotSummaryStateFromWith_swap
    (initial : ℕ) (left right : RegionShapeSummary)
    (tail : List RegionShapeSummary)
    (allocations : CircuitAllocations)
    (hvalid : allocations.Valid)
    (hleft : left.WellFormed) (hright : right.WellFormed)
    (hdisjoint : List.Disjoint left.columns right.columns)
    (htail : tail.Forall RegionShapeSummary.WellFormed) :
    SummaryStateEquivalent
      (slotSummaryStateFromWith initial (left :: right :: tail) allocations)
      (slotSummaryStateFromWith initial (right :: left :: tail) allocations) := by
  by_cases hleftColumns : left.columns = []
  · have hleftPlace : ∀ current,
        placeSummary left current = (some 0, current) := by
      intro current
      simp [placeSummary, hleftColumns, sortRegionColumns, firstFit]
    generalize hrightPlace : placeSummary right allocations = rightResult
    rcases rightResult with ⟨rightRow, updated⟩
    have hrightLaw := placeSummary_valid right allocations hvalid hright
    rw [hrightPlace] at hrightLaw
    have hprefix : SummaryStateEquivalent
        (max (max initial left.rowCount)
            (rightRow.getD 0 + right.rowCount), updated)
        (max (max initial (rightRow.getD 0 + right.rowCount))
            left.rowCount, updated) := by
      exact ⟨by omega, CircuitAllocations.Equivalent.refl updated⟩
    simpa only [slotSummaryStateFromWith, hleftPlace, hrightPlace,
      Option.getD_some, zero_add] using
        slotSummaryStateFromWith_equivalent tail htail hrightLaw hrightLaw
          hprefix
  · by_cases hrightColumns : right.columns = []
    · have hrightPlace : ∀ current,
          placeSummary right current = (some 0, current) := by
        intro current
        simp [placeSummary, hrightColumns, sortRegionColumns, firstFit]
      generalize hleftPlace : placeSummary left allocations = leftResult
      rcases leftResult with ⟨leftRow, updated⟩
      have hleftLaw := placeSummary_valid left allocations hvalid hleft
      rw [hleftPlace] at hleftLaw
      have hprefix : SummaryStateEquivalent
          (max (max initial (leftRow.getD 0 + left.rowCount))
              right.rowCount, updated)
          (max (max initial right.rowCount)
              (leftRow.getD 0 + left.rowCount), updated) := by
        exact ⟨by omega, CircuitAllocations.Equivalent.refl updated⟩
      simpa only [slotSummaryStateFromWith, hleftPlace, hrightPlace,
        Option.getD_some, zero_add] using
          slotSummaryStateFromWith_equivalent tail htail hleftLaw hleftLaw
            hprefix
    · have hcommute := placeSummary_commute left right allocations hvalid
        hleft.1 hright.1 (hleft.2 hleftColumns)
        (hright.2 hrightColumns) hdisjoint
      generalize hleftFirst : placeSummary left allocations = leftFirst
        at hcommute
      rcases leftFirst with ⟨leftRow, leftAllocations⟩
      generalize hrightFirst : placeSummary right allocations = rightFirst
        at hcommute
      rcases rightFirst with ⟨rightRow, rightAllocations⟩
      generalize hleftThenRight :
        placeSummary right leftAllocations = leftThenRight at hcommute
      rcases leftThenRight with
        ⟨rightRowAfterLeft, leftThenRightAllocations⟩
      generalize hrightThenLeft :
        placeSummary left rightAllocations = rightThenLeft at hcommute
      rcases rightThenLeft with
        ⟨leftRowAfterRight, rightThenLeftAllocations⟩
      simp only [hleftThenRight, hrightThenLeft] at hcommute
      have hleftLaw := placeSummary_law left allocations hvalid hleft.1
        (hleft.2 hleftColumns)
      have hrightLaw := placeSummary_law right allocations hvalid hright.1
        (hright.2 hrightColumns)
      rw [hleftFirst] at hleftLaw
      rw [hrightFirst] at hrightLaw
      have hleftThenRightLaw := placeSummary_law right leftAllocations
        hleftLaw.1.valid hright.1 (hright.2 hrightColumns)
      have hrightThenLeftLaw := placeSummary_law left rightAllocations
        hrightLaw.1.valid hleft.1 (hleft.2 hleftColumns)
      rw [hleftThenRight] at hleftThenRightLaw
      rw [hrightThenLeft] at hrightThenLeftLaw
      have hprefix : SummaryStateEquivalent
          (max (max initial (leftRow.getD 0 + left.rowCount))
              (rightRowAfterLeft.getD 0 + right.rowCount),
            leftThenRightAllocations)
          (max (max initial (rightRow.getD 0 + right.rowCount))
              (leftRowAfterRight.getD 0 + left.rowCount),
            rightThenLeftAllocations) := by
        constructor
        · rw [hcommute.1, hcommute.2.1]
          omega
        · exact hcommute.2.2
      simpa only [slotSummaryStateFromWith, hleftFirst, hrightFirst,
        hleftThenRight, hrightThenLeft] using
          slotSummaryStateFromWith_equivalent tail htail
            hleftThenRightLaw.1.valid hrightThenLeftLaw.1.valid hprefix

/-- Reordering a pairwise-commutative summary stream preserves the complete
planner state up to extensional allocation equality. -/
theorem slotSummaryStateFromWith_perm
    {left right : List RegionShapeSummary} (hperm : left.Perm right)
    (hwellFormed : left.Forall RegionShapeSummary.WellFormed)
    (hcommutative : ∀ first, first ∈ left → ∀ second, second ∈ left →
      first = second ∨ List.Disjoint first.columns second.columns)
    (initial : ℕ) (allocations : CircuitAllocations)
    (hvalid : allocations.Valid) :
    SummaryStateEquivalent
      (slotSummaryStateFromWith initial left allocations)
      (slotSummaryStateFromWith initial right allocations) := by
  induction hperm generalizing initial allocations with
  | nil => exact SummaryStateEquivalent.refl _
  | cons head hperm inductionHypothesis =>
      rw [List.forall_cons] at hwellFormed
      generalize hplaced : placeSummary head allocations = placed
      rcases placed with ⟨row, updated⟩
      have hupdatedValid : updated.Valid := by
        have hresult := placeSummary_valid head allocations hvalid
          hwellFormed.1
        rw [hplaced] at hresult
        exact hresult
      simpa only [slotSummaryStateFromWith, hplaced] using
        inductionHypothesis hwellFormed.2 (by
          intro first hfirst second hsecond
          exact hcommutative first (by simp [hfirst]) second
            (by simp [hsecond]))
          (max initial (row.getD 0 + head.rowCount)) updated hupdatedValid
  | swap first second rest =>
      rw [List.forall_cons, List.forall_cons] at hwellFormed
      have hpair := hcommutative first (by simp) second (by simp)
      rcases hpair with rfl | hdisjoint
      · exact SummaryStateEquivalent.refl _
      · exact (slotSummaryStateFromWith_swap initial first second rest
          allocations hvalid hwellFormed.2.1 hwellFormed.1 hdisjoint
          hwellFormed.2.2).symm
  | @trans left middle right hleft hright leftInduction rightInduction =>
      have hmiddleWellFormed :
          middle.Forall RegionShapeSummary.WellFormed := by
        rw [List.forall_iff_forall_mem]
        intro summary hsummary
        exact List.forall_iff_forall_mem.mp hwellFormed summary
          (hleft.mem_iff.mpr hsummary)
      have hmiddleCommutative : ∀
          (first : RegionShapeSummary), first ∈ middle →
          ∀ (second : RegionShapeSummary), second ∈ middle →
          first = second ∨ List.Disjoint first.columns second.columns := by
        intro first hfirst second hsecond
        exact hcommutative first (hleft.mem_iff.mpr hfirst) second
          (hleft.mem_iff.mpr hsecond)
      exact (leftInduction hwellFormed hcommutative initial allocations
        hvalid).trans
          (rightInduction hmiddleWellFormed hmiddleCommutative initial
            allocations hvalid)

/-- The zero-based endpoint specialization of disjoint-region commutation. -/
theorem slotSummaryEndFrom_swap
    (left right : RegionShapeSummary)
    (tail : List RegionShapeSummary)
    (allocations : CircuitAllocations)
    (hvalid : allocations.Valid)
    (hleftNodup : left.columns.Nodup)
    (hrightNodup : right.columns.Nodup)
    (hleftLength : 0 < left.rowCount)
    (hrightLength : 0 < right.rowCount)
    (hdisjoint : List.Disjoint left.columns right.columns)
    (htail : tail.Forall RegionShapeSummary.WellFormed) :
    slotSummaryEndFrom (left :: right :: tail) allocations =
      slotSummaryEndFrom (right :: left :: tail) allocations := by
  exact slotSummaryEndFromWith_swap 0 left right tail allocations hvalid
    hleftNodup hrightNodup hleftLength hrightLength hdisjoint htail

/-- The disjoint swap theorem with the empty-region case derived from summary
well-formedness. -/
theorem slotSummaryEndFromWith_swap_of_wellFormed
    (initial : ℕ) (left right : RegionShapeSummary)
    (tail : List RegionShapeSummary)
    (allocations : CircuitAllocations)
    (hvalid : allocations.Valid)
    (hleft : left.WellFormed) (hright : right.WellFormed)
    (hdisjoint : List.Disjoint left.columns right.columns)
    (htail : tail.Forall RegionShapeSummary.WellFormed) :
    slotSummaryEndFromWith initial (left :: right :: tail) allocations =
      slotSummaryEndFromWith initial (right :: left :: tail) allocations := by
  by_cases hleftColumns : left.columns = []
  · have hleftPlace : ∀ current,
        placeSummary left current = (some 0, current) := by
      intro current
      simp [placeSummary, hleftColumns, sortRegionColumns, firstFit]
    generalize hrightPlace : placeSummary right allocations = rightResult
    rcases rightResult with ⟨rightRow, updated⟩
    unfold slotSummaryEndFromWith
    simp only [slotShapeSummariesFrom, hleftPlace, hrightPlace,
      List.zip_cons_cons, List.map_cons, List.foldl_cons]
    congr 1
    rw [Nat.max_assoc, Nat.max_assoc,
      Nat.max_comm ((some 0).getD 0 + left.rowCount)
        (rightRow.getD 0 + right.rowCount)]
  · by_cases hrightColumns : right.columns = []
    · have hrightPlace : ∀ current,
          placeSummary right current = (some 0, current) := by
        intro current
        simp [placeSummary, hrightColumns, sortRegionColumns, firstFit]
      generalize hleftPlace : placeSummary left allocations = leftResult
      rcases leftResult with ⟨leftRow, updated⟩
      unfold slotSummaryEndFromWith
      simp only [slotShapeSummariesFrom, hrightPlace, hleftPlace,
        List.zip_cons_cons, List.map_cons, List.foldl_cons]
      congr 1
      rw [Nat.max_assoc, Nat.max_assoc,
        Nat.max_comm (leftRow.getD 0 + left.rowCount)
          ((some 0).getD 0 + right.rowCount)]
    · exact slotSummaryEndFromWith_swap initial left right tail
        allocations hvalid hleft.1 hright.1 (hleft.2 hleftColumns)
        (hright.2 hrightColumns) hdisjoint htail

/-- Every pair of summaries may be reordered without changing V1 placement: equal
summaries trivially commute, while distinct summaries use disjoint columns. -/
def PairwisePlacementCommutative
    (summaries : List RegionShapeSummary) : Prop :=
  ∀ left, left ∈ summaries → ∀ right, right ∈ summaries →
    left = right ∨ List.Disjoint left.columns right.columns

/-- Any permutation of a pairwise-commutative summary block has the same exact
endpoint, even when followed by an arbitrary well-formed suffix. -/
theorem slotSummaryEndFromWith_perm
    {left right : List RegionShapeSummary} (hperm : left.Perm right)
    (hwellFormed : left.Forall RegionShapeSummary.WellFormed)
    (hcommutative : PairwisePlacementCommutative left)
    (initial : ℕ) (allocations : CircuitAllocations)
    (hvalid : allocations.Valid) (tail : List RegionShapeSummary)
    (htail : tail.Forall RegionShapeSummary.WellFormed) :
    slotSummaryEndFromWith initial (left ++ tail) allocations =
      slotSummaryEndFromWith initial (right ++ tail) allocations := by
  induction hperm generalizing initial allocations tail with
  | nil => rfl
  | cons head hperm inductionHypothesis =>
      rw [List.forall_cons] at hwellFormed
      generalize hplaced : placeSummary head allocations = placed
      rcases placed with ⟨row, updated⟩
      have hupdatedValid : updated.Valid := by
        have hresult := placeSummary_valid head allocations hvalid
          hwellFormed.1
        rw [hplaced] at hresult
        exact hresult
      have hrest := inductionHypothesis hwellFormed.2 (by
        intro first hfirst second hsecond
        exact hcommutative first (by simp [hfirst]) second (by simp [hsecond]))
        (max initial (row.getD 0 + head.rowCount)) updated hupdatedValid
        tail htail
      simpa only [List.cons_append, slotSummaryEndFromWith_cons,
        hplaced] using hrest
  | swap first second rest =>
      rw [List.forall_cons, List.forall_cons] at hwellFormed
      have hpair := hcommutative first (by simp) second (by simp)
      rcases hpair with rfl | hdisjoint
      · rfl
      · symm
        simpa only [List.cons_append] using
          slotSummaryEndFromWith_swap_of_wellFormed initial first second
            (rest ++ tail) allocations hvalid hwellFormed.2.1
            hwellFormed.1 hdisjoint (by
              rw [List.forall_append]
              exact ⟨hwellFormed.2.2, htail⟩)
  | trans hleft hright leftInduction rightInduction =>
      exact (leftInduction hwellFormed hcommutative initial allocations
        hvalid tail htail).trans
          (rightInduction (by
              rw [List.forall_iff_forall_mem]
              intro summary hsummary
              exact List.forall_iff_forall_mem.mp hwellFormed summary
                (hleft.mem_iff.mpr hsummary)) (by
              intro first hfirst second hsecond
              exact hcommutative first (hleft.mem_iff.mpr hfirst)
                second (hleft.mem_iff.mpr hsecond)) initial allocations
            hvalid tail htail)

/-- Move one summary across a prefix of summaries that commute with it. -/
theorem slotSummaryEndFromWith_bubble
    (pivot : RegionShapeSummary)
    (before suffix tail : List RegionShapeSummary)
    (hwellBefore : before.Forall RegionShapeSummary.WellFormed)
    (hwellPivot : pivot.WellFormed)
    (hcommutes : ∀ item, item ∈ before →
      item.PlacementEquivalent pivot ∨
        List.Disjoint item.columns pivot.columns)
    (initial : ℕ) (allocations : CircuitAllocations)
    (hvalid : allocations.Valid)
    (hwellSuffix : suffix.Forall RegionShapeSummary.WellFormed)
    (hwellTail : tail.Forall RegionShapeSummary.WellFormed) :
    slotSummaryEndFromWith initial
        ((before ++ pivot :: suffix) ++ tail) allocations =
      slotSummaryEndFromWith initial
        ((pivot :: before ++ suffix) ++ tail) allocations := by
  induction before generalizing initial allocations with
  | nil => rfl
  | cons head rest inductionHypothesis =>
      rw [List.forall_cons] at hwellBefore
      generalize hplaced : placeSummary head allocations = placed
      rcases placed with ⟨row, updated⟩
      have hupdatedValid : updated.Valid := by
        have hresult := placeSummary_valid head allocations hvalid
          hwellBefore.1
        rw [hplaced] at hresult
        exact hresult
      have hrest := inductionHypothesis hwellBefore.2 (by
          intro item hitem
          exact hcommutes item (by simp [hitem]))
        (max initial (row.getD 0 + head.rowCount)) updated hupdatedValid
      have hbubbled :
          slotSummaryEndFromWith initial
              ((head :: rest ++ pivot :: suffix) ++ tail) allocations =
            slotSummaryEndFromWith initial
              ((head :: pivot :: rest ++ suffix) ++ tail) allocations := by
        simpa only [List.cons_append, slotSummaryEndFromWith_cons,
          hplaced] using hrest
      have hpair := hcommutes head (by simp)
      rcases hpair with hequivalent | hdisjoint
      · exact hbubbled.trans (by
          simpa only [List.cons_append] using
            slotSummaryEndFromWith_swap_of_placementEquivalent initial head
              pivot ((rest ++ suffix) ++ tail) allocations hequivalent)
      · exact hbubbled.trans (by
          simpa only [List.cons_append] using
            slotSummaryEndFromWith_swap_of_wellFormed initial head pivot
              ((rest ++ suffix) ++ tail) allocations hvalid hwellBefore.1
              hwellPivot hdisjoint (by
                rw [List.forall_append, List.forall_append]
                exact ⟨⟨hwellBefore.2, hwellSuffix⟩, hwellTail⟩))

/-- Complete-state form of bubbling one summary across a commuting prefix. -/
theorem slotSummaryStateFromWith_bubble
    (pivot : RegionShapeSummary)
    (before suffix : List RegionShapeSummary)
    (hwellBefore : before.Forall RegionShapeSummary.WellFormed)
    (hwellPivot : pivot.WellFormed)
    (hcommutes : ∀ item, item ∈ before →
      item.PlacementEquivalent pivot ∨
        List.Disjoint item.columns pivot.columns)
    (initial : ℕ) (allocations : CircuitAllocations)
    (hvalid : allocations.Valid)
    (hwellSuffix : suffix.Forall RegionShapeSummary.WellFormed) :
    SummaryStateEquivalent
      (slotSummaryStateFromWith initial
        (before ++ pivot :: suffix) allocations)
      (slotSummaryStateFromWith initial
        (pivot :: before ++ suffix) allocations) := by
  induction before generalizing initial allocations with
  | nil => exact SummaryStateEquivalent.refl _
  | cons head rest inductionHypothesis =>
      rw [List.forall_cons] at hwellBefore
      generalize hplaced : placeSummary head allocations = placed
      rcases placed with ⟨row, updated⟩
      have hupdatedValid : updated.Valid := by
        have hresult := placeSummary_valid head allocations hvalid
          hwellBefore.1
        rw [hplaced] at hresult
        exact hresult
      have hrest := inductionHypothesis hwellBefore.2 (by
          intro item hitem
          exact hcommutes item (by simp [hitem]))
        (max initial (row.getD 0 + head.rowCount)) updated hupdatedValid
      have hbubbled : SummaryStateEquivalent
          (slotSummaryStateFromWith initial
            (head :: rest ++ pivot :: suffix) allocations)
          (slotSummaryStateFromWith initial
            (head :: pivot :: rest ++ suffix) allocations) := by
        simpa only [List.cons_append, slotSummaryStateFromWith, hplaced]
          using hrest
      have hpair := hcommutes head (by simp)
      rcases hpair with hequivalent | hdisjoint
      · exact hbubbled.trans (by
          have hswap := slotSummaryStateFromWith_swap_of_placementEquivalent
            initial head pivot (rest ++ suffix) allocations hequivalent
          simpa only [List.cons_append, hswap] using
            SummaryStateEquivalent.refl
              (slotSummaryStateFromWith initial
                (pivot :: head :: rest ++ suffix) allocations))
      · exact hbubbled.trans (by
          simpa only [List.cons_append] using
            slotSummaryStateFromWith_swap initial head pivot
              (rest ++ suffix) allocations hvalid hwellBefore.1 hwellPivot
              hdisjoint (by
                rw [List.forall_append]
                exact ⟨hwellBefore.2, hwellSuffix⟩))

theorem perm_bubble (pivot : RegionShapeSummary)
    (before suffix : List RegionShapeSummary) :
    (before ++ pivot :: suffix).Perm (pivot :: before ++ suffix) := by
  induction before with
  | nil => rfl
  | cons head rest inductionHypothesis =>
      exact (inductionHypothesis.cons head).trans
        (List.Perm.swap pivot head (rest ++ suffix))

/-- For two key-sorted permutations, V1's endpoint is insensitive to the order
within tied-key runs whenever tied summaries are placement-equivalent or
column-disjoint. -/
theorem slotSummaryEndFromWith_eq_of_sorted_perm_interchangeable
    {K : Type} [LinearOrder K] (key : RegionShapeSummary → K)
    {left right : List RegionShapeSummary}
    (hperm : left.Perm right)
    (hsortedLeft : (left.map key).SortedLE)
    (hsortedRight : (right.map key).SortedLE)
    (hwellFormed : left.Forall RegionShapeSummary.WellFormed)
    (hties : ∀ first, first ∈ left → ∀ second, second ∈ left →
      key first = key second →
        first.PlacementEquivalent second ∨
          List.Disjoint first.columns second.columns)
    (initial : ℕ) (allocations : CircuitAllocations)
    (hvalid : allocations.Valid) (tail : List RegionShapeSummary)
    (hwellTail : tail.Forall RegionShapeSummary.WellFormed) :
    slotSummaryEndFromWith initial (left ++ tail) allocations =
      slotSummaryEndFromWith initial (right ++ tail) allocations := by
  induction left generalizing right initial allocations tail with
  | nil =>
      have : right = [] := hperm.symm.eq_nil
      subst right
      rfl
  | cons pivot rest inductionHypothesis =>
      have hpivotRight : pivot ∈ right := hperm.subset (by simp)
      obtain ⟨before, suffix, hright⟩ := List.mem_iff_append.mp hpivotRight
      subst right
      rw [List.forall_cons] at hwellFormed
      have hsortedLeftCons := hsortedLeft
      rw [List.sortedLE_iff_pairwise, List.map_cons,
        List.pairwise_cons] at hsortedLeftCons
      have hsortedRightAppend := hsortedRight
      rw [List.sortedLE_iff_pairwise, List.map_append, List.map_cons,
        List.pairwise_append] at hsortedRightAppend
      have hkeysEqual :
          (key pivot :: rest.map key) =
            before.map key ++ key pivot :: suffix.map key :=
        List.Perm.eq_of_sortedLE hsortedLeft (by
          simpa only [List.map_append, List.map_cons] using hsortedRight)
          (by simpa only [List.map_append, List.map_cons] using hperm.map key)
      have hlower : ∀ item,
          item ∈ before ++ pivot :: suffix → key pivot ≤ key item := by
        intro item hitem
        cases before with
        | nil =>
            simp only [List.nil_append] at hitem
            rw [List.mem_cons] at hitem
            rcases hitem with rfl | hitem
            · exact le_rfl
            · exact List.pairwise_cons.mp hsortedRightAppend.2.1 |>.1
                (key item) (List.mem_map.mpr ⟨item, hitem, rfl⟩)
        | cons head beforeRest =>
            simp only [List.map_cons, List.cons_append, List.cons.injEq]
              at hkeysEqual
            simp only [List.cons_append] at hitem
            rw [List.mem_cons] at hitem
            rcases hitem with rfl | hitem
            · exact hkeysEqual.1.le
            · have hrightCons :
                  (key head :: (beforeRest ++ pivot :: suffix).map key).Pairwise
                    (· ≤ ·) := by
                simpa only [List.sortedLE_iff_pairwise, List.map_cons] using
                  hsortedRight
              rw [List.pairwise_cons] at hrightCons
              exact hkeysEqual.1.le.trans
                (hrightCons.1 (key item)
                  (List.mem_map.mpr ⟨item, hitem, rfl⟩))
      have hbeforeKeys : ∀ item, item ∈ before →
          key item = key pivot := by
        intro item hitem
        apply le_antisymm
        · exact hsortedRightAppend.2.2 (key item)
            (List.mem_map.mpr ⟨item, hitem, rfl⟩) (key pivot) (by simp)
        · exact hlower item (by simp [hitem])
      have hwellRight :
          (before ++ pivot :: suffix).Forall
            RegionShapeSummary.WellFormed := by
        rw [List.forall_iff_forall_mem]
        intro summary hsummary
        exact List.forall_iff_forall_mem.mp
          (by rw [List.forall_cons]; exact hwellFormed) summary
          (hperm.mem_iff.mpr hsummary)
      rw [List.forall_append, List.forall_cons] at hwellRight
      have hbubble := slotSummaryEndFromWith_bubble pivot before suffix tail
        hwellRight.1 hwellFormed.1 (by
          intro item hitem
          have hpair := hties pivot (by simp) item
            (hperm.mem_iff.mpr (by simp [hitem]))
            (hbeforeKeys item hitem).symm
          rcases hpair with heq | hdisjoint
          · exact Or.inl heq.symm
          · exact Or.inr hdisjoint.symm)
        initial allocations hvalid hwellRight.2.2 hwellTail
      have htailPerm : rest.Perm (before ++ suffix) := by
        apply List.Perm.cons_inv
        exact hperm.trans (perm_bubble pivot before suffix)
      have htailSorted : ((before ++ suffix).map key).SortedLE := by
        rw [List.sortedLE_iff_pairwise, List.map_append,
          List.pairwise_append]
        exact ⟨hsortedRightAppend.1,
          (List.pairwise_cons.mp hsortedRightAppend.2.1).2, by
            intro leftKey hleftKey rightKey hrightKey
            exact hsortedRightAppend.2.2 leftKey hleftKey rightKey
              (by simp [hrightKey])⟩
      generalize hplaced : placeSummary pivot allocations = placed
      rcases placed with ⟨row, updated⟩
      have hupdatedValid : updated.Valid := by
        have hresult := placeSummary_valid pivot allocations hvalid
          hwellFormed.1
        rw [hplaced] at hresult
        exact hresult
      have hrest := inductionHypothesis htailPerm (by
          rw [List.sortedLE_iff_pairwise]
          exact hsortedLeftCons.2)
        htailSorted hwellFormed.2 (by
          intro first hfirst second hsecond hkey
          exact hties first (by simp [hfirst]) second (by simp [hsecond]) hkey)
        (max initial (row.getD 0 + pivot.rowCount)) updated
        hupdatedValid tail hwellTail
      have hconsRest :
          slotSummaryEndFromWith initial
              ((pivot :: rest) ++ tail) allocations =
            slotSummaryEndFromWith initial
              ((pivot :: before ++ suffix) ++ tail) allocations := by
        simpa only [List.cons_append, slotSummaryEndFromWith_cons,
          hplaced] using hrest
      exact hconsRest.trans hbubble.symm

/-- Complete-state form of sorted-permutation interchangeability. -/
theorem slotSummaryStateFromWith_eq_of_sorted_perm_interchangeable
    {K : Type} [LinearOrder K] (key : RegionShapeSummary → K)
    {left right : List RegionShapeSummary}
    (hperm : left.Perm right)
    (hsortedLeft : (left.map key).SortedLE)
    (hsortedRight : (right.map key).SortedLE)
    (hwellFormed : left.Forall RegionShapeSummary.WellFormed)
    (hties : ∀ first, first ∈ left → ∀ second, second ∈ left →
      key first = key second →
        first.PlacementEquivalent second ∨
          List.Disjoint first.columns second.columns)
    (initial : ℕ) (allocations : CircuitAllocations)
    (hvalid : allocations.Valid) :
    SummaryStateEquivalent
      (slotSummaryStateFromWith initial left allocations)
      (slotSummaryStateFromWith initial right allocations) := by
  induction left generalizing right initial allocations with
  | nil =>
      have : right = [] := hperm.symm.eq_nil
      subst right
      exact SummaryStateEquivalent.refl _
  | cons pivot rest inductionHypothesis =>
      have hpivotRight : pivot ∈ right := hperm.subset (by simp)
      obtain ⟨before, suffix, hright⟩ := List.mem_iff_append.mp hpivotRight
      subst right
      rw [List.forall_cons] at hwellFormed
      have hsortedLeftCons := hsortedLeft
      rw [List.sortedLE_iff_pairwise, List.map_cons,
        List.pairwise_cons] at hsortedLeftCons
      have hsortedRightAppend := hsortedRight
      rw [List.sortedLE_iff_pairwise, List.map_append, List.map_cons,
        List.pairwise_append] at hsortedRightAppend
      have hkeysEqual :
          (key pivot :: rest.map key) =
            before.map key ++ key pivot :: suffix.map key :=
        List.Perm.eq_of_sortedLE hsortedLeft (by
          simpa only [List.map_append, List.map_cons] using hsortedRight)
          (by simpa only [List.map_append, List.map_cons] using hperm.map key)
      have hlower : ∀ item,
          item ∈ before ++ pivot :: suffix → key pivot ≤ key item := by
        intro item hitem
        cases before with
        | nil =>
            simp only [List.nil_append] at hitem
            rw [List.mem_cons] at hitem
            rcases hitem with rfl | hitem
            · exact le_rfl
            · exact List.pairwise_cons.mp hsortedRightAppend.2.1 |>.1
                (key item) (List.mem_map.mpr ⟨item, hitem, rfl⟩)
        | cons head beforeRest =>
            simp only [List.map_cons, List.cons_append, List.cons.injEq]
              at hkeysEqual
            simp only [List.cons_append] at hitem
            rw [List.mem_cons] at hitem
            rcases hitem with rfl | hitem
            · exact hkeysEqual.1.le
            · have hrightCons :
                  (key head :: (beforeRest ++ pivot :: suffix).map key).Pairwise
                    (· ≤ ·) := by
                simpa only [List.sortedLE_iff_pairwise, List.map_cons] using
                  hsortedRight
              rw [List.pairwise_cons] at hrightCons
              exact hkeysEqual.1.le.trans
                (hrightCons.1 (key item)
                  (List.mem_map.mpr ⟨item, hitem, rfl⟩))
      have hbeforeKeys : ∀ item, item ∈ before →
          key item = key pivot := by
        intro item hitem
        apply le_antisymm
        · exact hsortedRightAppend.2.2 (key item)
            (List.mem_map.mpr ⟨item, hitem, rfl⟩) (key pivot) (by simp)
        · exact hlower item (by simp [hitem])
      have hwellRight :
          (before ++ pivot :: suffix).Forall
            RegionShapeSummary.WellFormed := by
        rw [List.forall_iff_forall_mem]
        intro summary hsummary
        exact List.forall_iff_forall_mem.mp
          (by rw [List.forall_cons]; exact hwellFormed) summary
          (hperm.mem_iff.mpr hsummary)
      rw [List.forall_append, List.forall_cons] at hwellRight
      have hbubble := slotSummaryStateFromWith_bubble pivot before suffix
        hwellRight.1 hwellFormed.1 (by
          intro item hitem
          have hpair := hties pivot (by simp) item
            (hperm.mem_iff.mpr (by simp [hitem]))
            (hbeforeKeys item hitem).symm
          rcases hpair with heq | hdisjoint
          · exact Or.inl heq.symm
          · exact Or.inr hdisjoint.symm)
        initial allocations hvalid hwellRight.2.2
      have htailPerm : rest.Perm (before ++ suffix) := by
        apply List.Perm.cons_inv
        exact hperm.trans (perm_bubble pivot before suffix)
      have htailSorted : ((before ++ suffix).map key).SortedLE := by
        rw [List.sortedLE_iff_pairwise, List.map_append,
          List.pairwise_append]
        exact ⟨hsortedRightAppend.1,
          (List.pairwise_cons.mp hsortedRightAppend.2.1).2, by
            intro leftKey hleftKey rightKey hrightKey
            exact hsortedRightAppend.2.2 leftKey hleftKey rightKey
              (by simp [hrightKey])⟩
      generalize hplaced : placeSummary pivot allocations = placed
      rcases placed with ⟨row, updated⟩
      have hupdatedValid : updated.Valid := by
        have hresult := placeSummary_valid pivot allocations hvalid
          hwellFormed.1
        rw [hplaced] at hresult
        exact hresult
      have hrest := inductionHypothesis htailPerm (by
          rw [List.sortedLE_iff_pairwise]
          exact hsortedLeftCons.2)
        htailSorted hwellFormed.2 (by
          intro first hfirst second hsecond hkey
          exact hties first (by simp [hfirst]) second (by simp [hsecond]) hkey)
        (max initial (row.getD 0 + pivot.rowCount)) updated hupdatedValid
      have hconsRest : SummaryStateEquivalent
          (slotSummaryStateFromWith initial (pivot :: rest) allocations)
          (slotSummaryStateFromWith initial
            (pivot :: before ++ suffix) allocations) := by
        simpa only [List.cons_append, slotSummaryStateFromWith, hplaced]
          using hrest
      exact hconsRest.trans hbubble.symm

/-- The common special case where tied summaries are definitionally the same or
column-disjoint. -/
theorem slotSummaryEndFromWith_eq_of_sorted_perm
    {K : Type} [LinearOrder K] (key : RegionShapeSummary → K)
    {left right : List RegionShapeSummary}
    (hperm : left.Perm right)
    (hsortedLeft : (left.map key).SortedLE)
    (hsortedRight : (right.map key).SortedLE)
    (hwellFormed : left.Forall RegionShapeSummary.WellFormed)
    (hties : ∀ first, first ∈ left → ∀ second, second ∈ left →
      key first = key second →
        first = second ∨ List.Disjoint first.columns second.columns)
    (initial : ℕ) (allocations : CircuitAllocations)
    (hvalid : allocations.Valid) (tail : List RegionShapeSummary)
    (hwellTail : tail.Forall RegionShapeSummary.WellFormed) :
    slotSummaryEndFromWith initial (left ++ tail) allocations =
      slotSummaryEndFromWith initial (right ++ tail) allocations := by
  exact slotSummaryEndFromWith_eq_of_sorted_perm_interchangeable key hperm
    hsortedLeft hsortedRight hwellFormed (by
      intro first hfirst second hsecond hkey
      rcases hties first hfirst second hsecond hkey with rfl | hdisjoint
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr hdisjoint)
    initial allocations hvalid tail hwellTail

/-- Two key-sorted streams with the same normalized physical shapes produce the
same V1 endpoint. The normalization equality may reorder equal-key shapes; the
usual tie-interchangeability condition makes that reordering harmless. -/
theorem slotSummaryEndFromWith_eq_of_normalized_perm
    {left right : List RegionShapeSummary}
    (hnormalized :
      (left.map RegionShapeSummary.normalized).Perm
        (right.map RegionShapeSummary.normalized))
    (hsortedLeft :
      (left.map (fun summary => (summary.key : OrderDual ℕ))).SortedLE)
    (hsortedRight :
      (right.map (fun summary => (summary.key : OrderDual ℕ))).SortedLE)
    (hwellFormed : right.Forall RegionShapeSummary.WellFormed)
    (hties : ∀ first, first ∈ right → ∀ second, second ∈ right →
      first.key = second.key →
        first.PlacementEquivalent second ∨
          List.Disjoint first.columns second.columns)
    (initial : ℕ) (allocations : CircuitAllocations)
    (hvalid : allocations.Valid) (tail : List RegionShapeSummary)
    (hwellTail : tail.Forall RegionShapeSummary.WellFormed) :
    slotSummaryEndFromWith initial (left ++ tail) allocations =
      slotSummaryEndFromWith initial (right ++ tail) allocations := by
  obtain ⟨aligned, haligned, hequivalent⟩ :=
    exists_perm_forall₂_of_map_perm RegionShapeSummary.normalized hnormalized
  have hplacement :
      List.Forall₂ RegionShapeSummary.PlacementEquivalent left aligned :=
    hequivalent.imp fun _ _ hnormalizedEq =>
      RegionShapeSummary.placementEquivalent_iff_normalized_eq.mpr
        hnormalizedEq
  have hleftAligned :
      slotSummaryEndFromWith initial (left ++ tail) allocations =
        slotSummaryEndFromWith initial (aligned ++ tail) allocations := by
    have htailPlacement :
        List.Forall₂ RegionShapeSummary.PlacementEquivalent tail tail := by
      rw [List.forall₂_same]
      intro summary _
      exact ⟨rfl, rfl⟩
    rw [← slotSummaryStateFromWith_fst,
      ← slotSummaryStateFromWith_fst]
    exact congrArg Prod.fst
      (slotSummaryStateFromWith_eq_of_forall₂_placementEquivalent
        (List.rel_append hplacement htailPlacement) initial allocations)
  have hkeys :
      left.map (fun summary => (summary.key : OrderDual ℕ)) =
        aligned.map (fun summary => (summary.key : OrderDual ℕ)) := by
    rw [← List.forall₂_eq_eq_eq]
    simpa only [List.forall₂_map_left_iff,
      List.forall₂_map_right_iff] using hplacement.imp (fun first second h =>
        congrArg (fun summary => (summary.key : OrderDual ℕ))
          (RegionShapeSummary.placementEquivalent_iff_normalized_eq.mp h) |>
            (RegionShapeSummary.normalized_key_eq first ▸
              RegionShapeSummary.normalized_key_eq second ▸ ·))
  have hsortedAligned :
      (aligned.map (fun summary => (summary.key : OrderDual ℕ))).SortedLE := by
    rw [← hkeys]
    exact hsortedLeft
  have hrightAligned :=
    slotSummaryEndFromWith_eq_of_sorted_perm_interchangeable
      (key := fun summary : RegionShapeSummary =>
        (show OrderDual ℕ from summary.key)) haligned.symm hsortedRight
      hsortedAligned hwellFormed (by
        intro first hfirst second hsecond hkey
        exact hties first hfirst second hsecond
          (show first.key = second.key from hkey))
      initial allocations hvalid tail hwellTail
  exact hleftAligned.trans hrightAligned.symm

/-- Complete-state form of normalized sorted-permutation equivalence. -/
theorem slotSummaryStateFromWith_eq_of_normalized_perm
    {left right : List RegionShapeSummary}
    (hnormalized :
      (left.map RegionShapeSummary.normalized).Perm
        (right.map RegionShapeSummary.normalized))
    (hsortedLeft :
      (left.map (fun summary => (summary.key : OrderDual ℕ))).SortedLE)
    (hsortedRight :
      (right.map (fun summary => (summary.key : OrderDual ℕ))).SortedLE)
    (hwellFormed : right.Forall RegionShapeSummary.WellFormed)
    (hties : ∀ first, first ∈ right → ∀ second, second ∈ right →
      first.key = second.key →
        first.PlacementEquivalent second ∨
          List.Disjoint first.columns second.columns)
    (initial : ℕ) (allocations : CircuitAllocations)
    (hvalid : allocations.Valid) :
    SummaryStateEquivalent
      (slotSummaryStateFromWith initial left allocations)
      (slotSummaryStateFromWith initial right allocations) := by
  obtain ⟨aligned, haligned, hequivalent⟩ :=
    exists_perm_forall₂_of_map_perm RegionShapeSummary.normalized hnormalized
  have hplacement :
      List.Forall₂ RegionShapeSummary.PlacementEquivalent left aligned :=
    hequivalent.imp fun _ _ hnormalizedEq =>
      RegionShapeSummary.placementEquivalent_iff_normalized_eq.mpr
        hnormalizedEq
  have hleftAligned :
      slotSummaryStateFromWith initial left allocations =
        slotSummaryStateFromWith initial aligned allocations :=
    slotSummaryStateFromWith_eq_of_forall₂_placementEquivalent
      hplacement initial allocations
  have hkeys :
      left.map (fun summary => (summary.key : OrderDual ℕ)) =
        aligned.map (fun summary => (summary.key : OrderDual ℕ)) := by
    rw [← List.forall₂_eq_eq_eq]
    simpa only [List.forall₂_map_left_iff,
      List.forall₂_map_right_iff] using hplacement.imp (fun first second h =>
        congrArg (fun summary => (summary.key : OrderDual ℕ))
          (RegionShapeSummary.placementEquivalent_iff_normalized_eq.mp h) |>
            (RegionShapeSummary.normalized_key_eq first ▸
              RegionShapeSummary.normalized_key_eq second ▸ ·))
  have hsortedAligned :
      (aligned.map (fun summary => (summary.key : OrderDual ℕ))).SortedLE := by
    rw [← hkeys]
    exact hsortedLeft
  have hrightAligned :=
    slotSummaryStateFromWith_eq_of_sorted_perm_interchangeable
      (key := fun summary : RegionShapeSummary =>
        (show OrderDual ℕ from summary.key)) haligned.symm hsortedRight
      hsortedAligned hwellFormed (by
        intro first hfirst second hsecond hkey
        exact hties first hfirst second hsecond
          (show first.key = second.key from hkey))
      initial allocations hvalid
  have hleftEquivalent : SummaryStateEquivalent
      (slotSummaryStateFromWith initial left allocations)
      (slotSummaryStateFromWith initial aligned allocations) := by
    rw [hleftAligned]
    exact SummaryStateEquivalent.refl _
  exact hleftEquivalent.trans hrightAligned.symm

/-- Forgetting shape indices changes no slotted endpoint, for any pair sequence. -/
theorem slottedEndFrom_forgetIndices_eq
    (shapes : List RegionShape) (pairs : List (ℕ × ℕ)) :
    slottedEndFrom shapes pairs =
      slottedSummaryEndFrom (shapes.map RegionShape.toSummary)
        (pairs.map (·.2)) := by
  unfold slottedEndFrom placedShapes slottedSummaryEndFrom
  apply congrArg (List.foldl max 0)
  induction shapes generalizing pairs with
  | nil => rfl
  | cons shape rest inductionHypothesis =>
      cases pairs with
      | nil => rfl
      | cons pair pairs =>
          simp only [List.map_cons, List.zip_cons_cons,
            RegionShape.toSummary]
          rw [inductionHypothesis]

/-- The exact endpoint of slotting can be computed entirely in the reduced,
index-free summary language. -/
theorem slottedEndFrom_eq_slottedSummaryEndFrom
    (shapes : List RegionShape) (allocations : CircuitAllocations) :
    slottedEndFrom shapes (slotInFrom shapes allocations).1 =
      slottedSummaryEndFrom (shapes.map RegionShape.toSummary)
        (slotShapeSummariesFrom
          (shapes.map RegionShape.toSummary) allocations).1 := by
  rw [slottedEndFrom_forgetIndices_eq]
  have hslot := slotInFrom_forgetIndices shapes allocations
  have hstarts :
      (slotInFrom shapes allocations).1.map (·.2) =
        (slotShapeSummariesFrom
          (shapes.map RegionShape.toSummary) allocations).1 := by
    simpa using congrArg Prod.fst hslot
  rw [hstarts]

/-- Indexing a summary sequence changes no slotted endpoint, for any returned
pair sequence. -/
theorem slottedEndFrom_indexRegionSummaries_eq
    (initial : ℕ) (summaries : List RegionShapeSummary)
    (pairs : List (ℕ × ℕ)) :
    slottedEndFrom (indexRegionSummaries initial summaries) pairs =
      slottedSummaryEndFrom summaries (pairs.map (·.2)) := by
  unfold slottedEndFrom placedShapes slottedSummaryEndFrom
  apply congrArg (List.foldl max 0)
  induction summaries generalizing initial pairs with
  | nil => rfl
  | cons summary rest inductionHypothesis =>
      cases pairs with
      | nil => rfl
      | cons pair pairs =>
          simp only [indexRegionSummaries, List.map_cons,
            List.zip_cons_cons, measureRegionSummary]
          rw [inductionHypothesis]

/-- Region indices are irrelevant to the endpoint of an actual slotted summary
sequence. -/
theorem slottedEndFrom_indexRegionSummaries
    (initial : ℕ) (summaries : List RegionShapeSummary)
    (allocations : CircuitAllocations) :
    slottedEndFrom (indexRegionSummaries initial summaries)
        (slotInFrom (indexRegionSummaries initial summaries) allocations).1 =
      slottedSummaryEndFrom summaries
        (slotShapeSummariesFrom summaries allocations).1 := by
  rw [slottedEndFrom_indexRegionSummaries_eq]
  have hslot := slotInFrom_indexRegionSummaries
    initial summaries allocations
  have hstarts :
      (slotInFrom (indexRegionSummaries initial summaries) allocations).1.map
          (·.2) =
        (slotShapeSummariesFrom summaries allocations).1 := by
    simpa using congrArg Prod.fst hslot
  rw [hstarts]

private theorem placedShapeEnds_eq
    (allPairs : List (ℕ × ℕ)) (shapes : List RegionShape)
    (starts : List ℕ)
    (hindices : allPairs.map (·.1) = shapes.map RegionShape.index)
    (hstarts : ∀ pair ∈ allPairs,
      starts.getD pair.1 0 = pair.2) :
    (placedShapes shapes allPairs).map (fun placed =>
      placed.2 + placed.1.rowCount) =
      shapes.map (fun shape =>
        starts.getD shape.index 0 + shape.rowCount) := by
  induction shapes generalizing allPairs with
  | nil => rfl
  | cons shape rest inductionHypothesis =>
      cases allPairs with
      | nil => simp at hindices
      | cons pair pairs =>
          simp only [List.map_cons, List.cons.injEq] at hindices
          simp only [placedShapes, List.map_cons, List.zip_cons_cons]
          rw [← hstarts pair (by simp), hindices.1]
          congr 1
          exact inductionHypothesis
            pairs hindices.2
            (by
              intro candidate hcandidate
              exact hstarts candidate (by simp [hcandidate]))

/-- `placementEndFrom` can be evaluated directly in the planner's slotting order.
The final index-restoration sort is irrelevant to the endpoint. -/
theorem placementEndFrom_planCandidate_eq_slottedEndFrom
    (shapes : List RegionShape)
    (hindices : shapes.map RegionShape.index = List.range shapes.length) :
    placementEndFrom shapes (planCandidate shapes).1 =
      let sortedDesc :=
        (Pdqsort.quicksort shapes.toArray
          (fun left right => left.key < right.key)).reverse.toList
      slottedEndFrom sortedDesc (slotIn sortedDesc).1 := by
  let sortedDesc :=
    (Pdqsort.quicksort shapes.toArray
      (fun left right => left.key < right.key)).reverse.toList
  let pairs := (slotIn sortedDesc).1
  let starts := (sortPairsByIndex pairs).map (·.2)
  have hsorted : sortedDesc.Perm shapes := by
    have hquick := Pdqsort.quicksort_perm shapes.toArray
      (fun left right => left.key < right.key)
    exact (by
      simpa [sortedDesc] using
        (List.reverse_perm
          (Pdqsort.quicksort shapes.toArray
            (fun left right => left.key < right.key)).toList).trans hquick)
  have hpairsIndices : pairs.map (·.1) =
      sortedDesc.map RegionShape.index := by
    exact slotIn_indices sortedDesc
  have hpairsRange : (pairs.map (·.1)).Perm
      (List.range shapes.length) := by
    rw [hpairsIndices]
    simpa only [hindices] using hsorted.map RegionShape.index
  have hsortedIndices :
      (sortPairsByIndex pairs).map (·.1) =
        List.range shapes.length :=
    sortPairsByIndex_fst_eq_range pairs shapes.length hpairsRange
  have hstarts : ∀ pair ∈ pairs,
      starts.getD pair.1 0 = pair.2 := by
    intro pair hpair
    exact starts_getD_of_pair_mem pairs shapes.length
      hsortedIndices hpair
  have hends := placedShapeEnds_eq
    pairs sortedDesc starts hpairsIndices hstarts
  have hpermEnds := hsorted.map (fun shape =>
    starts.getD shape.index 0 + shape.rowCount)
  change
    (shapes.map (fun shape =>
      starts.getD shape.index 0 + shape.rowCount)).foldl max 0 = _
  rw [← hpermEnds.foldl_eq 0, ← hends]
  rfl

theorem shape_end_le_placementEndFrom_of_mem
    (shapes : List RegionShape) (regionStarts : List ℕ)
    (shape : RegionShape) (hshape : shape ∈ shapes) :
    regionStarts.getD shape.index 0 + shape.rowCount ≤
      placementEndFrom shapes regionStarts := by
  exact value_le_foldl_max_of_mem
    (shapes.map fun current =>
      regionStarts.getD current.index 0 + current.rowCount)
    id 0
    (regionStarts.getD shape.index 0 + shape.rowCount)
    (List.mem_map.mpr ⟨shape, hshape, rfl⟩)

/-- Rows occupied in one column, as a finite set of placed half-open intervals. -/
def occupiedRowsIn (shapes : List RegionShape) (regionStarts : List ℕ)
    (column : RegionColumn) : Finset ℕ :=
  shapes.foldr (fun shape occupied =>
    if column ∈ shape.columns then
      Finset.Ico (regionStarts.getD shape.index 0)
          (regionStarts.getD shape.index 0 + shape.rowCount) ∪ occupied
    else occupied) ∅

theorem occupiedRowsIn_nil
    (regionStarts : List ℕ) (column : RegionColumn) :
    occupiedRowsIn [] regionStarts column = ∅ := rfl

theorem occupiedRowsIn_cons
    (shape : RegionShape) (rest : List RegionShape)
    (regionStarts : List ℕ) (column : RegionColumn) :
    occupiedRowsIn (shape :: rest) regionStarts column =
      if column ∈ shape.columns then
        Finset.Ico (regionStarts.getD shape.index 0)
            (regionStarts.getD shape.index 0 + shape.rowCount) ∪
          occupiedRowsIn rest regionStarts column
      else occupiedRowsIn rest regionStarts column := rfl

theorem mem_occupiedRowsIn_iff
    (shapes : List RegionShape) (regionStarts : List ℕ)
    (column : RegionColumn) (row : ℕ) :
    row ∈ occupiedRowsIn shapes regionStarts column ↔
      ∃ shape ∈ shapes,
        column ∈ shape.columns ∧
          regionStarts.getD shape.index 0 ≤ row ∧
          row < regionStarts.getD shape.index 0 + shape.rowCount := by
  induction shapes with
  | nil => simp [occupiedRowsIn_nil]
  | cons shape rest inductionHypothesis =>
      by_cases hcolumn : column ∈ shape.columns
      · simp only [occupiedRowsIn_cons, hcolumn, ↓reduceIte,
          Finset.mem_union, Finset.mem_Ico, inductionHypothesis,
          List.mem_cons, exists_eq_or_imp, true_and]
      · simp only [occupiedRowsIn_cons, hcolumn, ↓reduceIte,
          inductionHypothesis, List.mem_cons, exists_eq_or_imp,
          false_and, false_or]

theorem occupiedRowsIn_card_le_columnOccupiedLength
    (shapes : List RegionShape) (regionStarts : List ℕ)
    (column : RegionColumn) :
    (occupiedRowsIn shapes regionStarts column).card ≤
      columnOccupiedLength shapes column := by
  induction shapes with
  | nil => simp [occupiedRowsIn, columnOccupiedLength]
  | cons shape rest inductionHypothesis =>
      by_cases hcolumn : column ∈ shape.columns
      · simp only [occupiedRowsIn_cons, hcolumn, ↓reduceIte,
          columnOccupiedLength_cons]
        apply (Finset.card_union_le _ _).trans
        have hinterval :
            (Finset.Ico (regionStarts.getD shape.index 0)
              (regionStarts.getD shape.index 0 + shape.rowCount)).card =
              shape.rowCount := by
          rw [Nat.card_Ico]
          omega
        exact Nat.add_le_add (Nat.le_of_eq hinterval) (by
          exact inductionHypothesis)
      · simpa only [occupiedRowsIn_cons, hcolumn, ↓reduceIte,
          columnOccupiedLength_cons, zero_add] using
          inductionHypothesis

theorem occupiedRowsIn_card_eq_columnOccupiedLength
    (shapes : List RegionShape) (regionStarts : List ℕ)
    (column : RegionColumn)
    (hindices : (shapes.map (·.index)).Nodup)
    (hdisjoint : SharedColumnIntervalsDisjoint shapes regionStarts) :
    (occupiedRowsIn shapes regionStarts column).card =
      columnOccupiedLength shapes column := by
  induction shapes with
  | nil => simp only [occupiedRowsIn_nil, Finset.card_empty,
      columnOccupiedLength_nil]
  | cons shape rest inductionHypothesis =>
      rw [List.map_cons, List.nodup_cons] at hindices
      have hrestDisjoint : SharedColumnIntervalsDisjoint rest regionStarts := by
        intro left right hleft hright hne currentColumn
          hleftColumn hrightColumn
        exact hdisjoint (by simp [hleft]) (by simp [hright]) hne
          hleftColumn hrightColumn
      have hrestCard := inductionHypothesis hindices.2 hrestDisjoint
      by_cases hcolumn : column ∈ shape.columns
      · have hintervals : Disjoint
            (Finset.Ico (regionStarts.getD shape.index 0)
              (regionStarts.getD shape.index 0 + shape.rowCount))
            (occupiedRowsIn rest regionStarts column) := by
          rw [Finset.disjoint_left]
          intro row hshapeRow hrestRow
          rw [Finset.mem_Ico] at hshapeRow
          obtain ⟨other, hother, hotherColumn, hotherRow⟩ :=
            (mem_occupiedRowsIn_iff rest regionStarts column row).mp hrestRow
          have hindex : shape.index ≠ other.index := by
            intro hequal
            apply hindices.1
            exact List.mem_map.mpr ⟨other, hother, hequal.symm⟩
          have hplaced := hdisjoint (by simp) (by simp [hother]) hindex
            hcolumn hotherColumn
          unfold RowIntervalsDisjoint at hplaced
          omega
        simp only [occupiedRowsIn_cons, hcolumn, ↓reduceIte,
          columnOccupiedLength_cons]
        rw [Finset.card_union_of_disjoint hintervals, Nat.card_Ico,
          hrestCard]
        omega
      · simpa only [occupiedRowsIn_cons, hcolumn, ↓reduceIte,
          columnOccupiedLength_cons, zero_add] using hrestCard

theorem columnOccupiedLength_le_placementEndFrom
    (shapes : List RegionShape) (regionStarts : List ℕ)
    (column : RegionColumn)
    (hindices : (shapes.map (·.index)).Nodup)
    (hdisjoint : SharedColumnIntervalsDisjoint shapes regionStarts) :
    columnOccupiedLength shapes column ≤
      placementEndFrom shapes regionStarts := by
  rw [← occupiedRowsIn_card_eq_columnOccupiedLength
    shapes regionStarts column hindices hdisjoint]
  have hsubset : occupiedRowsIn shapes regionStarts column ⊆
      Finset.range (placementEndFrom shapes regionStarts) := by
    intro row hrow
    rw [Finset.mem_range]
    obtain ⟨shape, hshape, hcolumn, hbounds⟩ :=
      (mem_occupiedRowsIn_iff shapes regionStarts column row).mp hrow
    exact hbounds.2.trans_le
      (shape_end_le_placementEndFrom_of_mem
        shapes regionStarts shape hshape)
  simpa using Finset.card_le_card hsubset

/-- One past the last row occupied by any placed region.  This is Halo 2 V1's
`first_unassigned_row`, stated directly from the final placement rather than through
the planner's internal per-column allocation map. -/
def placementEnd (ops : Operations F) : ℕ :=
  placementEndFrom (measureRegions ops) (starts ops)

/-- Every synthesized selector activation lies below V1's placed-region endpoint. -/
theorem activation_row_lt_placementEnd
    (operations : Operations F) {selector row : ℕ}
    (hactivation : (selector, row) ∈
      activations (starts operations) (indexedRegions operations 0).1) :
    row < placementEnd operations := by
  rw [activations, List.mem_flatMap] at hactivation
  obtain ⟨⟨index, body⟩, hregion, hbody⟩ := hactivation
  rw [List.mem_flatMap] at hbody
  obtain ⟨operation, hoperation, hmapped⟩ := hbody
  have hshape : measureRegion index body ∈ measureRegions operations :=
    List.mem_map.mpr ⟨(index, body), hregion, rfl⟩
  have hend := shape_end_le_placementEndFrom_of_mem
    (measureRegions operations) (starts operations)
    (measureRegion index body) hshape
  cases operation with
  | enableGate gate localRow =>
      simp only [List.mem_singleton] at hmapped
      injection hmapped with _ hrow
      subst row
      have hlocal : localRow < (measureRegion index body).rowCount := by
        have hbound := regionOperationRowExtent_le_synthesisSummary_of_mem
          body (.enableGate gate localRow) hoperation
        simpa only [measureRegion_rowCount,
          regionOperationRowExtent] using hbound
      unfold placementEnd
      simp only [measureRegion] at hend hlocal
      omega
  | enableLookup argument enabled localRow =>
      rw [List.mem_map] at hmapped
      obtain ⟨sourceSelector, _, hequal⟩ := hmapped
      injection hequal with _ hrow
      subst row
      have hlocal := row_lt_measureRegion_of_enableLookup_mem
        index body argument enabled localRow hoperation
      unfold placementEnd
      simp only [measureRegion] at hend hlocal
      omega
  | assignAdvice | assignFixed | constrainEqual | constrainConstant |
      constrainInstance =>
      simp at hmapped

/-- The exact indexed region order consumed by V1 after its legacy pdqsort. -/
def sortedRegionOrder (ops : Operations F) : List RegionShape :=
  let shapes := measureRegions ops
  (Pdqsort.quicksort shapes.toArray
    (fun left right => left.key < right.key)).reverse.toList

/-- Original region indices in V1's consensus sort order. -/
def sortedRegionIndices (ops : Operations F) : List Nat :=
  (sortedRegionOrder ops).map RegionShape.index

/-- The exact index-free summary order consumed by V1 after its legacy pdqsort. -/
def sortedSummaryOrder (ops : Operations F) : List RegionShapeSummary :=
  (sortedRegionOrder ops).map RegionShape.toSummary

/-- The consensus-sorted summaries are determined by their original region
indices and the reduced synthesis summary. -/
theorem sortedSummaryOrder_eq_map_getD (ops : Operations F) :
    sortedSummaryOrder ops =
      (sortedRegionIndices ops).map fun index =>
        (synthesisSummary ops).regionShapes.getD index
          { columns := [], rowCount := 0 } := by
  let shapes := measureRegions ops
  let sorted := (Pdqsort.quicksort shapes.toArray
    (fun left right => left.key < right.key)).reverse.toList
  have hperm : sorted.Perm shapes := by
    have hquick := Pdqsort.quicksort_perm shapes.toArray
      (fun left right => left.key < right.key)
    simpa only [sorted, shapes, Array.toList_reverse] using
      (List.reverse_perm _).trans hquick
  have hlength : shapes.length = ops.regionCount := by
    have h := congrArg List.length (measureRegions_indices_eq_range ops)
    simpa only [shapes, List.length_map, List.length_range] using h
  have hindices : shapes.map RegionShape.index =
      List.range shapes.length := by
    simpa only [shapes, hlength] using measureRegions_indices_eq_range ops
  have hsummaries : shapes.map RegionShape.toSummary =
      (synthesisSummary ops).regionShapes := by
    simp only [shapes, measureRegions_eq_synthesisSummary_regionShapes,
      indexRegionSummaries_toSummary]
  unfold sortedSummaryOrder sortedRegionOrder sortedRegionIndices
  change sorted.map RegionShape.toSummary = _
  rw [List.map_map]
  apply List.map_congr_left
  intro shape hshape
  simp only [Function.comp_apply]
  have hmember : shape ∈ shapes := hperm.mem_iff.mp hshape
  have hget := getD_eq_of_mem_of_map_eq_range RegionShape.index shapes
    { index := 0, columns := [], rowCount := 0 } shape hindices hmember
  rw [← hsummaries]
  calc
    shape.toSummary =
        (shapes.getD shape.index
          { index := 0, columns := [], rowCount := 0 }).toSummary :=
      congrArg RegionShape.toSummary hget.symm
    _ = (shapes.map RegionShape.toSummary).getD shape.index
        { columns := [], rowCount := 0 } := by
      exact (List.getD_map shapes
        { index := 0, columns := [], rowCount := 0 }
        RegionShape.toSummary).symm

theorem sortedSummaryOrder_perm_synthesisSummary (ops : Operations F) :
    (sortedSummaryOrder ops).Perm
      (synthesisSummary ops).regionShapes := by
  let shapes := measureRegions ops
  let sorted :=
    (Pdqsort.quicksort shapes.toArray
      (fun left right => left.key < right.key)).toList
  have hquick : sorted.Perm shapes := by
    exact Pdqsort.quicksort_perm shapes.toArray
      (fun left right => left.key < right.key)
  have hsorted : sorted.reverse.Perm shapes :=
    (List.reverse_perm sorted).trans hquick
  have hsummaries := hsorted.map RegionShape.toSummary
  have hforget :
      (measureRegions ops).map RegionShape.toSummary =
        (synthesisSummary ops).regionShapes := by
    rw [measureRegions_eq_synthesisSummary_regionShapes,
      indexRegionSummaries_toSummary]
  rw [← hforget]
  simpa only [sortedSummaryOrder, sortedRegionOrder, shapes, sorted,
    Array.toList_reverse] using hsummaries

/-- Erasing selector columns preserves every start chosen in consensus sort
order when each selector is anchored by a physical column. -/
theorem sortedRegionStarts_eq_slotShapeSummariesFrom_withoutSelectors
    (ops : Operations F) (anchor : Nat → RegionColumn)
    (hanchors : SelectorAnchoredBy
      (synthesisSummary ops).regionShapes anchor) :
    let shapes := measureRegions ops
    let sorted := (Pdqsort.quicksort shapes.toArray
      (fun left right => left.key < right.key)).reverse.toList
    (slotIn sorted).1.map (·.2) =
      (slotShapeSummariesFrom
        ((sortedSummaryOrder ops).map
          RegionShapeSummary.withoutSelectors) ∅).1 := by
  let shapes := measureRegions ops
  let sorted := (Pdqsort.quicksort shapes.toArray
    (fun left right => left.key < right.key)).reverse.toList
  have hperm : (sorted.map RegionShape.toSummary).Perm
      (synthesisSummary ops).regionShapes := by
    simpa only [sorted, shapes, sortedSummaryOrder, sortedRegionOrder] using
      sortedSummaryOrder_perm_synthesisSummary ops
  have hwellFormed : (sorted.map RegionShape.toSummary).Forall
      RegionShapeSummary.WellFormed := by
    rw [List.forall_iff_forall_mem]
    intro summary hsummary
    exact List.forall_iff_forall_mem.mp
      (synthesisSummary_regionShapes_wellFormed ops) summary
      (hperm.mem_iff.mp hsummary)
  have hsortedAnchors : SelectorAnchoredBy
      (sorted.map RegionShape.toSummary) anchor := by
    rw [SelectorAnchoredBy, List.forall_iff_forall_mem]
    intro summary hsummary
    exact List.forall_iff_forall_mem.mp hanchors summary
      (hperm.mem_iff.mp hsummary)
  have hforget := congrArg Prod.fst
    (slotInFrom_forgetIndices sorted (∅ : CircuitAllocations))
  have hphysical := slotShapeSummariesFrom_eq_withoutSelectors
    (sorted.map RegionShape.toSummary)
    (∅ : CircuitAllocations) (∅ : CircuitAllocations)
    hwellFormed CircuitAllocations.Valid.empty
    CircuitAllocations.Valid.empty
    (CircuitAllocations.PhysicalEquivalent.refl ∅)
    (SelectorAllocationsDominatedBy.empty anchor)
    hsortedAnchors
  exact hforget.trans hphysical.1

/-- V1's placement endpoint is exactly the result of running the reduced summary
planner in its consensus sort order. -/
theorem placementEnd_eq_slotSummaryEndFrom (ops : Operations F) :
    placementEnd ops =
      slotSummaryEndFrom (sortedSummaryOrder ops) ∅ := by
  unfold placementEnd starts
  rw [planOperations_eq]
  have hindices := measureRegions_indices_eq_range ops
  have hlength : (measureRegions ops).length = ops.regionCount := by
    have := congrArg List.length hindices
    simpa using this
  rw [← hlength] at hindices
  rw [placementEndFrom_planCandidate_eq_slottedEndFrom
    (measureRegions ops) hindices]
  let sortedDesc :=
    (Pdqsort.quicksort (measureRegions ops).toArray
      (fun left right => left.key < right.key)).reverse.toList
  have hsummary := slottedEndFrom_eq_slottedSummaryEndFrom
    sortedDesc (∅ : CircuitAllocations)
  simpa only [sortedSummaryOrder, sortedRegionOrder, sortedDesc, slotIn,
    slotSummaryEndFrom, slotSummaryEndFromWith] using hsummary

/-- When virtual selectors are anchored by physical columns, the exact V1
endpoint can be computed after erasing selectors from the consensus-sorted
summary stream. -/
theorem placementEnd_eq_slotSummaryEndFrom_withoutSelectors
    (ops : Operations F) (anchor : ℕ → RegionColumn)
    (hanchors : SelectorAnchoredBy
      (synthesisSummary ops).regionShapes anchor) :
    placementEnd ops =
      slotSummaryEndFrom
        ((sortedSummaryOrder ops).map
          RegionShapeSummary.withoutSelectors) ∅ := by
  let sorted := sortedSummaryOrder ops
  have hperm := sortedSummaryOrder_perm_synthesisSummary ops
  have hsourceWellFormed := synthesisSummary_regionShapes_wellFormed ops
  have hsortedWellFormed :
      sorted.Forall RegionShapeSummary.WellFormed := by
    rw [List.forall_iff_forall_mem]
    intro summary hsummary
    exact List.forall_iff_forall_mem.mp hsourceWellFormed summary
      (hperm.mem_iff.mp hsummary)
  have hsortedAnchors : SelectorAnchoredBy sorted anchor := by
    rw [SelectorAnchoredBy, List.forall_iff_forall_mem]
    intro summary hsummary
    exact List.forall_iff_forall_mem.mp hanchors summary
      (hperm.mem_iff.mp hsummary)
  rw [placementEnd_eq_slotSummaryEndFrom]
  have herasure := slotSummaryEndFrom_eq_withoutSelectors sorted ∅ ∅
    hsortedWellFormed CircuitAllocations.Valid.empty
    CircuitAllocations.Valid.empty
    (CircuitAllocations.PhysicalEquivalent.refl ∅)
    (SelectorAllocationsDominatedBy.empty anchor) hsortedAnchors
  simpa only [sorted, slotSummaryEndFrom, slotSummaryEndFromWith]
    using herasure

end V1
end Halo2.FloorPlanner
