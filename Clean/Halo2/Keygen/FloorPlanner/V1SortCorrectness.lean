import Clean.Halo2.Keygen.FloorPlanner.V1Correctness

namespace Halo2.FloorPlanner.Pdqsort

/-- Stable canonical ordering of index-free V1 region summaries. -/
def stableRegionSort (summaries : List RegionShapeSummary) :
    List RegionShapeSummary :=
  summaries.mergeSort fun left right => left.key ≤ right.key

/-- Legacy pdqsort and the stable canonical region sort have the same exact V1
endpoint whenever tied summaries are placement-equivalent or column-disjoint. -/
theorem V1.slotSummaryEndFromWith_quicksort_eq_stableRegionSort_interchangeable
    (summaries : List RegionShapeSummary)
    (hwellFormed : summaries.Forall RegionShapeSummary.WellFormed)
    (hties : ∀ first, first ∈ summaries →
      ∀ second, second ∈ summaries →
      first.key = second.key →
        first.PlacementEquivalent second ∨
          List.Disjoint first.columns second.columns)
    (initial : ℕ) (allocations : CircuitAllocations)
    (hvalid : allocations.Valid) (tail : List RegionShapeSummary)
    (hwellTail : tail.Forall RegionShapeSummary.WellFormed) :
    let actual :=
      (quicksort summaries.toArray
        (lessBy RegionShapeSummary.key)).reverse.toList
    let canonical := (stableRegionSort summaries).reverse
    V1.slotSummaryEndFromWith initial (actual ++ tail) allocations =
      V1.slotSummaryEndFromWith initial (canonical ++ tail) allocations := by
  let actualAscending :=
    (quicksort summaries.toArray (lessBy RegionShapeSummary.key)).toList
  let canonicalAscending := stableRegionSort summaries
  have hactualPerm : actualAscending.Perm summaries := by
    exact quicksort_perm summaries.toArray
      (lessBy RegionShapeSummary.key)
  have hcanonicalPerm : canonicalAscending.Perm summaries := by
    exact List.mergeSort_perm summaries
      (fun left right => left.key ≤ right.key)
  have hcanonicalKeys :
      canonicalAscending.map RegionShapeSummary.key =
        (summaries.map RegionShapeSummary.key).mergeSort (· ≤ ·) := by
    apply List.map_mergeSort
    intro left hleft right hright
    rfl
  have hactualSorted :
      (actualAscending.reverse.map
        (fun summary => (summary.key : OrderDual ℕ))).SortedLE := by
    have hsorted := quicksort_sorted summaries.toArray
      RegionShapeSummary.key |>.reverse
    simpa only [List.map_reverse] using hsorted
  have hcanonicalSorted :
      (canonicalAscending.reverse.map
        (fun summary => (summary.key : OrderDual ℕ))).SortedLE := by
    have hsorted :
        (canonicalAscending.map RegionShapeSummary.key).SortedLE := by
      rw [hcanonicalKeys]
      exact List.sortedLE_mergeSort
    have hreverse := hsorted.reverse
    simpa only [List.map_reverse] using hreverse
  have hactualReversePerm :
      actualAscending.reverse.Perm summaries.reverse :=
    (List.reverse_perm actualAscending).trans
      (hactualPerm.trans (List.reverse_perm summaries).symm)
  have hcanonicalReversePerm :
      canonicalAscending.reverse.Perm summaries.reverse :=
    (List.reverse_perm canonicalAscending).trans
      (hcanonicalPerm.trans (List.reverse_perm summaries).symm)
  have hactualWellFormed :
      actualAscending.reverse.Forall RegionShapeSummary.WellFormed := by
    rw [List.forall_iff_forall_mem]
    intro summary hsummary
    exact List.forall_iff_forall_mem.mp hwellFormed summary
      (hactualPerm.mem_iff.mp (List.mem_reverse.mp hsummary))
  have hactualTies : ∀ first, first ∈ actualAscending.reverse →
      ∀ second, second ∈ actualAscending.reverse →
      first.key = second.key →
        first.PlacementEquivalent second ∨
          List.Disjoint first.columns second.columns := by
    intro first hfirst second hsecond hkey
    exact hties first
      (hactualPerm.mem_iff.mp (List.mem_reverse.mp hfirst)) second
      (hactualPerm.mem_iff.mp (List.mem_reverse.mp hsecond)) hkey
  have hresult :=
    V1.slotSummaryEndFromWith_eq_of_sorted_perm_interchangeable
    (key := fun summary : RegionShapeSummary =>
      (show OrderDual ℕ from summary.key))
    (hactualReversePerm.trans hcanonicalReversePerm.symm)
    hactualSorted hcanonicalSorted hactualWellFormed hactualTies
    initial allocations hvalid tail hwellTail
  simpa only [actualAscending, canonicalAscending, stableRegionSort,
    Array.toList_reverse] using hresult

/-- The common specialization where tied summaries are literally equal or
column-disjoint. -/
theorem V1.slotSummaryEndFromWith_quicksort_eq_stableRegionSort
    (summaries : List RegionShapeSummary)
    (hwellFormed : summaries.Forall RegionShapeSummary.WellFormed)
    (hties : ∀ first, first ∈ summaries →
      ∀ second, second ∈ summaries →
      first.key = second.key →
        first = second ∨ List.Disjoint first.columns second.columns)
    (initial : ℕ) (allocations : CircuitAllocations)
    (hvalid : allocations.Valid) (tail : List RegionShapeSummary)
    (hwellTail : tail.Forall RegionShapeSummary.WellFormed) :
    let actual :=
      (quicksort summaries.toArray
        (lessBy RegionShapeSummary.key)).reverse.toList
    let canonical := (stableRegionSort summaries).reverse
    V1.slotSummaryEndFromWith initial (actual ++ tail) allocations =
      V1.slotSummaryEndFromWith initial (canonical ++ tail) allocations := by
  exact
    V1.slotSummaryEndFromWith_quicksort_eq_stableRegionSort_interchangeable
      summaries hwellFormed (by
        intro first hfirst second hsecond hkey
        rcases hties first hfirst second hsecond hkey with rfl | hdisjoint
        · exact Or.inl ⟨rfl, rfl⟩
        · exact Or.inr hdisjoint)
      initial allocations hvalid tail hwellTail

end Halo2.FloorPlanner.Pdqsort

namespace Halo2.FloorPlanner.V1

/-- The reduced summary stream consumed by V1 is sorted by descending advice
area, independently of any concrete circuit. -/
theorem sortedSummaryOrder_key_sorted {F : Type} (ops : Operations F) :
    ((sortedSummaryOrder ops).map fun summary =>
      (summary.key : OrderDual ℕ)).SortedLE := by
  let shapes := measureRegions ops
  have hsorted :
      ((Pdqsort.quicksort shapes.toArray
        (Pdqsort.lessBy RegionShape.key)).toList.reverse.map fun shape =>
          (shape.key : OrderDual ℕ)).SortedLE := by
    have hascending :=
      Pdqsort.quicksort_sorted shapes.toArray RegionShape.key |>.reverse
    simpa only [List.map_reverse] using hascending
  simpa only [sortedSummaryOrder, sortedRegionOrder, shapes, List.map_map,
    Array.toList_reverse, RegionShape.toSummary_key, Pdqsort.lessBy] using hsorted

end Halo2.FloorPlanner.V1
