import Clean.Ironwood.Action.SelectorPacking.Reduced

namespace Zcash.Circuits.Action

open Halo2 FloorPlanner

private theorem actionNonzeroSelectors_eq :
    (List.range 56).filter (fun selector =>
      actionSelectorDegrees[selector]! ≠ 0) =
      [0, 1, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17,
       18, 19, 20, 21, 22, 23, 24, 26, 27, 28, 30, 31, 32, 33, 34,
       35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49,
       50, 51, 52, 53, 54, 55] := by
  unfold actionSelectorDegrees
  decide

/-- Halo 2's greedy selector packing allocates exactly fifteen columns for Action. -/
theorem actionSelectorColumnCount_eq :
    selectorColumnCountWith (List.range 56) 9
      (fun selector => actionSelectorDegrees[selector]!)
      (selectorActivationsConflict actionReducedSelectorActivations) = 15 := by
  rw [selectorColumnCountWith_congr_on (degreeB := fun selector =>
    actionSelectorDegrees[selector]!)
    (conflictsB := actionReducedSelectorConflict)]
  · unfold selectorColumnCountWith actionReducedSelectorConflict
    rw [actionNonzeroSelectors_eq]
    decide +kernel
  · intro selector _
    rfl
  · intro left hleft right hright
    have hleftRange : left < 56 :=
      List.mem_range.mp (List.mem_of_mem_filter hleft)
    have hrightRange : right < 56 :=
      List.mem_range.mp (List.mem_of_mem_filter hright)
    have hleftDegree : actionSelectorDegrees[left]! ≠ 0 := by
      simpa only [decide_eq_true_eq] using (List.mem_filter.mp hleft).2
    have hrightDegree : actionSelectorDegrees[right]! ≠ 0 := by
      simpa only [decide_eq_true_eq] using (List.mem_filter.mp hright).2
    exact actionSelectorConflict_eq_of_nonzeroDegrees left right
      hleftRange hrightRange hleftDegree hrightDegree

end Zcash.Circuits.Action
