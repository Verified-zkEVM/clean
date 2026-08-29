import Clean.Ironwood.Action.PlannerSort.Certificate

namespace Zcash.Circuits.Action

open Halo2 FloorPlanner

set_option maxRecDepth 1000000 in
private theorem actionMeasuredRegionShapes_eq_sortInput :
    (measureRegions actionOperations).toArray =
      PlannerSort.sortNode22Input := by
  rw [measureRegions_eq_synthesisSummary_regionShapes,
    ← actionSynthesisSummary_eq_operations]
  unfold actionSynthesisSummary Circuit.mainPostSynthesisSummary
    Circuit.synthesizeBaseSynthesisSummary
    Circuit.synthWitnessSynthesisSummary Circuit.synthChecksSynthesisSummary
    Circuit.synthNotesSynthesisSummary
    Circuit.synthCrossAddressChecksSynthesisSummary
  decide +kernel

/-- The reduced synthesis summary computes the published consensus sort order. -/
theorem actionSortedRegionIndices_eq :
    V1.sortedRegionIndices actionOperations = actionSortedRegionIndices := by
  simp only [V1.sortedRegionIndices, V1.sortedRegionOrder]
  rw [actionMeasuredRegionShapes_eq_sortInput]
  rw [show (fun left right : RegionShape => decide (left.key < right.key)) =
      PlannerSort.less by rfl]
  rw [PlannerSort.sortNode22_quicksort]
  exact PlannerSort.sortNode22_indices

end Zcash.Circuits.Action
