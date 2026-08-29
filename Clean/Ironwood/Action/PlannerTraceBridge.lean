import Clean.Ironwood.Action.PlannerSortBridge
import Clean.Ironwood.Action.PlannerTraceCertificate

namespace Zcash.Circuits.Action

open Halo2 FloorPlanner

/-- The exact consensus-order physical summary stream, retaining maximal runs. -/
def actionExactSortedPlannerSummaries : List RegionShapeSummary :=
  V1.PlannedSummaryBlock.summaries actionExactPlannerTrace ++
  List.replicate 2 { columns := [], rowCount := 0 }

/-- Exact Action start rows in consensus sort order. -/
def actionExactSortedStarts : List Nat :=
  V1.PlannedSummaryBlock.starts actionExactPlannerTrace ++ [0, 0]

set_option maxRecDepth 1000000 in
/-- Each reduced summary in consensus order has the exact physical footprint
recorded by the compact trace. -/
theorem actionSortedPlannerSummaries_equivalent_exact :
    List.Forall₂ RegionShapeSummary.PlacementEquivalent
      actionSortedPlannerSummaries actionExactSortedPlannerSummaries := by
  apply RegionShapeSummary.forall₂_placementEquivalent_of_map_normalized_eq
  unfold actionSortedPlannerSummaries
  rw [V1.sortedSummaryOrder_eq_map_getD]
  rw [actionSortedRegionIndices_eq]
  rw [show synthesisSummary actionOperations =
      actionSynthesisSummary by
    exact actionSynthesisSummary_eq_operations.symm]
  unfold actionExactSortedPlannerSummaries actionExactPlannerTrace
    actionExactPlannerRuns
    actionPlannerBlocks actionSortedRegionIndices actionSynthesisSummary
    Circuit.mainPostSynthesisSummary Circuit.synthesizeBaseSynthesisSummary
    Circuit.synthWitnessSynthesisSummary Circuit.synthChecksSynthesisSummary
    Circuit.synthNotesSynthesisSummary
    Circuit.synthCrossAddressChecksSynthesisSummary
    V1.PlannedSummaryBlock.summaries V1.PlannedSummaryBlock.blocks
  decide +kernel


end Zcash.Circuits.Action
