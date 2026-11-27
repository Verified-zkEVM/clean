module

public import Clean.Ironwood.Action.Shape.PlannerSortBridge
public import Clean.Ironwood.Action.Shape.PlannerTraceCertificate

@[expose] public section

namespace Zcash.Circuits.Action

open Halo2 FloorPlanner

/-- The exact consensus-order physical summary stream, retaining maximal runs. -/
def actionExactSortedPlannerSummaries : List RegionShapeSummary :=
  V1.PlannedSummaryBlock.summaries actionExactPlannerTrace ++
  List.replicate 2 { columns := [], rowCount := 0 }

/-- Exact Action start rows in consensus sort order. -/
def actionExactSortedStarts : List Nat :=
  V1.PlannedSummaryBlock.starts actionExactPlannerTrace ++ [0, 0]

private def insertRegionColumn (item : RegionColumn) : List RegionColumn → List RegionColumn
  | [] => [item]
  | head :: tail =>
      if item.lt head then item :: head :: tail else head :: insertRegionColumn item tail

private def sortRegionColumnsEval : List RegionColumn → List RegionColumn
  | [] => []
  | head :: tail => insertRegionColumn head (sortRegionColumnsEval tail)

private theorem insertRegionColumn_eq (item : RegionColumn) (cols : List RegionColumn) :
    List.orderedInsert (fun left right => left.lt right = true) item cols =
      insertRegionColumn item cols := by
  induction cols with
  | nil => simp [insertRegionColumn]
  | cons head tail ih =>
      simp only [List.orderedInsert_cons, insertRegionColumn, ih]

private theorem sortRegionColumns_eq_eval (cols : List RegionColumn) :
    sortRegionColumns cols = sortRegionColumnsEval cols := by
  induction cols with
  | nil => simp [sortRegionColumns, sortRegionColumnsEval]
  | cons head tail ih =>
      simp only [sortRegionColumns, List.insertionSort_cons, sortRegionColumnsEval]
      rw [← sortRegionColumns, ih, insertRegionColumn_eq]

private def normalizedEval (summary : RegionShapeSummary) : RegionShapeSummary :=
  { summary with columns := sortRegionColumnsEval summary.columns }

private theorem normalized_eq_eval :
    RegionShapeSummary.normalized = normalizedEval := by
  funext summary
  simp only [RegionShapeSummary.normalized, normalizedEval, sortRegionColumns_eq_eval]

set_option maxRecDepth 1000000 in
/-- Each reduced summary in consensus order has the exact physical footprint
recorded by the compact trace. -/
theorem actionSortedPlannerSummaries_equivalent_exact :
    List.Forall₂ RegionShapeSummary.PlacementEquivalent
      actionSortedPlannerSummaries actionExactSortedPlannerSummaries := by
  apply RegionShapeSummary.forall₂_placementEquivalent_of_map_normalized_eq
  rw [normalized_eq_eval]
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
