import Clean.Ironwood.Action.Shape.PlannerTraceData
import Clean.Halo2.Keygen.FloorPlanner.V1Evaluation

namespace Zcash.Circuits.Action

open Halo2 FloorPlanner

set_option maxRecDepth 1000000 in
/-- The reduced, already-sorted region shapes have the stated exact V1 placement. -/
theorem actionExactPlannerTrace_traceCheck_eq_true :
    V1.CompactPlanner.traceCheck actionExactPlannerTrace [] 0 = true := by
  decide +kernel

theorem actionExactPlannerTrace_lawful :
    V1.PlannedSummaryBlock.Lawful V1.AllocationView.empty
      actionExactPlannerTrace := by
  exact V1.CompactPlanner.lawful_of_traceCheck_eq_true
    actionExactPlannerTrace actionExactPlannerTrace_traceCheck_eq_true

/-- The exact Action placement trace ends at row 1779. -/
theorem actionExactPlannerTrace_endpoint :
    V1.PlannedSummaryBlock.endpointFrom 0 actionExactPlannerTrace = 1779 := by
  rw [V1.PlannedSummaryBlock.endpointFrom_eq_foldl_max]
  unfold actionExactPlannerTrace actionExactPlannerRuns actionPlannerBlocks
    plannerShape
  set_option maxRecDepth 1000000 in decide

end Zcash.Circuits.Action
