import Clean.Ironwood.Action.PlannerTraceData

namespace Zcash.Circuits.Action

open Halo2 FloorPlanner

macro "action_exact_planner_step" : tactic =>
  `(tactic|
    (unfold actionExactPlannerTrace actionPlannerBlocks
     simp only [List.map_cons, List.map_nil, List.take, List.drop,
       List.getD_cons_zero, List.getD_cons_succ,
       V1.PlannedSummaryBlock.TraceLawfulAfter]
     refine ⟨by norm_num,
       by simp [RegionShapeSummary.WellFormed, plannerShape],
       by simp [plannerShape], ?_, ?_, trivial⟩
     · simp [V1.PlannedSummaryBlock.FitsAfterAt, plannerShape,
         RowIntervalsDisjoint]
     · intro candidate hfits
       simp [V1.PlannedSummaryBlock.FitsAfterAt, plannerShape,
         RowIntervalsDisjoint] at hfits
       omega))

end Zcash.Circuits.Action
