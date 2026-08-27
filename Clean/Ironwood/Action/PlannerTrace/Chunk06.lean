import Clean.Ironwood.Action.PlannerTrace.Chunk05

namespace Zcash.Circuits.Action

open Halo2 FloorPlanner

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep72 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 72)
      ((actionExactPlannerTrace.drop 72).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep73 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 73)
      ((actionExactPlannerTrace.drop 73).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep74 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 74)
      ((actionExactPlannerTrace.drop 74).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep75 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 75)
      ((actionExactPlannerTrace.drop 75).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep76 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 76)
      ((actionExactPlannerTrace.drop 76).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep77 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 77)
      ((actionExactPlannerTrace.drop 77).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep78 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 78)
      ((actionExactPlannerTrace.drop 78).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep79 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 79)
      ((actionExactPlannerTrace.drop 79).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep80 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 80)
      ((actionExactPlannerTrace.drop 80).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep81 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 81)
      ((actionExactPlannerTrace.drop 81).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep82 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 82)
      ((actionExactPlannerTrace.drop 82).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep83 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 83)
      ((actionExactPlannerTrace.drop 83).take 1) := by
  action_exact_planner_step

theorem actionExactPlannerStepsChunk06
    (index : ℕ) (hlower : 72 ≤ index) (hupper : index < 84) :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take index)
      ((actionExactPlannerTrace.drop index).take 1) := by
  interval_cases index
  · exact actionExactPlannerStep72
  · exact actionExactPlannerStep73
  · exact actionExactPlannerStep74
  · exact actionExactPlannerStep75
  · exact actionExactPlannerStep76
  · exact actionExactPlannerStep77
  · exact actionExactPlannerStep78
  · exact actionExactPlannerStep79
  · exact actionExactPlannerStep80
  · exact actionExactPlannerStep81
  · exact actionExactPlannerStep82
  · exact actionExactPlannerStep83

end Zcash.Circuits.Action
