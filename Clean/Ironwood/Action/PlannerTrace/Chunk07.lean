import Clean.Ironwood.Action.PlannerTrace.Chunk06

namespace Zcash.Circuits.Action

open Halo2 FloorPlanner

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep84 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 84)
      ((actionExactPlannerTrace.drop 84).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep85 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 85)
      ((actionExactPlannerTrace.drop 85).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep86 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 86)
      ((actionExactPlannerTrace.drop 86).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep87 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 87)
      ((actionExactPlannerTrace.drop 87).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep88 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 88)
      ((actionExactPlannerTrace.drop 88).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep89 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 89)
      ((actionExactPlannerTrace.drop 89).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep90 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 90)
      ((actionExactPlannerTrace.drop 90).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep91 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 91)
      ((actionExactPlannerTrace.drop 91).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep92 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 92)
      ((actionExactPlannerTrace.drop 92).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep93 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 93)
      ((actionExactPlannerTrace.drop 93).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep94 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 94)
      ((actionExactPlannerTrace.drop 94).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep95 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 95)
      ((actionExactPlannerTrace.drop 95).take 1) := by
  action_exact_planner_step

theorem actionExactPlannerStepsChunk07
    (index : ℕ) (hlower : 84 ≤ index) (hupper : index < 96) :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take index)
      ((actionExactPlannerTrace.drop index).take 1) := by
  interval_cases index
  · exact actionExactPlannerStep84
  · exact actionExactPlannerStep85
  · exact actionExactPlannerStep86
  · exact actionExactPlannerStep87
  · exact actionExactPlannerStep88
  · exact actionExactPlannerStep89
  · exact actionExactPlannerStep90
  · exact actionExactPlannerStep91
  · exact actionExactPlannerStep92
  · exact actionExactPlannerStep93
  · exact actionExactPlannerStep94
  · exact actionExactPlannerStep95

end Zcash.Circuits.Action
