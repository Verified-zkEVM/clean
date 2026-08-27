import Clean.Ironwood.Action.PlannerTrace.Chunk09

namespace Zcash.Circuits.Action

open Halo2 FloorPlanner

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep120 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 120)
      ((actionExactPlannerTrace.drop 120).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep121 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 121)
      ((actionExactPlannerTrace.drop 121).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep122 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 122)
      ((actionExactPlannerTrace.drop 122).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep123 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 123)
      ((actionExactPlannerTrace.drop 123).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep124 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 124)
      ((actionExactPlannerTrace.drop 124).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep125 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 125)
      ((actionExactPlannerTrace.drop 125).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep126 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 126)
      ((actionExactPlannerTrace.drop 126).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep127 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 127)
      ((actionExactPlannerTrace.drop 127).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep128 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 128)
      ((actionExactPlannerTrace.drop 128).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep129 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 129)
      ((actionExactPlannerTrace.drop 129).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep130 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 130)
      ((actionExactPlannerTrace.drop 130).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep131 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 131)
      ((actionExactPlannerTrace.drop 131).take 1) := by
  action_exact_planner_step

theorem actionExactPlannerStepsChunk10
    (index : ℕ) (hlower : 120 ≤ index) (hupper : index < 132) :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take index)
      ((actionExactPlannerTrace.drop index).take 1) := by
  interval_cases index
  · exact actionExactPlannerStep120
  · exact actionExactPlannerStep121
  · exact actionExactPlannerStep122
  · exact actionExactPlannerStep123
  · exact actionExactPlannerStep124
  · exact actionExactPlannerStep125
  · exact actionExactPlannerStep126
  · exact actionExactPlannerStep127
  · exact actionExactPlannerStep128
  · exact actionExactPlannerStep129
  · exact actionExactPlannerStep130
  · exact actionExactPlannerStep131

end Zcash.Circuits.Action
