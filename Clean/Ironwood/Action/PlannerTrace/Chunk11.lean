import Clean.Ironwood.Action.PlannerTrace.Chunk10

namespace Zcash.Circuits.Action

open Halo2 FloorPlanner

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep132 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 132)
      ((actionExactPlannerTrace.drop 132).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep133 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 133)
      ((actionExactPlannerTrace.drop 133).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep134 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 134)
      ((actionExactPlannerTrace.drop 134).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep135 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 135)
      ((actionExactPlannerTrace.drop 135).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep136 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 136)
      ((actionExactPlannerTrace.drop 136).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep137 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 137)
      ((actionExactPlannerTrace.drop 137).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep138 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 138)
      ((actionExactPlannerTrace.drop 138).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep139 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 139)
      ((actionExactPlannerTrace.drop 139).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep140 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 140)
      ((actionExactPlannerTrace.drop 140).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep141 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 141)
      ((actionExactPlannerTrace.drop 141).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep142 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 142)
      ((actionExactPlannerTrace.drop 142).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep143 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 143)
      ((actionExactPlannerTrace.drop 143).take 1) := by
  action_exact_planner_step

theorem actionExactPlannerStepsChunk11
    (index : ℕ) (hlower : 132 ≤ index) (hupper : index < 144) :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take index)
      ((actionExactPlannerTrace.drop index).take 1) := by
  interval_cases index
  · exact actionExactPlannerStep132
  · exact actionExactPlannerStep133
  · exact actionExactPlannerStep134
  · exact actionExactPlannerStep135
  · exact actionExactPlannerStep136
  · exact actionExactPlannerStep137
  · exact actionExactPlannerStep138
  · exact actionExactPlannerStep139
  · exact actionExactPlannerStep140
  · exact actionExactPlannerStep141
  · exact actionExactPlannerStep142
  · exact actionExactPlannerStep143

end Zcash.Circuits.Action
