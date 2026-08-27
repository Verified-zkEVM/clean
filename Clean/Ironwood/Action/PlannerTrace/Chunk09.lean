import Clean.Ironwood.Action.PlannerTrace.Chunk08

namespace Zcash.Circuits.Action

open Halo2 FloorPlanner

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep108 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 108)
      ((actionExactPlannerTrace.drop 108).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep109 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 109)
      ((actionExactPlannerTrace.drop 109).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep110 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 110)
      ((actionExactPlannerTrace.drop 110).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep111 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 111)
      ((actionExactPlannerTrace.drop 111).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep112 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 112)
      ((actionExactPlannerTrace.drop 112).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep113 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 113)
      ((actionExactPlannerTrace.drop 113).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep114 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 114)
      ((actionExactPlannerTrace.drop 114).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep115 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 115)
      ((actionExactPlannerTrace.drop 115).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep116 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 116)
      ((actionExactPlannerTrace.drop 116).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep117 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 117)
      ((actionExactPlannerTrace.drop 117).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep118 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 118)
      ((actionExactPlannerTrace.drop 118).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep119 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 119)
      ((actionExactPlannerTrace.drop 119).take 1) := by
  action_exact_planner_step

theorem actionExactPlannerStepsChunk09
    (index : ℕ) (hlower : 108 ≤ index) (hupper : index < 120) :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take index)
      ((actionExactPlannerTrace.drop index).take 1) := by
  interval_cases index
  · exact actionExactPlannerStep108
  · exact actionExactPlannerStep109
  · exact actionExactPlannerStep110
  · exact actionExactPlannerStep111
  · exact actionExactPlannerStep112
  · exact actionExactPlannerStep113
  · exact actionExactPlannerStep114
  · exact actionExactPlannerStep115
  · exact actionExactPlannerStep116
  · exact actionExactPlannerStep117
  · exact actionExactPlannerStep118
  · exact actionExactPlannerStep119

end Zcash.Circuits.Action
