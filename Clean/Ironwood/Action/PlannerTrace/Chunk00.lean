import Clean.Ironwood.Action.PlannerTraceStep

namespace Zcash.Circuits.Action

open Halo2 FloorPlanner

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep0 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 0)
      ((actionExactPlannerTrace.drop 0).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep1 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 1)
      ((actionExactPlannerTrace.drop 1).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep2 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 2)
      ((actionExactPlannerTrace.drop 2).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep3 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 3)
      ((actionExactPlannerTrace.drop 3).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep4 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 4)
      ((actionExactPlannerTrace.drop 4).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep5 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 5)
      ((actionExactPlannerTrace.drop 5).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep6 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 6)
      ((actionExactPlannerTrace.drop 6).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep7 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 7)
      ((actionExactPlannerTrace.drop 7).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep8 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 8)
      ((actionExactPlannerTrace.drop 8).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep9 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 9)
      ((actionExactPlannerTrace.drop 9).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep10 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 10)
      ((actionExactPlannerTrace.drop 10).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep11 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 11)
      ((actionExactPlannerTrace.drop 11).take 1) := by
  action_exact_planner_step

theorem actionExactPlannerStepsChunk00
    (index : ℕ) (hlower : 0 ≤ index) (hupper : index < 12) :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take index)
      ((actionExactPlannerTrace.drop index).take 1) := by
  interval_cases index
  · exact actionExactPlannerStep0
  · exact actionExactPlannerStep1
  · exact actionExactPlannerStep2
  · exact actionExactPlannerStep3
  · exact actionExactPlannerStep4
  · exact actionExactPlannerStep5
  · exact actionExactPlannerStep6
  · exact actionExactPlannerStep7
  · exact actionExactPlannerStep8
  · exact actionExactPlannerStep9
  · exact actionExactPlannerStep10
  · exact actionExactPlannerStep11

end Zcash.Circuits.Action
