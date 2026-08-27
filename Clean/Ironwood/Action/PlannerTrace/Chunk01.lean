import Clean.Ironwood.Action.PlannerTrace.Chunk00

namespace Zcash.Circuits.Action

open Halo2 FloorPlanner

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep12 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 12)
      ((actionExactPlannerTrace.drop 12).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep13 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 13)
      ((actionExactPlannerTrace.drop 13).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep14 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 14)
      ((actionExactPlannerTrace.drop 14).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep15 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 15)
      ((actionExactPlannerTrace.drop 15).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep16 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 16)
      ((actionExactPlannerTrace.drop 16).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep17 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 17)
      ((actionExactPlannerTrace.drop 17).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep18 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 18)
      ((actionExactPlannerTrace.drop 18).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep19 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 19)
      ((actionExactPlannerTrace.drop 19).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep20 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 20)
      ((actionExactPlannerTrace.drop 20).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep21 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 21)
      ((actionExactPlannerTrace.drop 21).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep22 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 22)
      ((actionExactPlannerTrace.drop 22).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep23 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 23)
      ((actionExactPlannerTrace.drop 23).take 1) := by
  action_exact_planner_step

theorem actionExactPlannerStepsChunk01
    (index : ℕ) (hlower : 12 ≤ index) (hupper : index < 24) :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take index)
      ((actionExactPlannerTrace.drop index).take 1) := by
  interval_cases index
  · exact actionExactPlannerStep12
  · exact actionExactPlannerStep13
  · exact actionExactPlannerStep14
  · exact actionExactPlannerStep15
  · exact actionExactPlannerStep16
  · exact actionExactPlannerStep17
  · exact actionExactPlannerStep18
  · exact actionExactPlannerStep19
  · exact actionExactPlannerStep20
  · exact actionExactPlannerStep21
  · exact actionExactPlannerStep22
  · exact actionExactPlannerStep23

end Zcash.Circuits.Action
