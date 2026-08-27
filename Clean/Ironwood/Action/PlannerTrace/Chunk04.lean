import Clean.Ironwood.Action.PlannerTrace.Chunk03

namespace Zcash.Circuits.Action

open Halo2 FloorPlanner

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep48 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 48)
      ((actionExactPlannerTrace.drop 48).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep49 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 49)
      ((actionExactPlannerTrace.drop 49).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep50 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 50)
      ((actionExactPlannerTrace.drop 50).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep51 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 51)
      ((actionExactPlannerTrace.drop 51).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep52 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 52)
      ((actionExactPlannerTrace.drop 52).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep53 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 53)
      ((actionExactPlannerTrace.drop 53).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep54 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 54)
      ((actionExactPlannerTrace.drop 54).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep55 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 55)
      ((actionExactPlannerTrace.drop 55).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep56 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 56)
      ((actionExactPlannerTrace.drop 56).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep57 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 57)
      ((actionExactPlannerTrace.drop 57).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep58 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 58)
      ((actionExactPlannerTrace.drop 58).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep59 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 59)
      ((actionExactPlannerTrace.drop 59).take 1) := by
  action_exact_planner_step

theorem actionExactPlannerStepsChunk04
    (index : ℕ) (hlower : 48 ≤ index) (hupper : index < 60) :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take index)
      ((actionExactPlannerTrace.drop index).take 1) := by
  interval_cases index
  · exact actionExactPlannerStep48
  · exact actionExactPlannerStep49
  · exact actionExactPlannerStep50
  · exact actionExactPlannerStep51
  · exact actionExactPlannerStep52
  · exact actionExactPlannerStep53
  · exact actionExactPlannerStep54
  · exact actionExactPlannerStep55
  · exact actionExactPlannerStep56
  · exact actionExactPlannerStep57
  · exact actionExactPlannerStep58
  · exact actionExactPlannerStep59

end Zcash.Circuits.Action
