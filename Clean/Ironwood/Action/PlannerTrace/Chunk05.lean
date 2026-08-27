import Clean.Ironwood.Action.PlannerTrace.Chunk04

namespace Zcash.Circuits.Action

open Halo2 FloorPlanner

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep60 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 60)
      ((actionExactPlannerTrace.drop 60).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep61 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 61)
      ((actionExactPlannerTrace.drop 61).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep62 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 62)
      ((actionExactPlannerTrace.drop 62).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep63 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 63)
      ((actionExactPlannerTrace.drop 63).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep64 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 64)
      ((actionExactPlannerTrace.drop 64).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep65 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 65)
      ((actionExactPlannerTrace.drop 65).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep66 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 66)
      ((actionExactPlannerTrace.drop 66).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep67 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 67)
      ((actionExactPlannerTrace.drop 67).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep68 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 68)
      ((actionExactPlannerTrace.drop 68).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep69 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 69)
      ((actionExactPlannerTrace.drop 69).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep70 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 70)
      ((actionExactPlannerTrace.drop 70).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep71 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 71)
      ((actionExactPlannerTrace.drop 71).take 1) := by
  action_exact_planner_step

theorem actionExactPlannerStepsChunk05
    (index : ℕ) (hlower : 60 ≤ index) (hupper : index < 72) :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take index)
      ((actionExactPlannerTrace.drop index).take 1) := by
  interval_cases index
  · exact actionExactPlannerStep60
  · exact actionExactPlannerStep61
  · exact actionExactPlannerStep62
  · exact actionExactPlannerStep63
  · exact actionExactPlannerStep64
  · exact actionExactPlannerStep65
  · exact actionExactPlannerStep66
  · exact actionExactPlannerStep67
  · exact actionExactPlannerStep68
  · exact actionExactPlannerStep69
  · exact actionExactPlannerStep70
  · exact actionExactPlannerStep71

end Zcash.Circuits.Action
