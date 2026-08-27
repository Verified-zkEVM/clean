import Clean.Ironwood.Action.PlannerTrace.Chunk07

namespace Zcash.Circuits.Action

open Halo2 FloorPlanner

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep96 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 96)
      ((actionExactPlannerTrace.drop 96).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep97 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 97)
      ((actionExactPlannerTrace.drop 97).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep98 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 98)
      ((actionExactPlannerTrace.drop 98).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep99 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 99)
      ((actionExactPlannerTrace.drop 99).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep100 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 100)
      ((actionExactPlannerTrace.drop 100).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep101 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 101)
      ((actionExactPlannerTrace.drop 101).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep102 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 102)
      ((actionExactPlannerTrace.drop 102).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep103 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 103)
      ((actionExactPlannerTrace.drop 103).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep104 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 104)
      ((actionExactPlannerTrace.drop 104).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep105 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 105)
      ((actionExactPlannerTrace.drop 105).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep106 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 106)
      ((actionExactPlannerTrace.drop 106).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep107 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 107)
      ((actionExactPlannerTrace.drop 107).take 1) := by
  action_exact_planner_step

theorem actionExactPlannerStepsChunk08
    (index : ℕ) (hlower : 96 ≤ index) (hupper : index < 108) :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take index)
      ((actionExactPlannerTrace.drop index).take 1) := by
  interval_cases index
  · exact actionExactPlannerStep96
  · exact actionExactPlannerStep97
  · exact actionExactPlannerStep98
  · exact actionExactPlannerStep99
  · exact actionExactPlannerStep100
  · exact actionExactPlannerStep101
  · exact actionExactPlannerStep102
  · exact actionExactPlannerStep103
  · exact actionExactPlannerStep104
  · exact actionExactPlannerStep105
  · exact actionExactPlannerStep106
  · exact actionExactPlannerStep107

end Zcash.Circuits.Action
