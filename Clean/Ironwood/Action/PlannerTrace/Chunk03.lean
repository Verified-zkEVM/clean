import Clean.Ironwood.Action.PlannerTrace.Chunk02

namespace Zcash.Circuits.Action

open Halo2 FloorPlanner

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep36 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 36)
      ((actionExactPlannerTrace.drop 36).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep37 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 37)
      ((actionExactPlannerTrace.drop 37).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep38 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 38)
      ((actionExactPlannerTrace.drop 38).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep39 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 39)
      ((actionExactPlannerTrace.drop 39).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep40 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 40)
      ((actionExactPlannerTrace.drop 40).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep41 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 41)
      ((actionExactPlannerTrace.drop 41).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep42 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 42)
      ((actionExactPlannerTrace.drop 42).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep43 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 43)
      ((actionExactPlannerTrace.drop 43).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep44 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 44)
      ((actionExactPlannerTrace.drop 44).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep45 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 45)
      ((actionExactPlannerTrace.drop 45).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep46 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 46)
      ((actionExactPlannerTrace.drop 46).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep47 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 47)
      ((actionExactPlannerTrace.drop 47).take 1) := by
  action_exact_planner_step

theorem actionExactPlannerStepsChunk03
    (index : ℕ) (hlower : 36 ≤ index) (hupper : index < 48) :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take index)
      ((actionExactPlannerTrace.drop index).take 1) := by
  interval_cases index
  · exact actionExactPlannerStep36
  · exact actionExactPlannerStep37
  · exact actionExactPlannerStep38
  · exact actionExactPlannerStep39
  · exact actionExactPlannerStep40
  · exact actionExactPlannerStep41
  · exact actionExactPlannerStep42
  · exact actionExactPlannerStep43
  · exact actionExactPlannerStep44
  · exact actionExactPlannerStep45
  · exact actionExactPlannerStep46
  · exact actionExactPlannerStep47

end Zcash.Circuits.Action
