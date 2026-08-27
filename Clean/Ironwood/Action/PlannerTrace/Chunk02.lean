import Clean.Ironwood.Action.PlannerTrace.Chunk01

namespace Zcash.Circuits.Action

open Halo2 FloorPlanner

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep24 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 24)
      ((actionExactPlannerTrace.drop 24).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep25 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 25)
      ((actionExactPlannerTrace.drop 25).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep26 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 26)
      ((actionExactPlannerTrace.drop 26).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep27 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 27)
      ((actionExactPlannerTrace.drop 27).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep28 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 28)
      ((actionExactPlannerTrace.drop 28).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep29 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 29)
      ((actionExactPlannerTrace.drop 29).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep30 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 30)
      ((actionExactPlannerTrace.drop 30).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep31 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 31)
      ((actionExactPlannerTrace.drop 31).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep32 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 32)
      ((actionExactPlannerTrace.drop 32).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep33 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 33)
      ((actionExactPlannerTrace.drop 33).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep34 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 34)
      ((actionExactPlannerTrace.drop 34).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep35 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 35)
      ((actionExactPlannerTrace.drop 35).take 1) := by
  action_exact_planner_step

theorem actionExactPlannerStepsChunk02
    (index : ℕ) (hlower : 24 ≤ index) (hupper : index < 36) :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take index)
      ((actionExactPlannerTrace.drop index).take 1) := by
  interval_cases index
  · exact actionExactPlannerStep24
  · exact actionExactPlannerStep25
  · exact actionExactPlannerStep26
  · exact actionExactPlannerStep27
  · exact actionExactPlannerStep28
  · exact actionExactPlannerStep29
  · exact actionExactPlannerStep30
  · exact actionExactPlannerStep31
  · exact actionExactPlannerStep32
  · exact actionExactPlannerStep33
  · exact actionExactPlannerStep34
  · exact actionExactPlannerStep35

end Zcash.Circuits.Action
