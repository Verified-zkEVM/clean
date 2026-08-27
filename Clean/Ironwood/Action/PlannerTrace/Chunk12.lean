import Clean.Ironwood.Action.PlannerTrace.Chunk11

namespace Zcash.Circuits.Action

open Halo2 FloorPlanner

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep144 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 144)
      ((actionExactPlannerTrace.drop 144).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep145 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 145)
      ((actionExactPlannerTrace.drop 145).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep146 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 146)
      ((actionExactPlannerTrace.drop 146).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep147 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 147)
      ((actionExactPlannerTrace.drop 147).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep148 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 148)
      ((actionExactPlannerTrace.drop 148).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep149 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 149)
      ((actionExactPlannerTrace.drop 149).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep150 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 150)
      ((actionExactPlannerTrace.drop 150).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep151 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 151)
      ((actionExactPlannerTrace.drop 151).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep152 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 152)
      ((actionExactPlannerTrace.drop 152).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep153 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 153)
      ((actionExactPlannerTrace.drop 153).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep154 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 154)
      ((actionExactPlannerTrace.drop 154).take 1) := by
  action_exact_planner_step

set_option maxRecDepth 10000 in
private theorem actionExactPlannerStep155 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take 155)
      ((actionExactPlannerTrace.drop 155).take 1) := by
  action_exact_planner_step

theorem actionExactPlannerStepsChunk12
    (index : ℕ) (hlower : 144 ≤ index) (hupper : index < 156) :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take index)
      ((actionExactPlannerTrace.drop index).take 1) := by
  interval_cases index
  · exact actionExactPlannerStep144
  · exact actionExactPlannerStep145
  · exact actionExactPlannerStep146
  · exact actionExactPlannerStep147
  · exact actionExactPlannerStep148
  · exact actionExactPlannerStep149
  · exact actionExactPlannerStep150
  · exact actionExactPlannerStep151
  · exact actionExactPlannerStep152
  · exact actionExactPlannerStep153
  · exact actionExactPlannerStep154
  · exact actionExactPlannerStep155

end Zcash.Circuits.Action
