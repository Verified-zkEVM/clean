import Clean.Ironwood.Action.PlannerTrace.Chunk12

namespace Zcash.Circuits.Action

open Halo2 FloorPlanner

/-- The compact literal trace satisfies every least-fit planner transition. -/
theorem actionExactPlannerTrace_traceLawfulAfter :
    V1.PlannedSummaryBlock.TraceLawfulAfter [] actionExactPlannerTrace := by
  apply V1.PlannedSummaryBlock.traceLawfulAfter_of_steps
  intro index hindex
  have hlength : actionExactPlannerTrace.length = 156 := by rfl
  rw [hlength] at hindex
  have hstep : V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionExactPlannerTrace.take index)
      ((actionExactPlannerTrace.drop index).take 1) := by
    by_cases h0 : index < 12
    · exact actionExactPlannerStepsChunk00 index (by omega) h0
    · by_cases h1 : index < 24
      · exact actionExactPlannerStepsChunk01 index (by omega) h1
      · by_cases h2 : index < 36
        · exact actionExactPlannerStepsChunk02 index (by omega) h2
        · by_cases h3 : index < 48
          · exact actionExactPlannerStepsChunk03 index (by omega) h3
          · by_cases h4 : index < 60
            · exact actionExactPlannerStepsChunk04 index (by omega) h4
            · by_cases h5 : index < 72
              · exact actionExactPlannerStepsChunk05 index (by omega) h5
              · by_cases h6 : index < 84
                · exact actionExactPlannerStepsChunk06 index (by omega) h6
                · by_cases h7 : index < 96
                  · exact actionExactPlannerStepsChunk07 index (by omega) h7
                  · by_cases h8 : index < 108
                    · exact actionExactPlannerStepsChunk08 index (by omega) h8
                    · by_cases h9 : index < 120
                      · exact actionExactPlannerStepsChunk09 index (by omega) h9
                      · by_cases h10 : index < 132
                        · exact actionExactPlannerStepsChunk10 index (by omega) h10
                        · by_cases h11 : index < 144
                          · exact actionExactPlannerStepsChunk11 index (by omega) h11
                          · by_cases h12 : index < 156
                            · exact actionExactPlannerStepsChunk12 index (by omega) h12
                            · omega
  rw [List.take_one_drop_eq_of_lt_length hindex] at hstep
  exact hstep

theorem actionExactPlannerTrace_lawful :
    V1.PlannedSummaryBlock.Lawful V1.AllocationView.empty
      actionExactPlannerTrace := by
  exact V1.PlannedSummaryBlock.lawful_of_traceLawfulAfter []
    actionExactPlannerTrace (by simp)
      actionExactPlannerTrace_traceLawfulAfter

end Zcash.Circuits.Action
