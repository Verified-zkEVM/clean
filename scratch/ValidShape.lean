import Clean.Air.WitnessGeneration
open Air.Flat Air.Flat.WitnessGeneration
variable {F : Type} [FiniteField F] {PublicIO : TypeMap} [ProvableType PublicIO]

example (component : Component F) (rowPlan : RowPlan F)
    (h : validateRowPlan component rowPlan = .ok ()) : False := by
  simp only [validateRowPlan] at h
  trace_state
  sorry
example (plan : GenerationPlan F) (ensemble : Ensemble F PublicIO) (rowPlans) (h : plan.align ensemble = .ok rowPlans) : False := by
  simp only [GenerationPlan.align] at h
  trace_state
  sorry
