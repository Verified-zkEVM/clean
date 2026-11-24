import Midnight.SHA256.Semantics.WitnessDependencyData
import Midnight.Math.Witness.PlanDecidableEquality
import Midnight.SHA256.Semantics.StageUnfold

namespace Midnight.SHA256.Semantics.WitnessCheckpoints
open Halo2 Midnight.Math.Witness

set_option Elab.async false
set_option maxRecDepth 10000
attribute [local instance] PlanDecidableEquality.assignedCell
  PlanDecidableEquality.relativeAssignment

theorem inputPlanChecked : CompactPlan.observe (inputOperations 0) = inputPlan := by
  decide +kernel

theorem initialPlanChecked : CompactPlan.observe (initialOperations 0) = initialPlan := by
  decide +kernel

theorem paddingPlanChecked : CompactPlan.observe (paddingOperations 0) = paddingPlan := by
  decide +kernel

theorem packingPlanChecked : CompactPlan.observe (packingOperations 0) = packingPlan := by
  decide +kernel

theorem prepare0PlanChecked : CompactPlan.observe (prepare0Operations 0) = prepare0Plan := by
  decide +kernel

theorem prepare1PlanChecked : CompactPlan.observe (prepare1Operations 0) = prepare1Plan := by
  decide +kernel

theorem prepare2PlanChecked : CompactPlan.observe (prepare2Operations 0) = prepare2Plan := by
  decide +kernel

theorem prepare3PlanChecked : CompactPlan.observe (prepare3Operations 0) = prepare3Plan := by
  decide +kernel

end Midnight.SHA256.Semantics.WitnessCheckpoints
