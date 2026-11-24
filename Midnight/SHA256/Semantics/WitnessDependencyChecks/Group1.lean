import Midnight.SHA256.Semantics.WitnessDependencyChecks.Group0
import Midnight.SHA256.Semantics.WitnessDependencyData
import Midnight.Math.Witness.PlanDecidableEquality

namespace Midnight.SHA256.Semantics.WitnessCheckpoints
open Halo2 Midnight.Math.Witness

set_option Elab.async false
set_option maxRecDepth 10000
attribute [local instance] PlanDecidableEquality.assignedCell
  PlanDecidableEquality.relativeAssignment

theorem prepare4PlanChecked : CompactPlan.observe (prepare4Operations 0) = prepare4Plan := by
  decide +kernel

theorem prepare5PlanChecked : CompactPlan.observe (prepare5Operations 0) = prepare5Plan := by
  decide +kernel

theorem prepare6PlanChecked : CompactPlan.observe (prepare6Operations 0) = prepare6Plan := by
  decide +kernel

theorem prepare7PlanChecked : CompactPlan.observe (prepare7Operations 0) = prepare7Plan := by
  decide +kernel

theorem prepare8PlanChecked : CompactPlan.observe (prepare8Operations 0) = prepare8Plan := by
  decide +kernel

theorem prepare9PlanChecked : CompactPlan.observe (prepare9Operations 0) = prepare9Plan := by
  decide +kernel

theorem prepare10PlanChecked : CompactPlan.observe (prepare10Operations 0) = prepare10Plan := by
  decide +kernel

theorem prepare11PlanChecked : CompactPlan.observe (prepare11Operations 0) = prepare11Plan := by
  decide +kernel

end Midnight.SHA256.Semantics.WitnessCheckpoints
