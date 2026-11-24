import Midnight.SHA256.Semantics.WitnessDependencyChecks.Group16
import Midnight.SHA256.Semantics.WitnessDependencyData
import Midnight.Math.Witness.PlanDecidableEquality

namespace Midnight.SHA256.Semantics.WitnessCheckpoints
open Halo2 Midnight.Math.Witness

set_option Elab.async false
set_option maxRecDepth 10000
attribute [local instance] PlanDecidableEquality.assignedCell
  PlanDecidableEquality.relativeAssignment

theorem serialize3PlanChecked : CompactPlan.observe (serialize3Operations 0) = serialize3Plan := by
  decide +kernel

theorem serialize4PlanChecked : CompactPlan.observe (serialize4Operations 0) = serialize4Plan := by
  decide +kernel

theorem serialize5PlanChecked : CompactPlan.observe (serialize5Operations 0) = serialize5Plan := by
  decide +kernel

theorem serialize6PlanChecked : CompactPlan.observe (serialize6Operations 0) = serialize6Plan := by
  decide +kernel

theorem serialize7PlanChecked : CompactPlan.observe (serialize7Operations 0) = serialize7Plan := by
  decide +kernel

theorem publicPlanChecked : CompactPlan.observe (publicOperations 0) = publicPlan := by
  decide +kernel

end Midnight.SHA256.Semantics.WitnessCheckpoints
