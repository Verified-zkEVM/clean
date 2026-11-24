import Midnight.Math.Witness.DependencySnapshotSyntax
import Midnight.SHA256.WitnessDependencyAcceptanceData
import Midnight.SHA256.WitnessDependencyAcceptance.Stage0

namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

def initialPhysical : List (DependencyPlan.PlanAssignment F) := RegionPlan.lower place initialPlan 24
theorem initialCount : initialPlan.length = 23 := by decide +kernel
dependency_snapshot_step initial tree77 from inputAfter
theorem initialOrdered : DependencyPlan.ordered place inputAfter initialPhysical = true := by cbv

end Midnight.SHA256.WitnessDependencyAcceptance
