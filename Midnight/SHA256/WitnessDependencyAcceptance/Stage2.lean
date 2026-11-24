import Midnight.Math.Witness.DependencySnapshotSyntax
import Midnight.SHA256.WitnessDependencyAcceptanceData
import Midnight.SHA256.WitnessDependencyAcceptance.Stage1

namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

def paddingPhysical : List (DependencyPlan.PlanAssignment F) := RegionPlan.lower place paddingPlan 47
theorem paddingCount : paddingPlan.length = 3 := by decide +kernel
dependency_snapshot_step padding tree85 from initialAfter
theorem paddingOrdered : DependencyPlan.ordered place initialAfter paddingPhysical = true := by cbv

end Midnight.SHA256.WitnessDependencyAcceptance
