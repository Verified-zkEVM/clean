import Midnight.Math.Witness.DependencySnapshotSyntax
import Midnight.SHA256.WitnessDependencyAcceptanceData
import Midnight.SHA256.WitnessDependencyAcceptance.Stage2

namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

def packingPhysical : List (DependencyPlan.PlanAssignment F) := RegionPlan.lower place packingPlan 50
theorem packingCount : packingPlan.length = 7 := by decide +kernel
dependency_snapshot_step packing tree191 from paddingAfter
theorem packingOrdered : DependencyPlan.ordered place paddingAfter packingPhysical = true := by cbv

end Midnight.SHA256.WitnessDependencyAcceptance
