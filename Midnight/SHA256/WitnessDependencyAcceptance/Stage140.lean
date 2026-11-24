import Midnight.Math.Witness.DependencySnapshotSyntax
import Midnight.SHA256.WitnessDependencyAcceptanceData
import Midnight.SHA256.WitnessDependencyAcceptance.Stage139

namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

def serialize7Physical : List (DependencyPlan.PlanAssignment F) := RegionPlan.lower place serialize7Plan 688
theorem serialize7Count : serialize7Plan.length = 2 := by decide +kernel
dependency_snapshot_step serialize7 tree42488 from serialize6After
theorem serialize7Ordered : DependencyPlan.ordered place serialize6After serialize7Physical = true := by decide +kernel

end Midnight.SHA256.WitnessDependencyAcceptance
