import Midnight.Math.Witness.DependencySnapshotSyntax
import Midnight.SHA256.WitnessDependencyAcceptanceData
import Midnight.SHA256.WitnessDependencyAcceptance.Stage41

namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

def expand38Physical : List (DependencyPlan.PlanAssignment F) := RegionPlan.lower place expand38Plan 139
theorem expand38Count : expand38Plan.length = 3 := by decide +kernel
dependency_snapshot_step expand38 tree5576 from expand37After
theorem expand38Ordered : DependencyPlan.ordered place expand37After expand38Physical = true := by decide +kernel

end Midnight.SHA256.WitnessDependencyAcceptance
