import Midnight.Math.Witness.DependencySnapshotSyntax
import Midnight.SHA256.WitnessDependencyAcceptanceData
import Midnight.SHA256.WitnessDependencyAcceptance.Stage56

namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

def expand53Physical : List (DependencyPlan.PlanAssignment F) := RegionPlan.lower place expand53Plan 184
theorem expand53Count : expand53Plan.length = 3 := by decide +kernel
dependency_snapshot_step expand53 tree8438 from expand52After
theorem expand53Ordered : DependencyPlan.ordered place expand52After expand53Physical = true := by decide +kernel

end Midnight.SHA256.WitnessDependencyAcceptance
