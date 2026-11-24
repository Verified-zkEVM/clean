import Midnight.Math.Witness.DependencySnapshotSyntax
import Midnight.SHA256.WitnessDependencyAcceptanceData
import Midnight.SHA256.WitnessDependencyAcceptance.Stage66

namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

def expand63Physical : List (DependencyPlan.PlanAssignment F) := RegionPlan.lower place expand63Plan 214
theorem expand63Count : expand63Plan.length = 3 := by decide +kernel
dependency_snapshot_step expand63 tree10444 from expand62After
theorem expand63Ordered : DependencyPlan.ordered place expand62After expand63Physical = true := by decide +kernel

end Midnight.SHA256.WitnessDependencyAcceptance
