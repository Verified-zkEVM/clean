import Midnight.Math.Witness.DependencySnapshotSyntax
import Midnight.SHA256.WitnessDependencyAcceptanceData
import Midnight.SHA256.WitnessDependencyAcceptance.Stage35

namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

def expand32Physical : List (DependencyPlan.PlanAssignment F) := RegionPlan.lower place expand32Plan 121
theorem expand32Count : expand32Plan.length = 3 := by decide +kernel
dependency_snapshot_step expand32 tree4456 from expand31After
theorem expand32Ordered : DependencyPlan.ordered place expand31After expand32Physical = true := by decide +kernel

end Midnight.SHA256.WitnessDependencyAcceptance
