import Midnight.Math.Witness.DependencySnapshotSyntax
import Midnight.SHA256.WitnessDependencyAcceptanceData
import Midnight.SHA256.WitnessDependencyAcceptance.Stage24

namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

def expand21Physical : List (DependencyPlan.PlanAssignment F) := RegionPlan.lower place expand21Plan 88
theorem expand21Count : expand21Plan.length = 3 := by decide +kernel
dependency_snapshot_step expand21 tree2515 from expand20After
theorem expand21Ordered : DependencyPlan.ordered place expand20After expand21Physical = true := by decide +kernel

end Midnight.SHA256.WitnessDependencyAcceptance
