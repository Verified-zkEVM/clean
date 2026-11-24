import Midnight.Math.Witness.DependencySnapshotSyntax
import Midnight.SHA256.WitnessDependencyAcceptanceData
import Midnight.SHA256.WitnessDependencyAcceptance.Stage62

namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

def expand59Physical : List (DependencyPlan.PlanAssignment F) := RegionPlan.lower place expand59Plan 202
theorem expand59Count : expand59Plan.length = 3 := by decide +kernel
dependency_snapshot_step expand59 tree9620 from expand58After
theorem expand59Ordered : DependencyPlan.ordered place expand58After expand59Physical = true := by decide +kernel

end Midnight.SHA256.WitnessDependencyAcceptance
