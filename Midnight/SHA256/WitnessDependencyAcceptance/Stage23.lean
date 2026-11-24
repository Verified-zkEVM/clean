import Midnight.Math.Witness.DependencySnapshotSyntax
import Midnight.SHA256.WitnessDependencyAcceptanceData
import Midnight.SHA256.WitnessDependencyAcceptance.Stage22

namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

def expand19Physical : List (DependencyPlan.PlanAssignment F) := RegionPlan.lower place expand19Plan 82
theorem expand19Count : expand19Plan.length = 3 := by decide +kernel
dependency_snapshot_step expand19 tree2178 from expand18After
theorem expand19Ordered : DependencyPlan.ordered place expand18After expand19Physical = true := by decide +kernel

end Midnight.SHA256.WitnessDependencyAcceptance
