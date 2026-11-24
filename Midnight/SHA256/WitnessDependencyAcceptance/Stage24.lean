import Midnight.Math.Witness.DependencySnapshotSyntax
import Midnight.SHA256.WitnessDependencyAcceptanceData
import Midnight.SHA256.WitnessDependencyAcceptance.Stage23

namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

def expand20Physical : List (DependencyPlan.PlanAssignment F) := RegionPlan.lower place expand20Plan 85
theorem expand20Count : expand20Plan.length = 3 := by decide +kernel
dependency_snapshot_step expand20 tree2340 from expand19After
theorem expand20Ordered : DependencyPlan.ordered place expand19After expand20Physical = true := by decide +kernel

end Midnight.SHA256.WitnessDependencyAcceptance
