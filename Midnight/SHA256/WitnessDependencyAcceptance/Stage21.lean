import Midnight.Math.Witness.DependencySnapshotSyntax
import Midnight.SHA256.WitnessDependencyAcceptanceData
import Midnight.SHA256.WitnessDependencyAcceptance.Stage20

namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

def expand17Physical : List (DependencyPlan.PlanAssignment F) := RegionPlan.lower place expand17Plan 76
theorem expand17Count : expand17Plan.length = 3 := by decide +kernel
dependency_snapshot_step expand17 tree1852 from expand16After
theorem expand17Ordered : DependencyPlan.ordered place expand16After expand17Physical = true := by decide +kernel

end Midnight.SHA256.WitnessDependencyAcceptance
