import Midnight.Math.Witness.DependencySnapshotSyntax
import Midnight.SHA256.WitnessDependencyAcceptanceData
import Midnight.SHA256.WitnessDependencyAcceptance.Stage48

namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

def expand45Physical : List (DependencyPlan.PlanAssignment F) := RegionPlan.lower place expand45Plan 160
theorem expand45Count : expand45Plan.length = 3 := by decide +kernel
dependency_snapshot_step expand45 tree6880 from expand44After
theorem expand45Ordered : DependencyPlan.ordered place expand44After expand45Physical = true := by decide +kernel

end Midnight.SHA256.WitnessDependencyAcceptance
