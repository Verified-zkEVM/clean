import Midnight.Math.Witness.DependencySnapshotSyntax
import Midnight.SHA256.WitnessDependencyAcceptanceData
import Midnight.SHA256.WitnessDependencyAcceptance.Stage45

namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

def expand42Physical : List (DependencyPlan.PlanAssignment F) := RegionPlan.lower place expand42Plan 151
theorem expand42Count : expand42Plan.length = 3 := by decide +kernel
dependency_snapshot_step expand42 tree6306 from expand41After
theorem expand42Ordered : DependencyPlan.ordered place expand41After expand42Physical = true := by decide +kernel

end Midnight.SHA256.WitnessDependencyAcceptance
