import Midnight.Math.Witness.DependencySnapshotSyntax
import Midnight.SHA256.WitnessDependencyAcceptanceData
import Midnight.SHA256.WitnessDependencyAcceptance.Stage28

namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

def expand25Physical : List (DependencyPlan.PlanAssignment F) := RegionPlan.lower place expand25Plan 100
theorem expand25Count : expand25Plan.length = 3 := by decide +kernel
dependency_snapshot_step expand25 tree3195 from expand24After
theorem expand25Ordered : DependencyPlan.ordered place expand24After expand25Physical = true := by decide +kernel

end Midnight.SHA256.WitnessDependencyAcceptance
