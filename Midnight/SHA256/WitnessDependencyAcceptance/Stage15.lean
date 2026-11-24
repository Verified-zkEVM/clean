import Midnight.Math.Witness.DependencySnapshotSyntax
import Midnight.SHA256.WitnessDependencyAcceptanceData
import Midnight.SHA256.WitnessDependencyAcceptance.Stage14

namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

def prepare11Physical : List (DependencyPlan.PlanAssignment F) := RegionPlan.lower place prepare11Plan 68
theorem prepare11Count : prepare11Plan.length = 1 := by decide +kernel
dependency_snapshot_step prepare11 tree1167 from prepare10After
theorem prepare11Ordered : DependencyPlan.ordered place prepare10After prepare11Physical = true := by cbv

end Midnight.SHA256.WitnessDependencyAcceptance
