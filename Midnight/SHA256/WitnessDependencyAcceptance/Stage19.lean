import Midnight.Math.Witness.DependencySnapshotSyntax
import Midnight.SHA256.WitnessDependencyAcceptanceData
import Midnight.SHA256.WitnessDependencyAcceptance.Stage18

namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

def prepare15Physical : List (DependencyPlan.PlanAssignment F) := RegionPlan.lower place prepare15Plan 72
theorem prepare15Count : prepare15Plan.length = 1 := by decide +kernel
dependency_snapshot_step prepare15 tree1560 from prepare14After
theorem prepare15Ordered : DependencyPlan.ordered place prepare14After prepare15Physical = true := by cbv

end Midnight.SHA256.WitnessDependencyAcceptance
