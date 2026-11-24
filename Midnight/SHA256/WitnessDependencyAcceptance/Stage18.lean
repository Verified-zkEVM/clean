import Midnight.Math.Witness.DependencySnapshotSyntax
import Midnight.SHA256.WitnessDependencyAcceptanceData
import Midnight.SHA256.WitnessDependencyAcceptance.Stage17

namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

def prepare14Physical : List (DependencyPlan.PlanAssignment F) := RegionPlan.lower place prepare14Plan 71
theorem prepare14Count : prepare14Plan.length = 1 := by decide +kernel
dependency_snapshot_step prepare14 tree1452 from prepare13After
theorem prepare14Ordered : DependencyPlan.ordered place prepare13After prepare14Physical = true := by cbv

end Midnight.SHA256.WitnessDependencyAcceptance
