import Midnight.Math.Witness.DependencySnapshotSyntax
import Midnight.SHA256.WitnessDependencyAcceptanceData
import Midnight.SHA256.WitnessDependencyAcceptance.Stage16

namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

def prepare13Physical : List (DependencyPlan.PlanAssignment F) := RegionPlan.lower place prepare13Plan 70
theorem prepare13Count : prepare13Plan.length = 1 := by decide +kernel
dependency_snapshot_step prepare13 tree1356 from prepare12After
theorem prepare13Ordered : DependencyPlan.ordered place prepare12After prepare13Physical = true := by cbv

end Midnight.SHA256.WitnessDependencyAcceptance
