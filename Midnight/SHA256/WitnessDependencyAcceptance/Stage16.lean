import Midnight.Math.Witness.DependencySnapshotSyntax
import Midnight.SHA256.WitnessDependencyAcceptanceData
import Midnight.SHA256.WitnessDependencyAcceptance.Stage15

namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

def prepare12Physical : List (DependencyPlan.PlanAssignment F) := RegionPlan.lower place prepare12Plan 69
theorem prepare12Count : prepare12Plan.length = 1 := by decide +kernel
dependency_snapshot_step prepare12 tree1256 from prepare11After
theorem prepare12Ordered : DependencyPlan.ordered place prepare11After prepare12Physical = true := by cbv

end Midnight.SHA256.WitnessDependencyAcceptance
