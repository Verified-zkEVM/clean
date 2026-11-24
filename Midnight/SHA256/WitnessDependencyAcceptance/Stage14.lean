import Midnight.Math.Witness.DependencySnapshotSyntax
import Midnight.SHA256.WitnessDependencyAcceptanceData
import Midnight.SHA256.WitnessDependencyAcceptance.Stage13

namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

def prepare10Physical : List (DependencyPlan.PlanAssignment F) := RegionPlan.lower place prepare10Plan 67
theorem prepare10Count : prepare10Plan.length = 1 := by decide +kernel
dependency_snapshot_step prepare10 tree1071 from prepare9After
theorem prepare10Ordered : DependencyPlan.ordered place prepare9After prepare10Physical = true := by cbv

end Midnight.SHA256.WitnessDependencyAcceptance
