import Midnight.Math.Witness.DependencySnapshotSyntax
import Midnight.SHA256.WitnessDependencyAcceptanceData
import Midnight.SHA256.WitnessDependencyAcceptance.Stage8

namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

def prepare5Physical : List (DependencyPlan.PlanAssignment F) := RegionPlan.lower place prepare5Plan 62
theorem prepare5Count : prepare5Plan.length = 1 := by decide +kernel
dependency_snapshot_step prepare5 tree624 from prepare4After
theorem prepare5Ordered : DependencyPlan.ordered place prepare4After prepare5Physical = true := by cbv

end Midnight.SHA256.WitnessDependencyAcceptance
