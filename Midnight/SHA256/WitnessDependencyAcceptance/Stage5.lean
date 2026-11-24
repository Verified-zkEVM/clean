import Midnight.Math.Witness.DependencySnapshotSyntax
import Midnight.SHA256.WitnessDependencyAcceptanceData
import Midnight.SHA256.WitnessDependencyAcceptance.Stage4

namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

def prepare1Physical : List (DependencyPlan.PlanAssignment F) := RegionPlan.lower place prepare1Plan 58
theorem prepare1Count : prepare1Plan.length = 1 := by decide +kernel
dependency_snapshot_step prepare1 tree317 from prepare0After
theorem prepare1Ordered : DependencyPlan.ordered place prepare0After prepare1Physical = true := by cbv

end Midnight.SHA256.WitnessDependencyAcceptance
