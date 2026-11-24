import Midnight.Math.Witness.DependencySnapshotSyntax
import Midnight.SHA256.WitnessDependencyAcceptanceData
import Midnight.SHA256.WitnessDependencyAcceptance.Stage5

namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

def prepare2Physical : List (DependencyPlan.PlanAssignment F) := RegionPlan.lower place prepare2Plan 59
theorem prepare2Count : prepare2Plan.length = 1 := by decide +kernel
dependency_snapshot_step prepare2 tree388 from prepare1After
theorem prepare2Ordered : DependencyPlan.ordered place prepare1After prepare2Physical = true := by cbv

end Midnight.SHA256.WitnessDependencyAcceptance
