import Midnight.Math.Witness.DependencySnapshotSyntax
import Midnight.SHA256.WitnessDependencyAcceptanceData
import Midnight.SHA256.WitnessDependencyAcceptance.Stage3

namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

def prepare0Physical : List (DependencyPlan.PlanAssignment F) := RegionPlan.lower place prepare0Plan 57
theorem prepare0Count : prepare0Plan.length = 1 := by decide +kernel
dependency_snapshot_step prepare0 tree247 from packingAfter
theorem prepare0Ordered : DependencyPlan.ordered place packingAfter prepare0Physical = true := by cbv

end Midnight.SHA256.WitnessDependencyAcceptance
