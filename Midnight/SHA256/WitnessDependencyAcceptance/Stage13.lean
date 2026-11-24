import Midnight.Math.Witness.DependencySnapshotSyntax
import Midnight.SHA256.WitnessDependencyAcceptanceData
import Midnight.SHA256.WitnessDependencyAcceptance.Stage12

namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

def prepare9Physical : List (DependencyPlan.PlanAssignment F) := RegionPlan.lower place prepare9Plan 66
theorem prepare9Count : prepare9Plan.length = 1 := by decide +kernel
dependency_snapshot_step prepare9 tree978 from prepare8After
theorem prepare9Ordered : DependencyPlan.ordered place prepare8After prepare9Physical = true := by cbv

end Midnight.SHA256.WitnessDependencyAcceptance
