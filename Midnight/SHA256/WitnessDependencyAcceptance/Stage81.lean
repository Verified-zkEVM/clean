import Midnight.Math.Witness.DependencySnapshotSyntax
import Midnight.SHA256.WitnessDependencyAcceptanceData
import Midnight.SHA256.WitnessDependencyAcceptance.Stage80

namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

def round13Physical : List (DependencyPlan.PlanAssignment F) := RegionPlan.lower place round13Plan 309
theorem round13Count : round13Plan.length = 7 := by decide +kernel
dependency_snapshot_step round13 tree14470 from round12After
theorem round13Ordered : DependencyPlan.ordered place round12After round13Physical = true := by decide +kernel

end Midnight.SHA256.WitnessDependencyAcceptance
