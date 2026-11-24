import Midnight.Math.Witness.DependencySnapshotSyntax
import Midnight.SHA256.WitnessDependencyAcceptanceData
import Midnight.SHA256.WitnessDependencyAcceptance.Stage72

namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

def round5Physical : List (DependencyPlan.PlanAssignment F) := RegionPlan.lower place round5Plan 253
theorem round5Count : round5Plan.length = 7 := by decide +kernel
dependency_snapshot_step round5 tree12140 from round4After
theorem round5Ordered : DependencyPlan.ordered place round4After round5Physical = true := by decide +kernel

end Midnight.SHA256.WitnessDependencyAcceptance
