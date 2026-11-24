import Midnight.Math.Witness.DependencySnapshotSyntax
import Midnight.SHA256.WitnessDependencyAcceptanceData
import Midnight.SHA256.WitnessDependencyAcceptance.Stage77

namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

def round10Physical : List (DependencyPlan.PlanAssignment F) := RegionPlan.lower place round10Plan 288
theorem round10Count : round10Plan.length = 7 := by decide +kernel
dependency_snapshot_step round10 tree13593 from round9After
theorem round10Ordered : DependencyPlan.ordered place round9After round10Physical = true := by decide +kernel

end Midnight.SHA256.WitnessDependencyAcceptance
