import Midnight.Math.Witness.DependencySnapshotSyntax
import Midnight.SHA256.WitnessDependencyAcceptanceData
import Midnight.SHA256.WitnessDependencyAcceptance.Stage78

namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

def round11Physical : List (DependencyPlan.PlanAssignment F) := RegionPlan.lower place round11Plan 295
theorem round11Count : round11Plan.length = 7 := by decide +kernel
dependency_snapshot_step round11 tree13887 from round10After
theorem round11Ordered : DependencyPlan.ordered place round10After round11Physical = true := by decide +kernel

end Midnight.SHA256.WitnessDependencyAcceptance
