import Midnight.Math.Witness.DependencySnapshotSyntax
import Midnight.SHA256.WitnessDependencyAcceptanceData
import Midnight.SHA256.WitnessDependencyAcceptance.Stage79

namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

def round12Physical : List (DependencyPlan.PlanAssignment F) := RegionPlan.lower place round12Plan 302
theorem round12Count : round12Plan.length = 7 := by decide +kernel
dependency_snapshot_step round12 tree14182 from round11After
theorem round12Ordered : DependencyPlan.ordered place round11After round12Physical = true := by decide +kernel

end Midnight.SHA256.WitnessDependencyAcceptance
