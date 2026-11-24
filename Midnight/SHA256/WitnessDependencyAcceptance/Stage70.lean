import Midnight.Math.Witness.DependencySnapshotSyntax
import Midnight.SHA256.WitnessDependencyAcceptanceData
import Midnight.SHA256.WitnessDependencyAcceptance.Stage69

namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

def round2Physical : List (DependencyPlan.PlanAssignment F) := RegionPlan.lower place round2Plan 232
theorem round2Count : round2Plan.length = 7 := by decide +kernel
dependency_snapshot_step round2 tree11293 from round1After
theorem round2Ordered : DependencyPlan.ordered place round1After round2Physical = true := by decide +kernel

end Midnight.SHA256.WitnessDependencyAcceptance
