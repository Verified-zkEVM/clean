import Midnight.Math.Witness.DependencySnapshotSyntax
import Midnight.SHA256.WitnessDependencyAcceptanceData
import Midnight.SHA256.WitnessDependencyAcceptance.Stage82

namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

def round15Physical : List (DependencyPlan.PlanAssignment F) := RegionPlan.lower place round15Plan 323
theorem round15Count : round15Plan.length = 7 := by decide +kernel
dependency_snapshot_step round15 tree15062 from round14After
theorem round15Ordered : DependencyPlan.ordered place round14After round15Physical = true := by decide +kernel

end Midnight.SHA256.WitnessDependencyAcceptance
