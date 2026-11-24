import Midnight.Math.Witness.DependencySnapshotSyntax
import Midnight.SHA256.WitnessDependencyAcceptanceData
import Midnight.SHA256.WitnessDependencyAcceptance.Stage73

namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

def round6Physical : List (DependencyPlan.PlanAssignment F) := RegionPlan.lower place round6Plan 260
theorem round6Count : round6Plan.length = 7 := by decide +kernel
dependency_snapshot_step round6 tree12439 from round5After
theorem round6Ordered : DependencyPlan.ordered place round5After round6Physical = true := by decide +kernel

end Midnight.SHA256.WitnessDependencyAcceptance
