import Midnight.Math.Witness.DependencySnapshotSyntax
import Midnight.SHA256.WitnessDependencyAcceptanceData
import Midnight.SHA256.WitnessDependencyAcceptance.Stage138

namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

def serialize6Physical : List (DependencyPlan.PlanAssignment F) := RegionPlan.lower place serialize6Plan 686
theorem serialize6Count : serialize6Plan.length = 2 := by decide +kernel
dependency_snapshot_step serialize6 tree42323 from serialize5After
theorem serialize6Ordered : DependencyPlan.ordered place serialize5After serialize6Physical = true := by decide +kernel

end Midnight.SHA256.WitnessDependencyAcceptance
