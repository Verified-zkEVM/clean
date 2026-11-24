import Midnight.Math.Witness.DependencySnapshotSyntax
import Midnight.SHA256.WitnessDependencyAcceptanceData
import Midnight.SHA256.WitnessDependencyAcceptance.Stage87

namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

def round20Physical : List (DependencyPlan.PlanAssignment F) := RegionPlan.lower place round20Plan 358
theorem round20Count : round20Plan.length = 7 := by decide +kernel
dependency_snapshot_step round20 tree16528 from round19After
theorem round20Ordered : DependencyPlan.ordered place round19After round20Physical = true := by decide +kernel

end Midnight.SHA256.WitnessDependencyAcceptance
