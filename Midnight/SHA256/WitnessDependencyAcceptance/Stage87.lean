import Midnight.Math.Witness.DependencySnapshotSyntax
import Midnight.SHA256.WitnessDependencyAcceptanceData
import Midnight.SHA256.WitnessDependencyAcceptance.Stage86

namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

def round19Physical : List (DependencyPlan.PlanAssignment F) := RegionPlan.lower place round19Plan 351
theorem round19Count : round19Plan.length = 7 := by decide +kernel
dependency_snapshot_step round19 tree16238 from round18After
theorem round19Ordered : DependencyPlan.ordered place round18After round19Physical = true := by decide +kernel

end Midnight.SHA256.WitnessDependencyAcceptance
