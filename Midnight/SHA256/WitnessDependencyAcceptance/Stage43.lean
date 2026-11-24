import Midnight.Math.Witness.DependencySnapshotSyntax
import Midnight.SHA256.WitnessDependencyAcceptanceData
import Midnight.SHA256.WitnessDependencyAcceptance.Stage42

namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

def expand39Physical : List (DependencyPlan.PlanAssignment F) := RegionPlan.lower place expand39Plan 142
theorem expand39Count : expand39Plan.length = 3 := by decide +kernel
dependency_snapshot_step expand39 tree5763 from expand38After
theorem expand39Ordered : DependencyPlan.ordered place expand38After expand39Physical = true := by decide +kernel

end Midnight.SHA256.WitnessDependencyAcceptance
