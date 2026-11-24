import Midnight.Math.Witness.DependencySnapshotSyntax
import Midnight.SHA256.WitnessDependencyAcceptanceData
import Midnight.SHA256.WitnessDependencyAcceptance.Stage40

namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

def expand37Physical : List (DependencyPlan.PlanAssignment F) := RegionPlan.lower place expand37Plan 136
theorem expand37Count : expand37Plan.length = 3 := by decide +kernel
dependency_snapshot_step expand37 tree5383 from expand36After
theorem expand37Ordered : DependencyPlan.ordered place expand36After expand37Physical = true := by decide +kernel

end Midnight.SHA256.WitnessDependencyAcceptance
