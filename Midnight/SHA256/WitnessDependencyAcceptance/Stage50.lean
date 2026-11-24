import Midnight.Math.Witness.DependencySnapshotSyntax
import Midnight.SHA256.WitnessDependencyAcceptanceData
import Midnight.SHA256.WitnessDependencyAcceptance.Stage49

namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

def expand46Physical : List (DependencyPlan.PlanAssignment F) := RegionPlan.lower place expand46Plan 163
theorem expand46Count : expand46Plan.length = 3 := by decide +kernel
dependency_snapshot_step expand46 tree7076 from expand45After
theorem expand46Ordered : DependencyPlan.ordered place expand45After expand46Physical = true := by decide +kernel

end Midnight.SHA256.WitnessDependencyAcceptance
