import Midnight.Math.Witness.DependencySnapshotSyntax
import Midnight.SHA256.WitnessDependencyAcceptanceData
import Midnight.SHA256.WitnessDependencyAcceptance.Stage50

namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

def expand47Physical : List (DependencyPlan.PlanAssignment F) := RegionPlan.lower place expand47Plan 166
theorem expand47Count : expand47Plan.length = 3 := by decide +kernel
dependency_snapshot_step expand47 tree7276 from expand46After
theorem expand47Ordered : DependencyPlan.ordered place expand46After expand47Physical = true := by decide +kernel

end Midnight.SHA256.WitnessDependencyAcceptance
