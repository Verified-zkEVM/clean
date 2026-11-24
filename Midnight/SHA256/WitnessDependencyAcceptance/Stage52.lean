import Midnight.Math.Witness.DependencySnapshotSyntax
import Midnight.SHA256.WitnessDependencyAcceptanceData
import Midnight.SHA256.WitnessDependencyAcceptance.Stage51

namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

def expand48Physical : List (DependencyPlan.PlanAssignment F) := RegionPlan.lower place expand48Plan 169
theorem expand48Count : expand48Plan.length = 3 := by decide +kernel
dependency_snapshot_step expand48 tree7457 from expand47After
theorem expand48Ordered : DependencyPlan.ordered place expand47After expand48Physical = true := by decide +kernel

end Midnight.SHA256.WitnessDependencyAcceptance
