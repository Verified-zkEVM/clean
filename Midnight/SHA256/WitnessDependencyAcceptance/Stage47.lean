import Midnight.Math.Witness.DependencySnapshotSyntax
import Midnight.SHA256.WitnessDependencyAcceptanceData
import Midnight.SHA256.WitnessDependencyAcceptance.Stage46

namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

def expand43Physical : List (DependencyPlan.PlanAssignment F) := RegionPlan.lower place expand43Plan 154
theorem expand43Count : expand43Plan.length = 3 := by decide +kernel
dependency_snapshot_step expand43 tree6497 from expand42After
theorem expand43Ordered : DependencyPlan.ordered place expand42After expand43Physical = true := by decide +kernel

end Midnight.SHA256.WitnessDependencyAcceptance
