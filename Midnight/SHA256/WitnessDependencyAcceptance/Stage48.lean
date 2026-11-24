import Midnight.Math.Witness.DependencySnapshotSyntax
import Midnight.SHA256.WitnessDependencyAcceptanceData
import Midnight.SHA256.WitnessDependencyAcceptance.Stage47

namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

def expand44Physical : List (DependencyPlan.PlanAssignment F) := RegionPlan.lower place expand44Plan 157
theorem expand44Count : expand44Plan.length = 3 := by decide +kernel
dependency_snapshot_step expand44 tree6682 from expand43After
theorem expand44Ordered : DependencyPlan.ordered place expand43After expand44Physical = true := by decide +kernel

end Midnight.SHA256.WitnessDependencyAcceptance
