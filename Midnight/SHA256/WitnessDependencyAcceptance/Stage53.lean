import Midnight.Math.Witness.DependencySnapshotSyntax
import Midnight.SHA256.WitnessDependencyAcceptanceData
import Midnight.SHA256.WitnessDependencyAcceptance.Stage52

namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

def expand49Physical : List (DependencyPlan.PlanAssignment F) := RegionPlan.lower place expand49Plan 172
theorem expand49Count : expand49Plan.length = 3 := by decide +kernel
dependency_snapshot_step expand49 tree7648 from expand48After
theorem expand49Ordered : DependencyPlan.ordered place expand48After expand49Physical = true := by decide +kernel

end Midnight.SHA256.WitnessDependencyAcceptance
