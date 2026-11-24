import Midnight.Math.Witness.DependencySnapshotSyntax
import Midnight.SHA256.WitnessDependencyAcceptanceData
import Midnight.SHA256.WitnessDependencyAcceptance.Stage57

namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

def expand54Physical : List (DependencyPlan.PlanAssignment F) := RegionPlan.lower place expand54Plan 187
theorem expand54Count : expand54Plan.length = 3 := by decide +kernel
dependency_snapshot_step expand54 tree8634 from expand53After
theorem expand54Ordered : DependencyPlan.ordered place expand53After expand54Physical = true := by decide +kernel

end Midnight.SHA256.WitnessDependencyAcceptance
