import Midnight.Math.Witness.DependencySnapshotSyntax
import Midnight.SHA256.WitnessDependencyAcceptanceData
import Midnight.SHA256.WitnessDependencyAcceptance.Stage36

namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

def expand33Physical : List (DependencyPlan.PlanAssignment F) := RegionPlan.lower place expand33Plan 124
theorem expand33Count : expand33Plan.length = 3 := by decide +kernel
dependency_snapshot_step expand33 tree4634 from expand32After
theorem expand33Ordered : DependencyPlan.ordered place expand32After expand33Physical = true := by decide +kernel

end Midnight.SHA256.WitnessDependencyAcceptance
