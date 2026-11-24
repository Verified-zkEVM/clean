import Midnight.Math.Witness.DependencySnapshotSyntax
import Midnight.SHA256.WitnessDependencyAcceptanceData
import Midnight.SHA256.WitnessDependencyAcceptance.Stage61

namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

def expand58Physical : List (DependencyPlan.PlanAssignment F) := RegionPlan.lower place expand58Plan 199
theorem expand58Count : expand58Plan.length = 3 := by decide +kernel
dependency_snapshot_step expand58 tree9415 from expand57After
theorem expand58Ordered : DependencyPlan.ordered place expand57After expand58Physical = true := by decide +kernel

end Midnight.SHA256.WitnessDependencyAcceptance
