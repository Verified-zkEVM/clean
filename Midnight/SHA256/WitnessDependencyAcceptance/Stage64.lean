import Midnight.Math.Witness.DependencySnapshotSyntax
import Midnight.SHA256.WitnessDependencyAcceptanceData
import Midnight.SHA256.WitnessDependencyAcceptance.Stage63

namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

def expand60Physical : List (DependencyPlan.PlanAssignment F) := RegionPlan.lower place expand60Plan 205
theorem expand60Count : expand60Plan.length = 3 := by decide +kernel
dependency_snapshot_step expand60 tree9815 from expand59After
theorem expand60Ordered : DependencyPlan.ordered place expand59After expand60Physical = true := by decide +kernel

end Midnight.SHA256.WitnessDependencyAcceptance
