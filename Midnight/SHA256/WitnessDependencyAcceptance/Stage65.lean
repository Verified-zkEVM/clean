import Midnight.Math.Witness.DependencySnapshotSyntax
import Midnight.SHA256.WitnessDependencyAcceptanceData
import Midnight.SHA256.WitnessDependencyAcceptance.Stage64

namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

def expand61Physical : List (DependencyPlan.PlanAssignment F) := RegionPlan.lower place expand61Plan 208
theorem expand61Count : expand61Plan.length = 3 := by decide +kernel
dependency_snapshot_step expand61 tree10022 from expand60After
theorem expand61Ordered : DependencyPlan.ordered place expand60After expand61Physical = true := by decide +kernel

end Midnight.SHA256.WitnessDependencyAcceptance
