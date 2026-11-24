import Midnight.Math.Witness.DependencySnapshotSyntax
import Midnight.SHA256.WitnessDependencyAcceptanceData
import Midnight.SHA256.WitnessDependencyAcceptance.Stage33

namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

def expand30Physical : List (DependencyPlan.PlanAssignment F) := RegionPlan.lower place expand30Plan 115
theorem expand30Count : expand30Plan.length = 3 := by decide +kernel
dependency_snapshot_step expand30 tree4095 from expand29After
theorem expand30Ordered : DependencyPlan.ordered place expand29After expand30Physical = true := by decide +kernel

end Midnight.SHA256.WitnessDependencyAcceptance
