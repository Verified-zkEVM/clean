import Midnight.Math.Witness.DependencySnapshotSyntax
import Midnight.SHA256.WitnessDependencyAcceptanceData
import Midnight.SHA256.WitnessDependencyAcceptance.Stage60

namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

def expand57Physical : List (DependencyPlan.PlanAssignment F) := RegionPlan.lower place expand57Plan 196
theorem expand57Count : expand57Plan.length = 3 := by decide +kernel
dependency_snapshot_step expand57 tree9219 from expand56After
theorem expand57Ordered : DependencyPlan.ordered place expand56After expand57Physical = true := by decide +kernel

end Midnight.SHA256.WitnessDependencyAcceptance
