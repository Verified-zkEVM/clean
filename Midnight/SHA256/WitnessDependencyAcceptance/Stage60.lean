import Midnight.Math.Witness.DependencySnapshotSyntax
import Midnight.SHA256.WitnessDependencyAcceptanceData
import Midnight.SHA256.WitnessDependencyAcceptance.Stage59

namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

def expand56Physical : List (DependencyPlan.PlanAssignment F) := RegionPlan.lower place expand56Plan 193
theorem expand56Count : expand56Plan.length = 3 := by decide +kernel
dependency_snapshot_step expand56 tree9022 from expand55After
theorem expand56Ordered : DependencyPlan.ordered place expand55After expand56Physical = true := by decide +kernel

end Midnight.SHA256.WitnessDependencyAcceptance
