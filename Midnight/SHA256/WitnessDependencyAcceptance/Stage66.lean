import Midnight.Math.Witness.DependencySnapshotSyntax
import Midnight.SHA256.WitnessDependencyAcceptanceData
import Midnight.SHA256.WitnessDependencyAcceptance.Stage65

namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

def expand62Physical : List (DependencyPlan.PlanAssignment F) := RegionPlan.lower place expand62Plan 211
theorem expand62Count : expand62Plan.length = 3 := by decide +kernel
dependency_snapshot_step expand62 tree10229 from expand61After
theorem expand62Ordered : DependencyPlan.ordered place expand61After expand62Physical = true := by decide +kernel

end Midnight.SHA256.WitnessDependencyAcceptance
