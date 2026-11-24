import Midnight.Math.Witness.DependencySnapshotSyntax
import Midnight.SHA256.WitnessDependencyAcceptanceData
import Midnight.SHA256.WitnessDependencyAcceptance.Stage27

namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

def expand24Physical : List (DependencyPlan.PlanAssignment F) := RegionPlan.lower place expand24Plan 97
theorem expand24Count : expand24Plan.length = 3 := by decide +kernel
dependency_snapshot_step expand24 tree3026 from expand23After
theorem expand24Ordered : DependencyPlan.ordered place expand23After expand24Physical = true := by decide +kernel

end Midnight.SHA256.WitnessDependencyAcceptance
