import Midnight.Math.Witness.DependencySnapshotSyntax
import Midnight.SHA256.WitnessDependencyAcceptanceData
import Midnight.SHA256.WitnessDependencyAcceptance.Stage76

namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

def round9Physical : List (DependencyPlan.PlanAssignment F) := RegionPlan.lower place round9Plan 281
theorem round9Count : round9Plan.length = 7 := by decide +kernel
dependency_snapshot_step round9 tree13302 from round8After
theorem round9Ordered : DependencyPlan.ordered place round8After round9Physical = true := by decide +kernel

end Midnight.SHA256.WitnessDependencyAcceptance
