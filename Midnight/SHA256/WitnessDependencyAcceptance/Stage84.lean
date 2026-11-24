import Midnight.Math.Witness.DependencySnapshotSyntax
import Midnight.SHA256.WitnessDependencyAcceptanceData
import Midnight.SHA256.WitnessDependencyAcceptance.Stage83

namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

def round16Physical : List (DependencyPlan.PlanAssignment F) := RegionPlan.lower place round16Plan 330
theorem round16Count : round16Plan.length = 7 := by decide +kernel
dependency_snapshot_step round16 tree15345 from round15After
theorem round16Ordered : DependencyPlan.ordered place round15After round16Physical = true := by decide +kernel

end Midnight.SHA256.WitnessDependencyAcceptance
