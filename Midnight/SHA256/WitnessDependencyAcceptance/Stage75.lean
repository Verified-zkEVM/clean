import Midnight.Math.Witness.DependencySnapshotSyntax
import Midnight.SHA256.WitnessDependencyAcceptanceData
import Midnight.SHA256.WitnessDependencyAcceptance.Stage74

namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

def round7Physical : List (DependencyPlan.PlanAssignment F) := RegionPlan.lower place round7Plan 267
theorem round7Count : round7Plan.length = 7 := by decide +kernel
dependency_snapshot_step round7 tree12729 from round6After
theorem round7Ordered : DependencyPlan.ordered place round6After round7Physical = true := by decide +kernel

end Midnight.SHA256.WitnessDependencyAcceptance
