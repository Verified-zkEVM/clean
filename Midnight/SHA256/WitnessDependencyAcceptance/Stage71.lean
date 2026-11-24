import Midnight.Math.Witness.DependencySnapshotSyntax
import Midnight.SHA256.WitnessDependencyAcceptanceData
import Midnight.SHA256.WitnessDependencyAcceptance.Stage70

namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

def round3Physical : List (DependencyPlan.PlanAssignment F) := RegionPlan.lower place round3Plan 239
theorem round3Count : round3Plan.length = 7 := by decide +kernel
dependency_snapshot_step round3 tree11577 from round2After
theorem round3Ordered : DependencyPlan.ordered place round2After round3Physical = true := by decide +kernel

end Midnight.SHA256.WitnessDependencyAcceptance
