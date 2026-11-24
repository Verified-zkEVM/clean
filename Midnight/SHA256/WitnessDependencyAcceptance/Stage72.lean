import Midnight.Math.Witness.DependencySnapshotSyntax
import Midnight.SHA256.WitnessDependencyAcceptanceData
import Midnight.SHA256.WitnessDependencyAcceptance.Stage71

namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

def round4Physical : List (DependencyPlan.PlanAssignment F) := RegionPlan.lower place round4Plan 246
theorem round4Count : round4Plan.length = 7 := by decide +kernel
dependency_snapshot_step round4 tree11860 from round3After
theorem round4Ordered : DependencyPlan.ordered place round3After round4Physical = true := by decide +kernel

end Midnight.SHA256.WitnessDependencyAcceptance
