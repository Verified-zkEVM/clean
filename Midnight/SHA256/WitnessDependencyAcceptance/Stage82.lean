import Midnight.Math.Witness.DependencySnapshotSyntax
import Midnight.SHA256.WitnessDependencyAcceptanceData
import Midnight.SHA256.WitnessDependencyAcceptance.Stage81

namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

def round14Physical : List (DependencyPlan.PlanAssignment F) := RegionPlan.lower place round14Plan 316
theorem round14Count : round14Plan.length = 7 := by decide +kernel
dependency_snapshot_step round14 tree14764 from round13After
theorem round14Ordered : DependencyPlan.ordered place round13After round14Physical = true := by decide +kernel

end Midnight.SHA256.WitnessDependencyAcceptance
