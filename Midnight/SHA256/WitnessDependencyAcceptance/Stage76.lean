import Midnight.Math.Witness.DependencySnapshotSyntax
import Midnight.SHA256.WitnessDependencyAcceptanceData
import Midnight.SHA256.WitnessDependencyAcceptance.Stage75

namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

def round8Physical : List (DependencyPlan.PlanAssignment F) := RegionPlan.lower place round8Plan 274
theorem round8Count : round8Plan.length = 7 := by decide +kernel
dependency_snapshot_step round8 tree13007 from round7After
theorem round8Ordered : DependencyPlan.ordered place round7After round8Physical = true := by decide +kernel

end Midnight.SHA256.WitnessDependencyAcceptance
