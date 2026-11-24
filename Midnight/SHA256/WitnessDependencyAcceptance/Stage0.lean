import Midnight.Math.Witness.DependencySnapshotSyntax
import Midnight.SHA256.WitnessDependencyAcceptanceData

namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

def inputPhysical : List (DependencyPlan.PlanAssignment F) := RegionPlan.lower place inputPlan 0
theorem inputCount : inputPlan.length = 24 := by decide +kernel
dependency_snapshot_step input tree47 from (∅ : DependencySnapshot.State)
theorem inputOrdered : DependencyPlan.ordered place (∅ : DependencySnapshot.State) inputPhysical = true := by cbv

end Midnight.SHA256.WitnessDependencyAcceptance
