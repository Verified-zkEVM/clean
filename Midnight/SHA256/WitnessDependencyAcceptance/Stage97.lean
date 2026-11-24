import Midnight.Math.Witness.DependencySnapshotSyntax
import Midnight.SHA256.WitnessDependencyAcceptanceData
import Midnight.SHA256.WitnessDependencyAcceptance.Stage96

namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

def round29Physical : List (DependencyPlan.PlanAssignment F) := RegionPlan.lower place round29Plan 421
theorem round29Count : round29Plan.length = 7 := by decide +kernel
def round29Part0Physical : List (DependencyPlan.PlanAssignment F) := (round29Physical.drop 0).take 64
dependency_snapshot_step round29Part0 tree20859 from round28After
theorem round29Part0Ordered : DependencyPlan.ordered place round28After round29Part0Physical = true := by decide +kernel
def round29Part1Physical : List (DependencyPlan.PlanAssignment F) := (round29Physical.drop 64).take 64
dependency_snapshot_step round29Part1 tree21039 from round29Part0After
theorem round29Part1Ordered : DependencyPlan.ordered place round29Part0After round29Part1Physical = true := by decide +kernel
def round29Part2Physical : List (DependencyPlan.PlanAssignment F) := (round29Physical.drop 128).take 64
dependency_snapshot_step round29Part2 tree21202 from round29Part1After
theorem round29Part2Ordered : DependencyPlan.ordered place round29Part1After round29Part2Physical = true := by decide +kernel
theorem round29Split : round29Physical = round29Part0Physical ++ round29Part1Physical ++ round29Part2Physical := by rfl
attribute [local irreducible] round28After round29Part0Physical round29Part0After round29Part1Physical round29Part1After round29Part2Physical round29Part2After
theorem round29PartsAfter_eq : DependencyPlan.advance round28After round29Physical = round29Part2After := by
  rw [round29Split]
  simp only [DependencyPlan.advance_append, round29Part0After_eq, round29Part1After_eq, round29Part2After_eq]
def round29After : DependencySnapshot.State := round29Part2After
theorem round29After_eq : DependencyPlan.advance round28After round29Physical = round29After := round29PartsAfter_eq
theorem round29Ordered : DependencyPlan.ordered place round28After round29Physical = true := by
  rw [round29Split]
  simp only [DependencyPlan.ordered_append, DependencyPlan.advance_append, round29Part0After_eq, round29Part1After_eq, round29Part0Ordered, round29Part1Ordered, round29Part2Ordered, Bool.true_and]

end Midnight.SHA256.WitnessDependencyAcceptance
