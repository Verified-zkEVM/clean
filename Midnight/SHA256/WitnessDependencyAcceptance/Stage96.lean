import Midnight.Math.Witness.DependencySnapshotSyntax
import Midnight.SHA256.WitnessDependencyAcceptanceData
import Midnight.SHA256.WitnessDependencyAcceptance.Stage95

namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

def round28Physical : List (DependencyPlan.PlanAssignment F) := RegionPlan.lower place round28Plan 414
theorem round28Count : round28Plan.length = 7 := by decide +kernel
def round28Part0Physical : List (DependencyPlan.PlanAssignment F) := (round28Physical.drop 0).take 64
dependency_snapshot_step round28Part0 tree20316 from round27After
theorem round28Part0Ordered : DependencyPlan.ordered place round27After round28Part0Physical = true := by decide +kernel
def round28Part1Physical : List (DependencyPlan.PlanAssignment F) := (round28Physical.drop 64).take 64
dependency_snapshot_step round28Part1 tree20506 from round28Part0After
theorem round28Part1Ordered : DependencyPlan.ordered place round28Part0After round28Part1Physical = true := by decide +kernel
def round28Part2Physical : List (DependencyPlan.PlanAssignment F) := (round28Physical.drop 128).take 64
dependency_snapshot_step round28Part2 tree20675 from round28Part1After
theorem round28Part2Ordered : DependencyPlan.ordered place round28Part1After round28Part2Physical = true := by decide +kernel
theorem round28Split : round28Physical = round28Part0Physical ++ round28Part1Physical ++ round28Part2Physical := by rfl
attribute [local irreducible] round27After round28Part0Physical round28Part0After round28Part1Physical round28Part1After round28Part2Physical round28Part2After
theorem round28PartsAfter_eq : DependencyPlan.advance round27After round28Physical = round28Part2After := by
  rw [round28Split]
  simp only [DependencyPlan.advance_append, round28Part0After_eq, round28Part1After_eq, round28Part2After_eq]
def round28After : DependencySnapshot.State := round28Part2After
theorem round28After_eq : DependencyPlan.advance round27After round28Physical = round28After := round28PartsAfter_eq
theorem round28Ordered : DependencyPlan.ordered place round27After round28Physical = true := by
  rw [round28Split]
  simp only [DependencyPlan.ordered_append, DependencyPlan.advance_append, round28Part0After_eq, round28Part1After_eq, round28Part0Ordered, round28Part1Ordered, round28Part2Ordered, Bool.true_and]

end Midnight.SHA256.WitnessDependencyAcceptance
