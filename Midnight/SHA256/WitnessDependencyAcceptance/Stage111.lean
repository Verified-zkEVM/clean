import Midnight.Math.Witness.DependencySnapshotSyntax
import Midnight.SHA256.WitnessDependencyAcceptanceData
import Midnight.SHA256.WitnessDependencyAcceptance.Stage110

namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

def round43Physical : List (DependencyPlan.PlanAssignment F) := RegionPlan.lower place round43Plan 519
theorem round43Count : round43Plan.length = 7 := by decide +kernel
def round43Part0Physical : List (DependencyPlan.PlanAssignment F) := (round43Physical.drop 0).take 64
dependency_snapshot_step round43Part0 tree28660 from round42After
theorem round43Part0Ordered : DependencyPlan.ordered place round42After round43Part0Physical = true := by decide +kernel
def round43Part1Physical : List (DependencyPlan.PlanAssignment F) := (round43Physical.drop 64).take 64
dependency_snapshot_step round43Part1 tree28856 from round43Part0After
theorem round43Part1Ordered : DependencyPlan.ordered place round43Part0After round43Part1Physical = true := by decide +kernel
def round43Part2Physical : List (DependencyPlan.PlanAssignment F) := (round43Physical.drop 128).take 64
dependency_snapshot_step round43Part2 tree29038 from round43Part1After
theorem round43Part2Ordered : DependencyPlan.ordered place round43Part1After round43Part2Physical = true := by decide +kernel
theorem round43Split : round43Physical = round43Part0Physical ++ round43Part1Physical ++ round43Part2Physical := by rfl
attribute [local irreducible] round42After round43Part0Physical round43Part0After round43Part1Physical round43Part1After round43Part2Physical round43Part2After
theorem round43PartsAfter_eq : DependencyPlan.advance round42After round43Physical = round43Part2After := by
  rw [round43Split]
  simp only [DependencyPlan.advance_append, round43Part0After_eq, round43Part1After_eq, round43Part2After_eq]
def round43After : DependencySnapshot.State := round43Part2After
theorem round43After_eq : DependencyPlan.advance round42After round43Physical = round43After := round43PartsAfter_eq
theorem round43Ordered : DependencyPlan.ordered place round42After round43Physical = true := by
  rw [round43Split]
  simp only [DependencyPlan.ordered_append, DependencyPlan.advance_append, round43Part0After_eq, round43Part1After_eq, round43Part0Ordered, round43Part1Ordered, round43Part2Ordered, Bool.true_and]

end Midnight.SHA256.WitnessDependencyAcceptance
