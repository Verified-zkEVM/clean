import Midnight.Math.Witness.DependencySnapshotSyntax
import Midnight.SHA256.WitnessDependencyAcceptanceData
import Midnight.SHA256.WitnessDependencyAcceptance.Stage118

namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

def round51Physical : List (DependencyPlan.PlanAssignment F) := RegionPlan.lower place round51Plan 575
theorem round51Count : round51Plan.length = 7 := by decide +kernel
def round51Part0Physical : List (DependencyPlan.PlanAssignment F) := (round51Physical.drop 0).take 64
dependency_snapshot_step round51Part0 tree33221 from round50After
theorem round51Part0Ordered : DependencyPlan.ordered place round50After round51Part0Physical = true := by decide +kernel
def round51Part1Physical : List (DependencyPlan.PlanAssignment F) := (round51Physical.drop 64).take 64
dependency_snapshot_step round51Part1 tree33408 from round51Part0After
theorem round51Part1Ordered : DependencyPlan.ordered place round51Part0After round51Part1Physical = true := by decide +kernel
def round51Part2Physical : List (DependencyPlan.PlanAssignment F) := (round51Physical.drop 128).take 64
dependency_snapshot_step round51Part2 tree33583 from round51Part1After
theorem round51Part2Ordered : DependencyPlan.ordered place round51Part1After round51Part2Physical = true := by decide +kernel
theorem round51Split : round51Physical = round51Part0Physical ++ round51Part1Physical ++ round51Part2Physical := by rfl
attribute [local irreducible] round50After round51Part0Physical round51Part0After round51Part1Physical round51Part1After round51Part2Physical round51Part2After
theorem round51PartsAfter_eq : DependencyPlan.advance round50After round51Physical = round51Part2After := by
  rw [round51Split]
  simp only [DependencyPlan.advance_append, round51Part0After_eq, round51Part1After_eq, round51Part2After_eq]
def round51After : DependencySnapshot.State := round51Part2After
theorem round51After_eq : DependencyPlan.advance round50After round51Physical = round51After := round51PartsAfter_eq
theorem round51Ordered : DependencyPlan.ordered place round50After round51Physical = true := by
  rw [round51Split]
  simp only [DependencyPlan.ordered_append, DependencyPlan.advance_append, round51Part0After_eq, round51Part1After_eq, round51Part0Ordered, round51Part1Ordered, round51Part2Ordered, Bool.true_and]

end Midnight.SHA256.WitnessDependencyAcceptance
