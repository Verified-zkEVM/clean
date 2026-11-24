import Midnight.Math.Witness.DependencySnapshotSyntax
import Midnight.SHA256.WitnessDependencyAcceptanceData
import Midnight.SHA256.WitnessDependencyAcceptance.Stage123

namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

def round56Physical : List (DependencyPlan.PlanAssignment F) := RegionPlan.lower place round56Plan 610
theorem round56Count : round56Plan.length = 7 := by decide +kernel
def round56Part0Physical : List (DependencyPlan.PlanAssignment F) := (round56Physical.drop 0).take 64
dependency_snapshot_step round56Part0 tree36051 from round55After
theorem round56Part0Ordered : DependencyPlan.ordered place round55After round56Part0Physical = true := by decide +kernel
def round56Part1Physical : List (DependencyPlan.PlanAssignment F) := (round56Physical.drop 64).take 64
dependency_snapshot_step round56Part1 tree36243 from round56Part0After
theorem round56Part1Ordered : DependencyPlan.ordered place round56Part0After round56Part1Physical = true := by decide +kernel
def round56Part2Physical : List (DependencyPlan.PlanAssignment F) := (round56Physical.drop 128).take 64
dependency_snapshot_step round56Part2 tree36416 from round56Part1After
theorem round56Part2Ordered : DependencyPlan.ordered place round56Part1After round56Part2Physical = true := by decide +kernel
theorem round56Split : round56Physical = round56Part0Physical ++ round56Part1Physical ++ round56Part2Physical := by rfl
attribute [local irreducible] round55After round56Part0Physical round56Part0After round56Part1Physical round56Part1After round56Part2Physical round56Part2After
theorem round56PartsAfter_eq : DependencyPlan.advance round55After round56Physical = round56Part2After := by
  rw [round56Split]
  simp only [DependencyPlan.advance_append, round56Part0After_eq, round56Part1After_eq, round56Part2After_eq]
def round56After : DependencySnapshot.State := round56Part2After
theorem round56After_eq : DependencyPlan.advance round55After round56Physical = round56After := round56PartsAfter_eq
theorem round56Ordered : DependencyPlan.ordered place round55After round56Physical = true := by
  rw [round56Split]
  simp only [DependencyPlan.ordered_append, DependencyPlan.advance_append, round56Part0After_eq, round56Part1After_eq, round56Part0Ordered, round56Part1Ordered, round56Part2Ordered, Bool.true_and]

end Midnight.SHA256.WitnessDependencyAcceptance
