import Midnight.Math.Witness.DependencySnapshotSyntax
import Midnight.SHA256.WitnessDependencyAcceptanceData
import Midnight.SHA256.WitnessDependencyAcceptance.Stage103

namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

def round36Physical : List (DependencyPlan.PlanAssignment F) := RegionPlan.lower place round36Plan 470
theorem round36Count : round36Plan.length = 7 := by decide +kernel
def round36Part0Physical : List (DependencyPlan.PlanAssignment F) := (round36Physical.drop 0).take 64
dependency_snapshot_step round36Part0 tree24706 from round35After
theorem round36Part0Ordered : DependencyPlan.ordered place round35After round36Part0Physical = true := by decide +kernel
def round36Part1Physical : List (DependencyPlan.PlanAssignment F) := (round36Physical.drop 64).take 64
dependency_snapshot_step round36Part1 tree24907 from round36Part0After
theorem round36Part1Ordered : DependencyPlan.ordered place round36Part0After round36Part1Physical = true := by decide +kernel
def round36Part2Physical : List (DependencyPlan.PlanAssignment F) := (round36Physical.drop 128).take 64
dependency_snapshot_step round36Part2 tree25084 from round36Part1After
theorem round36Part2Ordered : DependencyPlan.ordered place round36Part1After round36Part2Physical = true := by decide +kernel
theorem round36Split : round36Physical = round36Part0Physical ++ round36Part1Physical ++ round36Part2Physical := by rfl
attribute [local irreducible] round35After round36Part0Physical round36Part0After round36Part1Physical round36Part1After round36Part2Physical round36Part2After
theorem round36PartsAfter_eq : DependencyPlan.advance round35After round36Physical = round36Part2After := by
  rw [round36Split]
  simp only [DependencyPlan.advance_append, round36Part0After_eq, round36Part1After_eq, round36Part2After_eq]
def round36After : DependencySnapshot.State := round36Part2After
theorem round36After_eq : DependencyPlan.advance round35After round36Physical = round36After := round36PartsAfter_eq
theorem round36Ordered : DependencyPlan.ordered place round35After round36Physical = true := by
  rw [round36Split]
  simp only [DependencyPlan.ordered_append, DependencyPlan.advance_append, round36Part0After_eq, round36Part1After_eq, round36Part0Ordered, round36Part1Ordered, round36Part2Ordered, Bool.true_and]

end Midnight.SHA256.WitnessDependencyAcceptance
