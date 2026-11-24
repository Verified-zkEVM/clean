import Midnight.Math.Witness.DependencySnapshotSyntax
import Midnight.SHA256.WitnessDependencyAcceptanceData
import Midnight.SHA256.WitnessDependencyAcceptance.Stage122

namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

def round55Physical : List (DependencyPlan.PlanAssignment F) := RegionPlan.lower place round55Plan 603
theorem round55Count : round55Plan.length = 7 := by decide +kernel
def round55Part0Physical : List (DependencyPlan.PlanAssignment F) := (round55Physical.drop 0).take 64
dependency_snapshot_step round55Part0 tree35486 from round54After
theorem round55Part0Ordered : DependencyPlan.ordered place round54After round55Part0Physical = true := by decide +kernel
def round55Part1Physical : List (DependencyPlan.PlanAssignment F) := (round55Physical.drop 64).take 64
dependency_snapshot_step round55Part1 tree35685 from round55Part0After
theorem round55Part1Ordered : DependencyPlan.ordered place round55Part0After round55Part1Physical = true := by decide +kernel
def round55Part2Physical : List (DependencyPlan.PlanAssignment F) := (round55Physical.drop 128).take 64
dependency_snapshot_step round55Part2 tree35862 from round55Part1After
theorem round55Part2Ordered : DependencyPlan.ordered place round55Part1After round55Part2Physical = true := by decide +kernel
theorem round55Split : round55Physical = round55Part0Physical ++ round55Part1Physical ++ round55Part2Physical := by rfl
attribute [local irreducible] round54After round55Part0Physical round55Part0After round55Part1Physical round55Part1After round55Part2Physical round55Part2After
theorem round55PartsAfter_eq : DependencyPlan.advance round54After round55Physical = round55Part2After := by
  rw [round55Split]
  simp only [DependencyPlan.advance_append, round55Part0After_eq, round55Part1After_eq, round55Part2After_eq]
def round55After : DependencySnapshot.State := round55Part2After
theorem round55After_eq : DependencyPlan.advance round54After round55Physical = round55After := round55PartsAfter_eq
theorem round55Ordered : DependencyPlan.ordered place round54After round55Physical = true := by
  rw [round55Split]
  simp only [DependencyPlan.ordered_append, DependencyPlan.advance_append, round55Part0After_eq, round55Part1After_eq, round55Part0Ordered, round55Part1Ordered, round55Part2Ordered, Bool.true_and]

end Midnight.SHA256.WitnessDependencyAcceptance
