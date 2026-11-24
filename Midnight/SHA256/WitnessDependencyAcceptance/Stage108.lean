import Midnight.Math.Witness.DependencySnapshotSyntax
import Midnight.SHA256.WitnessDependencyAcceptanceData
import Midnight.SHA256.WitnessDependencyAcceptance.Stage107

namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

def round40Physical : List (DependencyPlan.PlanAssignment F) := RegionPlan.lower place round40Plan 498
theorem round40Count : round40Plan.length = 7 := by decide +kernel
def round40Part0Physical : List (DependencyPlan.PlanAssignment F) := (round40Physical.drop 0).take 64
dependency_snapshot_step round40Part0 tree26931 from round39After
theorem round40Part0Ordered : DependencyPlan.ordered place round39After round40Part0Physical = true := by decide +kernel
def round40Part1Physical : List (DependencyPlan.PlanAssignment F) := (round40Physical.drop 64).take 64
dependency_snapshot_step round40Part1 tree27125 from round40Part0After
theorem round40Part1Ordered : DependencyPlan.ordered place round40Part0After round40Part1Physical = true := by decide +kernel
def round40Part2Physical : List (DependencyPlan.PlanAssignment F) := (round40Physical.drop 128).take 64
dependency_snapshot_step round40Part2 tree27301 from round40Part1After
theorem round40Part2Ordered : DependencyPlan.ordered place round40Part1After round40Part2Physical = true := by decide +kernel
theorem round40Split : round40Physical = round40Part0Physical ++ round40Part1Physical ++ round40Part2Physical := by rfl
attribute [local irreducible] round39After round40Part0Physical round40Part0After round40Part1Physical round40Part1After round40Part2Physical round40Part2After
theorem round40PartsAfter_eq : DependencyPlan.advance round39After round40Physical = round40Part2After := by
  rw [round40Split]
  simp only [DependencyPlan.advance_append, round40Part0After_eq, round40Part1After_eq, round40Part2After_eq]
def round40After : DependencySnapshot.State := round40Part2After
theorem round40After_eq : DependencyPlan.advance round39After round40Physical = round40After := round40PartsAfter_eq
theorem round40Ordered : DependencyPlan.ordered place round39After round40Physical = true := by
  rw [round40Split]
  simp only [DependencyPlan.ordered_append, DependencyPlan.advance_append, round40Part0After_eq, round40Part1After_eq, round40Part0Ordered, round40Part1Ordered, round40Part2Ordered, Bool.true_and]

end Midnight.SHA256.WitnessDependencyAcceptance
