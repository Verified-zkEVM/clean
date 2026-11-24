import Midnight.Math.Witness.DependencySnapshotSyntax
import Midnight.SHA256.WitnessDependencyAcceptanceData
import Midnight.SHA256.WitnessDependencyAcceptance.Stage108

namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

def round41Physical : List (DependencyPlan.PlanAssignment F) := RegionPlan.lower place round41Plan 505
theorem round41Count : round41Plan.length = 7 := by decide +kernel
def round41Part0Physical : List (DependencyPlan.PlanAssignment F) := (round41Physical.drop 0).take 64
dependency_snapshot_step round41Part0 tree27504 from round40After
theorem round41Part0Ordered : DependencyPlan.ordered place round40After round41Part0Physical = true := by decide +kernel
def round41Part1Physical : List (DependencyPlan.PlanAssignment F) := (round41Physical.drop 64).take 64
dependency_snapshot_step round41Part1 tree27699 from round41Part0After
theorem round41Part1Ordered : DependencyPlan.ordered place round41Part0After round41Part1Physical = true := by decide +kernel
def round41Part2Physical : List (DependencyPlan.PlanAssignment F) := (round41Physical.drop 128).take 64
dependency_snapshot_step round41Part2 tree27877 from round41Part1After
theorem round41Part2Ordered : DependencyPlan.ordered place round41Part1After round41Part2Physical = true := by decide +kernel
theorem round41Split : round41Physical = round41Part0Physical ++ round41Part1Physical ++ round41Part2Physical := by rfl
attribute [local irreducible] round40After round41Part0Physical round41Part0After round41Part1Physical round41Part1After round41Part2Physical round41Part2After
theorem round41PartsAfter_eq : DependencyPlan.advance round40After round41Physical = round41Part2After := by
  rw [round41Split]
  simp only [DependencyPlan.advance_append, round41Part0After_eq, round41Part1After_eq, round41Part2After_eq]
def round41After : DependencySnapshot.State := round41Part2After
theorem round41After_eq : DependencyPlan.advance round40After round41Physical = round41After := round41PartsAfter_eq
theorem round41Ordered : DependencyPlan.ordered place round40After round41Physical = true := by
  rw [round41Split]
  simp only [DependencyPlan.ordered_append, DependencyPlan.advance_append, round41Part0After_eq, round41Part1After_eq, round41Part0Ordered, round41Part1Ordered, round41Part2Ordered, Bool.true_and]

end Midnight.SHA256.WitnessDependencyAcceptance
