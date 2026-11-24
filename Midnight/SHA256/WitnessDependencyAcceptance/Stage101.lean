import Midnight.Math.Witness.DependencySnapshotSyntax
import Midnight.SHA256.WitnessDependencyAcceptanceData
import Midnight.SHA256.WitnessDependencyAcceptance.Stage100

namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

def round33Physical : List (DependencyPlan.PlanAssignment F) := RegionPlan.lower place round33Plan 449
theorem round33Count : round33Plan.length = 7 := by decide +kernel
def round33Part0Physical : List (DependencyPlan.PlanAssignment F) := (round33Physical.drop 0).take 64
dependency_snapshot_step round33Part0 tree23041 from round32After
theorem round33Part0Ordered : DependencyPlan.ordered place round32After round33Part0Physical = true := by decide +kernel
def round33Part1Physical : List (DependencyPlan.PlanAssignment F) := (round33Physical.drop 64).take 64
dependency_snapshot_step round33Part1 tree23232 from round33Part0After
theorem round33Part1Ordered : DependencyPlan.ordered place round33Part0After round33Part1Physical = true := by decide +kernel
def round33Part2Physical : List (DependencyPlan.PlanAssignment F) := (round33Physical.drop 128).take 64
dependency_snapshot_step round33Part2 tree23401 from round33Part1After
theorem round33Part2Ordered : DependencyPlan.ordered place round33Part1After round33Part2Physical = true := by decide +kernel
theorem round33Split : round33Physical = round33Part0Physical ++ round33Part1Physical ++ round33Part2Physical := by rfl
attribute [local irreducible] round32After round33Part0Physical round33Part0After round33Part1Physical round33Part1After round33Part2Physical round33Part2After
theorem round33PartsAfter_eq : DependencyPlan.advance round32After round33Physical = round33Part2After := by
  rw [round33Split]
  simp only [DependencyPlan.advance_append, round33Part0After_eq, round33Part1After_eq, round33Part2After_eq]
def round33After : DependencySnapshot.State := round33Part2After
theorem round33After_eq : DependencyPlan.advance round32After round33Physical = round33After := round33PartsAfter_eq
theorem round33Ordered : DependencyPlan.ordered place round32After round33Physical = true := by
  rw [round33Split]
  simp only [DependencyPlan.ordered_append, DependencyPlan.advance_append, round33Part0After_eq, round33Part1After_eq, round33Part0Ordered, round33Part1Ordered, round33Part2Ordered, Bool.true_and]

end Midnight.SHA256.WitnessDependencyAcceptance
