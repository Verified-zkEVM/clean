import Midnight.Math.Witness.DependencySnapshotSyntax
import Midnight.SHA256.WitnessDependencyAcceptanceData
import Midnight.SHA256.WitnessDependencyAcceptance.Stage99

namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

def round32Physical : List (DependencyPlan.PlanAssignment F) := RegionPlan.lower place round32Plan 442
theorem round32Count : round32Plan.length = 7 := by decide +kernel
def round32Part0Physical : List (DependencyPlan.PlanAssignment F) := (round32Physical.drop 0).take 64
dependency_snapshot_step round32Part0 tree22497 from round31After
theorem round32Part0Ordered : DependencyPlan.ordered place round31After round32Part0Physical = true := by decide +kernel
def round32Part1Physical : List (DependencyPlan.PlanAssignment F) := (round32Physical.drop 64).take 64
dependency_snapshot_step round32Part1 tree22679 from round32Part0After
theorem round32Part1Ordered : DependencyPlan.ordered place round32Part0After round32Part1Physical = true := by decide +kernel
def round32Part2Physical : List (DependencyPlan.PlanAssignment F) := (round32Physical.drop 128).take 64
dependency_snapshot_step round32Part2 tree22845 from round32Part1After
theorem round32Part2Ordered : DependencyPlan.ordered place round32Part1After round32Part2Physical = true := by decide +kernel
theorem round32Split : round32Physical = round32Part0Physical ++ round32Part1Physical ++ round32Part2Physical := by rfl
attribute [local irreducible] round31After round32Part0Physical round32Part0After round32Part1Physical round32Part1After round32Part2Physical round32Part2After
theorem round32PartsAfter_eq : DependencyPlan.advance round31After round32Physical = round32Part2After := by
  rw [round32Split]
  simp only [DependencyPlan.advance_append, round32Part0After_eq, round32Part1After_eq, round32Part2After_eq]
def round32After : DependencySnapshot.State := round32Part2After
theorem round32After_eq : DependencyPlan.advance round31After round32Physical = round32After := round32PartsAfter_eq
theorem round32Ordered : DependencyPlan.ordered place round31After round32Physical = true := by
  rw [round32Split]
  simp only [DependencyPlan.ordered_append, DependencyPlan.advance_append, round32Part0After_eq, round32Part1After_eq, round32Part0Ordered, round32Part1Ordered, round32Part2Ordered, Bool.true_and]

end Midnight.SHA256.WitnessDependencyAcceptance
