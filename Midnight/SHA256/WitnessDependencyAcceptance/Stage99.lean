import Midnight.Math.Witness.DependencySnapshotSyntax
import Midnight.SHA256.WitnessDependencyAcceptanceData
import Midnight.SHA256.WitnessDependencyAcceptance.Stage98

namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

def round31Physical : List (DependencyPlan.PlanAssignment F) := RegionPlan.lower place round31Plan 435
theorem round31Count : round31Plan.length = 7 := by decide +kernel
def round31Part0Physical : List (DependencyPlan.PlanAssignment F) := (round31Physical.drop 0).take 64
dependency_snapshot_step round31Part0 tree21961 from round30After
theorem round31Part0Ordered : DependencyPlan.ordered place round30After round31Part0Physical = true := by decide +kernel
def round31Part1Physical : List (DependencyPlan.PlanAssignment F) := (round31Physical.drop 64).take 64
dependency_snapshot_step round31Part1 tree22149 from round31Part0After
theorem round31Part1Ordered : DependencyPlan.ordered place round31Part0After round31Part1Physical = true := by decide +kernel
def round31Part2Physical : List (DependencyPlan.PlanAssignment F) := (round31Physical.drop 128).take 64
dependency_snapshot_step round31Part2 tree22319 from round31Part1After
theorem round31Part2Ordered : DependencyPlan.ordered place round31Part1After round31Part2Physical = true := by decide +kernel
theorem round31Split : round31Physical = round31Part0Physical ++ round31Part1Physical ++ round31Part2Physical := by rfl
attribute [local irreducible] round30After round31Part0Physical round31Part0After round31Part1Physical round31Part1After round31Part2Physical round31Part2After
theorem round31PartsAfter_eq : DependencyPlan.advance round30After round31Physical = round31Part2After := by
  rw [round31Split]
  simp only [DependencyPlan.advance_append, round31Part0After_eq, round31Part1After_eq, round31Part2After_eq]
def round31After : DependencySnapshot.State := round31Part2After
theorem round31After_eq : DependencyPlan.advance round30After round31Physical = round31After := round31PartsAfter_eq
theorem round31Ordered : DependencyPlan.ordered place round30After round31Physical = true := by
  rw [round31Split]
  simp only [DependencyPlan.ordered_append, DependencyPlan.advance_append, round31Part0After_eq, round31Part1After_eq, round31Part0Ordered, round31Part1Ordered, round31Part2Ordered, Bool.true_and]

end Midnight.SHA256.WitnessDependencyAcceptance
