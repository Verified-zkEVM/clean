import Midnight.Math.Witness.DependencySnapshotSyntax
import Midnight.SHA256.WitnessDependencyAcceptanceData
import Midnight.SHA256.WitnessDependencyAcceptance.Stage127

namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

def round60Physical : List (DependencyPlan.PlanAssignment F) := RegionPlan.lower place round60Plan 638
theorem round60Count : round60Plan.length = 7 := by decide +kernel
def round60Part0Physical : List (DependencyPlan.PlanAssignment F) := (round60Physical.drop 0).take 64
dependency_snapshot_step round60Part0 tree38363 from round59After
theorem round60Part0Ordered : DependencyPlan.ordered place round59After round60Part0Physical = true := by decide +kernel
def round60Part1Physical : List (DependencyPlan.PlanAssignment F) := (round60Physical.drop 64).take 64
dependency_snapshot_step round60Part1 tree38569 from round60Part0After
theorem round60Part1Ordered : DependencyPlan.ordered place round60Part0After round60Part1Physical = true := by decide +kernel
def round60Part2Physical : List (DependencyPlan.PlanAssignment F) := (round60Physical.drop 128).take 64
dependency_snapshot_step round60Part2 tree38754 from round60Part1After
theorem round60Part2Ordered : DependencyPlan.ordered place round60Part1After round60Part2Physical = true := by decide +kernel
theorem round60Split : round60Physical = round60Part0Physical ++ round60Part1Physical ++ round60Part2Physical := by rfl
attribute [local irreducible] round59After round60Part0Physical round60Part0After round60Part1Physical round60Part1After round60Part2Physical round60Part2After
theorem round60PartsAfter_eq : DependencyPlan.advance round59After round60Physical = round60Part2After := by
  rw [round60Split]
  simp only [DependencyPlan.advance_append, round60Part0After_eq, round60Part1After_eq, round60Part2After_eq]
def round60After : DependencySnapshot.State := round60Part2After
theorem round60After_eq : DependencyPlan.advance round59After round60Physical = round60After := round60PartsAfter_eq
theorem round60Ordered : DependencyPlan.ordered place round59After round60Physical = true := by
  rw [round60Split]
  simp only [DependencyPlan.ordered_append, DependencyPlan.advance_append, round60Part0After_eq, round60Part1After_eq, round60Part0Ordered, round60Part1Ordered, round60Part2Ordered, Bool.true_and]

end Midnight.SHA256.WitnessDependencyAcceptance
