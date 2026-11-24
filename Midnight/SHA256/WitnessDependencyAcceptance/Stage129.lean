import Midnight.Math.Witness.DependencySnapshotSyntax
import Midnight.SHA256.WitnessDependencyAcceptanceData
import Midnight.SHA256.WitnessDependencyAcceptance.Stage128

namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

def round61Physical : List (DependencyPlan.PlanAssignment F) := RegionPlan.lower place round61Plan 645
theorem round61Count : round61Plan.length = 7 := by decide +kernel
def round61Part0Physical : List (DependencyPlan.PlanAssignment F) := (round61Physical.drop 0).take 64
dependency_snapshot_step round61Part0 tree38956 from round60After
theorem round61Part0Ordered : DependencyPlan.ordered place round60After round61Part0Physical = true := by decide +kernel
def round61Part1Physical : List (DependencyPlan.PlanAssignment F) := (round61Physical.drop 64).take 64
dependency_snapshot_step round61Part1 tree39149 from round61Part0After
theorem round61Part1Ordered : DependencyPlan.ordered place round61Part0After round61Part1Physical = true := by decide +kernel
def round61Part2Physical : List (DependencyPlan.PlanAssignment F) := (round61Physical.drop 128).take 64
dependency_snapshot_step round61Part2 tree39323 from round61Part1After
theorem round61Part2Ordered : DependencyPlan.ordered place round61Part1After round61Part2Physical = true := by decide +kernel
theorem round61Split : round61Physical = round61Part0Physical ++ round61Part1Physical ++ round61Part2Physical := by rfl
attribute [local irreducible] round60After round61Part0Physical round61Part0After round61Part1Physical round61Part1After round61Part2Physical round61Part2After
theorem round61PartsAfter_eq : DependencyPlan.advance round60After round61Physical = round61Part2After := by
  rw [round61Split]
  simp only [DependencyPlan.advance_append, round61Part0After_eq, round61Part1After_eq, round61Part2After_eq]
def round61After : DependencySnapshot.State := round61Part2After
theorem round61After_eq : DependencyPlan.advance round60After round61Physical = round61After := round61PartsAfter_eq
theorem round61Ordered : DependencyPlan.ordered place round60After round61Physical = true := by
  rw [round61Split]
  simp only [DependencyPlan.ordered_append, DependencyPlan.advance_append, round61Part0After_eq, round61Part1After_eq, round61Part0Ordered, round61Part1Ordered, round61Part2Ordered, Bool.true_and]

end Midnight.SHA256.WitnessDependencyAcceptance
