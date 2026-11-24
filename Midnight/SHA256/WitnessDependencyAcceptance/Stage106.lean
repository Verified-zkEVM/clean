import Midnight.Math.Witness.DependencySnapshotSyntax
import Midnight.SHA256.WitnessDependencyAcceptanceData
import Midnight.SHA256.WitnessDependencyAcceptance.Stage105

namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

def round38Physical : List (DependencyPlan.PlanAssignment F) := RegionPlan.lower place round38Plan 484
theorem round38Count : round38Plan.length = 7 := by decide +kernel
def round38Part0Physical : List (DependencyPlan.PlanAssignment F) := (round38Physical.drop 0).take 64
dependency_snapshot_step round38Part0 tree25819 from round37After
theorem round38Part0Ordered : DependencyPlan.ordered place round37After round38Part0Physical = true := by decide +kernel
def round38Part1Physical : List (DependencyPlan.PlanAssignment F) := (round38Physical.drop 64).take 64
dependency_snapshot_step round38Part1 tree26010 from round38Part0After
theorem round38Part1Ordered : DependencyPlan.ordered place round38Part0After round38Part1Physical = true := by decide +kernel
def round38Part2Physical : List (DependencyPlan.PlanAssignment F) := (round38Physical.drop 128).take 64
dependency_snapshot_step round38Part2 tree26182 from round38Part1After
theorem round38Part2Ordered : DependencyPlan.ordered place round38Part1After round38Part2Physical = true := by decide +kernel
theorem round38Split : round38Physical = round38Part0Physical ++ round38Part1Physical ++ round38Part2Physical := by rfl
attribute [local irreducible] round37After round38Part0Physical round38Part0After round38Part1Physical round38Part1After round38Part2Physical round38Part2After
theorem round38PartsAfter_eq : DependencyPlan.advance round37After round38Physical = round38Part2After := by
  rw [round38Split]
  simp only [DependencyPlan.advance_append, round38Part0After_eq, round38Part1After_eq, round38Part2After_eq]
def round38After : DependencySnapshot.State := round38Part2After
theorem round38After_eq : DependencyPlan.advance round37After round38Physical = round38After := round38PartsAfter_eq
theorem round38Ordered : DependencyPlan.ordered place round37After round38Physical = true := by
  rw [round38Split]
  simp only [DependencyPlan.ordered_append, DependencyPlan.advance_append, round38Part0After_eq, round38Part1After_eq, round38Part0Ordered, round38Part1Ordered, round38Part2Ordered, Bool.true_and]

end Midnight.SHA256.WitnessDependencyAcceptance
