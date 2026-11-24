import Midnight.Math.Witness.DependencySnapshotSyntax
import Midnight.SHA256.WitnessDependencyAcceptanceData
import Midnight.SHA256.WitnessDependencyAcceptance.Stage91

namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

def round24Physical : List (DependencyPlan.PlanAssignment F) := RegionPlan.lower place round24Plan 386
theorem round24Count : round24Plan.length = 7 := by decide +kernel
def round24Part0Physical : List (DependencyPlan.PlanAssignment F) := (round24Physical.drop 0).take 64
dependency_snapshot_step round24Part0 tree18137 from round23After
theorem round24Part0Ordered : DependencyPlan.ordered place round23After round24Part0Physical = true := by decide +kernel
def round24Part1Physical : List (DependencyPlan.PlanAssignment F) := (round24Physical.drop 64).take 64
dependency_snapshot_step round24Part1 tree18332 from round24Part0After
theorem round24Part1Ordered : DependencyPlan.ordered place round24Part0After round24Part1Physical = true := by decide +kernel
def round24Part2Physical : List (DependencyPlan.PlanAssignment F) := (round24Physical.drop 128).take 64
dependency_snapshot_step round24Part2 tree18506 from round24Part1After
theorem round24Part2Ordered : DependencyPlan.ordered place round24Part1After round24Part2Physical = true := by decide +kernel
theorem round24Split : round24Physical = round24Part0Physical ++ round24Part1Physical ++ round24Part2Physical := by rfl
attribute [local irreducible] round23After round24Part0Physical round24Part0After round24Part1Physical round24Part1After round24Part2Physical round24Part2After
theorem round24PartsAfter_eq : DependencyPlan.advance round23After round24Physical = round24Part2After := by
  rw [round24Split]
  simp only [DependencyPlan.advance_append, round24Part0After_eq, round24Part1After_eq, round24Part2After_eq]
def round24After : DependencySnapshot.State := round24Part2After
theorem round24After_eq : DependencyPlan.advance round23After round24Physical = round24After := round24PartsAfter_eq
theorem round24Ordered : DependencyPlan.ordered place round23After round24Physical = true := by
  rw [round24Split]
  simp only [DependencyPlan.ordered_append, DependencyPlan.advance_append, round24Part0After_eq, round24Part1After_eq, round24Part0Ordered, round24Part1Ordered, round24Part2Ordered, Bool.true_and]

end Midnight.SHA256.WitnessDependencyAcceptance
