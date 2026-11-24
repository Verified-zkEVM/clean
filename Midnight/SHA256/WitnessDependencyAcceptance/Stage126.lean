import Midnight.Math.Witness.DependencySnapshotSyntax
import Midnight.SHA256.WitnessDependencyAcceptanceData
import Midnight.SHA256.WitnessDependencyAcceptance.Stage125

namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

def round58Physical : List (DependencyPlan.PlanAssignment F) := RegionPlan.lower place round58Plan 624
theorem round58Count : round58Plan.length = 7 := by decide +kernel
def round58Part0Physical : List (DependencyPlan.PlanAssignment F) := (round58Physical.drop 0).take 64
dependency_snapshot_step round58Part0 tree37207 from round57After
theorem round58Part0Ordered : DependencyPlan.ordered place round57After round58Part0Physical = true := by decide +kernel
def round58Part1Physical : List (DependencyPlan.PlanAssignment F) := (round58Physical.drop 64).take 64
dependency_snapshot_step round58Part1 tree37404 from round58Part0After
theorem round58Part1Ordered : DependencyPlan.ordered place round58Part0After round58Part1Physical = true := by decide +kernel
def round58Part2Physical : List (DependencyPlan.PlanAssignment F) := (round58Physical.drop 128).take 64
dependency_snapshot_step round58Part2 tree37580 from round58Part1After
theorem round58Part2Ordered : DependencyPlan.ordered place round58Part1After round58Part2Physical = true := by decide +kernel
theorem round58Split : round58Physical = round58Part0Physical ++ round58Part1Physical ++ round58Part2Physical := by rfl
attribute [local irreducible] round57After round58Part0Physical round58Part0After round58Part1Physical round58Part1After round58Part2Physical round58Part2After
theorem round58PartsAfter_eq : DependencyPlan.advance round57After round58Physical = round58Part2After := by
  rw [round58Split]
  simp only [DependencyPlan.advance_append, round58Part0After_eq, round58Part1After_eq, round58Part2After_eq]
def round58After : DependencySnapshot.State := round58Part2After
theorem round58After_eq : DependencyPlan.advance round57After round58Physical = round58After := round58PartsAfter_eq
theorem round58Ordered : DependencyPlan.ordered place round57After round58Physical = true := by
  rw [round58Split]
  simp only [DependencyPlan.ordered_append, DependencyPlan.advance_append, round58Part0After_eq, round58Part1After_eq, round58Part0Ordered, round58Part1Ordered, round58Part2Ordered, Bool.true_and]

end Midnight.SHA256.WitnessDependencyAcceptance
