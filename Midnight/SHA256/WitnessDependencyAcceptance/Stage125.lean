import Midnight.Math.Witness.DependencySnapshotSyntax
import Midnight.SHA256.WitnessDependencyAcceptanceData
import Midnight.SHA256.WitnessDependencyAcceptance.Stage124

namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

def round57Physical : List (DependencyPlan.PlanAssignment F) := RegionPlan.lower place round57Plan 617
theorem round57Count : round57Plan.length = 7 := by decide +kernel
def round57Part0Physical : List (DependencyPlan.PlanAssignment F) := (round57Physical.drop 0).take 64
dependency_snapshot_step round57Part0 tree36620 from round56After
theorem round57Part0Ordered : DependencyPlan.ordered place round56After round57Part0Physical = true := by decide +kernel
def round57Part1Physical : List (DependencyPlan.PlanAssignment F) := (round57Physical.drop 64).take 64
dependency_snapshot_step round57Part1 tree36820 from round57Part0After
theorem round57Part1Ordered : DependencyPlan.ordered place round57Part0After round57Part1Physical = true := by decide +kernel
def round57Part2Physical : List (DependencyPlan.PlanAssignment F) := (round57Physical.drop 128).take 64
dependency_snapshot_step round57Part2 tree37003 from round57Part1After
theorem round57Part2Ordered : DependencyPlan.ordered place round57Part1After round57Part2Physical = true := by decide +kernel
theorem round57Split : round57Physical = round57Part0Physical ++ round57Part1Physical ++ round57Part2Physical := by rfl
attribute [local irreducible] round56After round57Part0Physical round57Part0After round57Part1Physical round57Part1After round57Part2Physical round57Part2After
theorem round57PartsAfter_eq : DependencyPlan.advance round56After round57Physical = round57Part2After := by
  rw [round57Split]
  simp only [DependencyPlan.advance_append, round57Part0After_eq, round57Part1After_eq, round57Part2After_eq]
def round57After : DependencySnapshot.State := round57Part2After
theorem round57After_eq : DependencyPlan.advance round56After round57Physical = round57After := round57PartsAfter_eq
theorem round57Ordered : DependencyPlan.ordered place round56After round57Physical = true := by
  rw [round57Split]
  simp only [DependencyPlan.ordered_append, DependencyPlan.advance_append, round57Part0After_eq, round57Part1After_eq, round57Part0Ordered, round57Part1Ordered, round57Part2Ordered, Bool.true_and]

end Midnight.SHA256.WitnessDependencyAcceptance
