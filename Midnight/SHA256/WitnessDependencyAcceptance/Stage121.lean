import Midnight.Math.Witness.DependencySnapshotSyntax
import Midnight.SHA256.WitnessDependencyAcceptanceData
import Midnight.SHA256.WitnessDependencyAcceptance.Stage120

namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

def round53Physical : List (DependencyPlan.PlanAssignment F) := RegionPlan.lower place round53Plan 589
theorem round53Count : round53Plan.length = 7 := by decide +kernel
def round53Part0Physical : List (DependencyPlan.PlanAssignment F) := (round53Physical.drop 0).take 64
dependency_snapshot_step round53Part0 tree34339 from round52After
theorem round53Part0Ordered : DependencyPlan.ordered place round52After round53Part0Physical = true := by decide +kernel
def round53Part1Physical : List (DependencyPlan.PlanAssignment F) := (round53Physical.drop 64).take 64
dependency_snapshot_step round53Part1 tree34522 from round53Part0After
theorem round53Part1Ordered : DependencyPlan.ordered place round53Part0After round53Part1Physical = true := by decide +kernel
def round53Part2Physical : List (DependencyPlan.PlanAssignment F) := (round53Physical.drop 128).take 64
dependency_snapshot_step round53Part2 tree34693 from round53Part1After
theorem round53Part2Ordered : DependencyPlan.ordered place round53Part1After round53Part2Physical = true := by decide +kernel
theorem round53Split : round53Physical = round53Part0Physical ++ round53Part1Physical ++ round53Part2Physical := by rfl
attribute [local irreducible] round52After round53Part0Physical round53Part0After round53Part1Physical round53Part1After round53Part2Physical round53Part2After
theorem round53PartsAfter_eq : DependencyPlan.advance round52After round53Physical = round53Part2After := by
  rw [round53Split]
  simp only [DependencyPlan.advance_append, round53Part0After_eq, round53Part1After_eq, round53Part2After_eq]
def round53After : DependencySnapshot.State := round53Part2After
theorem round53After_eq : DependencyPlan.advance round52After round53Physical = round53After := round53PartsAfter_eq
theorem round53Ordered : DependencyPlan.ordered place round52After round53Physical = true := by
  rw [round53Split]
  simp only [DependencyPlan.ordered_append, DependencyPlan.advance_append, round53Part0After_eq, round53Part1After_eq, round53Part0Ordered, round53Part1Ordered, round53Part2Ordered, Bool.true_and]

end Midnight.SHA256.WitnessDependencyAcceptance
