import Midnight.Math.Witness.DependencySnapshotSyntax
import Midnight.SHA256.WitnessDependencyAcceptanceData
import Midnight.SHA256.WitnessDependencyAcceptance.Stage130

namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

def round63Physical : List (DependencyPlan.PlanAssignment F) := RegionPlan.lower place round63Plan 659
theorem round63Count : round63Plan.length = 7 := by decide +kernel
def round63Part0Physical : List (DependencyPlan.PlanAssignment F) := (round63Physical.drop 0).take 64
dependency_snapshot_step round63Part0 tree40113 from round62After
theorem round63Part0Ordered : DependencyPlan.ordered place round62After round63Part0Physical = true := by decide +kernel
def round63Part1Physical : List (DependencyPlan.PlanAssignment F) := (round63Physical.drop 64).take 64
dependency_snapshot_step round63Part1 tree40311 from round63Part0After
theorem round63Part1Ordered : DependencyPlan.ordered place round63Part0After round63Part1Physical = true := by decide +kernel
def round63Part2Physical : List (DependencyPlan.PlanAssignment F) := (round63Physical.drop 128).take 64
dependency_snapshot_step round63Part2 tree40495 from round63Part1After
theorem round63Part2Ordered : DependencyPlan.ordered place round63Part1After round63Part2Physical = true := by decide +kernel
theorem round63Split : round63Physical = round63Part0Physical ++ round63Part1Physical ++ round63Part2Physical := by rfl
attribute [local irreducible] round62After round63Part0Physical round63Part0After round63Part1Physical round63Part1After round63Part2Physical round63Part2After
theorem round63PartsAfter_eq : DependencyPlan.advance round62After round63Physical = round63Part2After := by
  rw [round63Split]
  simp only [DependencyPlan.advance_append, round63Part0After_eq, round63Part1After_eq, round63Part2After_eq]
def round63After : DependencySnapshot.State := round63Part2After
theorem round63After_eq : DependencyPlan.advance round62After round63Physical = round63After := round63PartsAfter_eq
theorem round63Ordered : DependencyPlan.ordered place round62After round63Physical = true := by
  rw [round63Split]
  simp only [DependencyPlan.ordered_append, DependencyPlan.advance_append, round63Part0After_eq, round63Part1After_eq, round63Part0Ordered, round63Part1Ordered, round63Part2Ordered, Bool.true_and]

end Midnight.SHA256.WitnessDependencyAcceptance
