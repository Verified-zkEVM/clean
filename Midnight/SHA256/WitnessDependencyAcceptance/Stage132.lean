import Midnight.Math.Witness.DependencySnapshotSyntax
import Midnight.SHA256.WitnessDependencyAcceptanceData
import Midnight.SHA256.WitnessDependencyAcceptance.Stage131

namespace Midnight.SHA256.WitnessDependencyAcceptance
open Halo2 Midnight.Math.Witness Semantics.WitnessCheckpoints
attribute [local instance] lexOrd
set_option Elab.async false
set_option maxRecDepth 10000

def feedforwardPhysical : List (DependencyPlan.PlanAssignment F) := RegionPlan.lower place feedforwardPlan 666
theorem feedforwardCount : feedforwardPlan.length = 8 := by decide +kernel
def feedforwardPart0Physical : List (DependencyPlan.PlanAssignment F) := (feedforwardPhysical.drop 0).take 64
dependency_snapshot_step feedforwardPart0 tree40684 from round63After
theorem feedforwardPart0Ordered : DependencyPlan.ordered place round63After feedforwardPart0Physical = true := by decide +kernel
def feedforwardPart1Physical : List (DependencyPlan.PlanAssignment F) := (feedforwardPhysical.drop 64).take 64
dependency_snapshot_step feedforwardPart1 tree40891 from feedforwardPart0After
theorem feedforwardPart1Ordered : DependencyPlan.ordered place feedforwardPart0After feedforwardPart1Physical = true := by decide +kernel
def feedforwardPart2Physical : List (DependencyPlan.PlanAssignment F) := (feedforwardPhysical.drop 128).take 64
dependency_snapshot_step feedforwardPart2 tree41104 from feedforwardPart1After
theorem feedforwardPart2Ordered : DependencyPlan.ordered place feedforwardPart1After feedforwardPart2Physical = true := by decide +kernel
def feedforwardPart3Physical : List (DependencyPlan.PlanAssignment F) := (feedforwardPhysical.drop 192).take 64
dependency_snapshot_step feedforwardPart3 tree41266 from feedforwardPart2After
theorem feedforwardPart3Ordered : DependencyPlan.ordered place feedforwardPart2After feedforwardPart3Physical = true := by decide +kernel
theorem feedforwardSplit : feedforwardPhysical = feedforwardPart0Physical ++ feedforwardPart1Physical ++ feedforwardPart2Physical ++ feedforwardPart3Physical := by rfl
attribute [local irreducible] round63After feedforwardPart0Physical feedforwardPart0After feedforwardPart1Physical feedforwardPart1After feedforwardPart2Physical feedforwardPart2After feedforwardPart3Physical feedforwardPart3After
theorem feedforwardPartsAfter_eq : DependencyPlan.advance round63After feedforwardPhysical = feedforwardPart3After := by
  rw [feedforwardSplit]
  simp only [DependencyPlan.advance_append, feedforwardPart0After_eq, feedforwardPart1After_eq, feedforwardPart2After_eq, feedforwardPart3After_eq]
def feedforwardAfter : DependencySnapshot.State := feedforwardPart3After
theorem feedforwardAfter_eq : DependencyPlan.advance round63After feedforwardPhysical = feedforwardAfter := feedforwardPartsAfter_eq
theorem feedforwardOrdered : DependencyPlan.ordered place round63After feedforwardPhysical = true := by
  rw [feedforwardSplit]
  simp only [DependencyPlan.ordered_append, DependencyPlan.advance_append, feedforwardPart0After_eq, feedforwardPart1After_eq, feedforwardPart2After_eq, feedforwardPart0Ordered, feedforwardPart1Ordered, feedforwardPart2Ordered, feedforwardPart3Ordered, Bool.true_and]

end Midnight.SHA256.WitnessDependencyAcceptance
