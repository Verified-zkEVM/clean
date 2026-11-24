import Midnight.Math.Witness.Operations
import Midnight.Math.Witness.Fast
import Midnight.Math.FloorPlanner.SimplePlacement
import Midnight.SHA256.Semantics.PreimageSource
import Clean.Halo2.Keygen.FloorPlanner.Simple

/-! Constructive execution of the actual fixed-input native SHA circuit at its
SimpleFloorPlanner placement. The dependency certificate is independent of
private hint values: programs read the hint only when execution takes place. -/
namespace Midnight.SHA256.WitnessExecution
open Halo2 Midnight.Math.Witness

def source : Operations F := (WitnessCircuit.preimageCircuit Semantics.Preimage.privatePrograms).operations

def starts : Array Nat := (Midnight.Math.FloorPlanner.SimplePlacement.starts source).toArray

theorem starts_eq_native : starts = (FloorPlanner.SimpleFloorPlanner.starts source).toArray := by
  unfold starts
  rw [Midnight.Math.FloorPlanner.SimplePlacement.starts_eq_native]

def place (self : RegionIndex) : Nat := starts[self]!

def scalarAssignments : List (Execute.Assignment F) := Operations.assignments place source 0

def dependencyCheck : Bool := Fast.ordered place ∅ scalarAssignments

end Midnight.SHA256.WitnessExecution
