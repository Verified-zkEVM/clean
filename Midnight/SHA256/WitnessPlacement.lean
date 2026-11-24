import Midnight.Math.FloorPlanner.SimpleShapes
import Midnight.SHA256.WitnessExecution
import Midnight.SHA256.Semantics.ErasureStructural

/-! Exact placement bridge for the original SHA witness program. Advice erasure
preserves every measured shape, so the static source's compact shape projection
can supply its starts. A separately proved shape checkpoint can replace that
projection through `starts_eq_of_observe_eq`; no captured starts are assumed. -/
namespace Midnight.SHA256.WitnessPlacement
open Halo2 Midnight.Math.FloorPlanner

attribute [local irreducible] WitnessCircuit.preimageCircuit WitnessExecution.source
  Synthesis.operations SHA256.activation

def sourceShapes : List FloorPlanner.RegionShapeSummary :=
  SimpleShapes.observe (Synthesis.operations SHA256.activation)

theorem observe_erasure (ops : Operations F) :
    SimpleShapes.observe (WitnessErasure.operations ops) = SimpleShapes.observe ops := by
  rw [SimpleShapes.observe_eq, SimpleShapes.observe_eq, WitnessErasure.summary]

theorem source_shapes (input : Vector (WitgenIR F 1) 24) :
    SimpleShapes.observe ((WitnessCircuit.preimageCircuit input).operations 0) = sourceShapes := by
  rw [← observe_erasure, WitnessErasure.preimage_operations_eq_source]
  rfl

theorem source_starts (input : Vector (WitgenIR F 1) 24) :
    SimplePlacement.starts ((WitnessCircuit.preimageCircuit input).operations 0) =
      SimpleShapes.starts sourceShapes :=
  SimpleShapes.starts_eq_of_observe_eq _ sourceShapes (source_shapes input)

theorem execution_starts :
    WitnessExecution.starts = (SimpleShapes.starts sourceShapes).toArray := by
  unfold WitnessExecution.starts
  simpa only [WitnessExecution.source] using
    congrArg List.toArray (source_starts Semantics.Preimage.privatePrograms)

end Midnight.SHA256.WitnessPlacement
