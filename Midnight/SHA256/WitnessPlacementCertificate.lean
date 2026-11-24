import Midnight.SHA256.WitnessPlacement
import Midnight.SHA256.Semantics.StructuralPlacementData

/-! Exact bridge from actual witness placement to the compact source-certified
structural placement. The reduction data are computed from that source below;
no reference-capture layout is assumed. -/
namespace Midnight.SHA256.WitnessPlacementCertificate
open Midnight.Math.FloorPlanner

attribute [local irreducible] WitnessExecution.starts WitnessPlacement.sourceShapes
  Semantics.StructuralPlacement.shapes

theorem sourceShapes_eq :
    WitnessPlacement.sourceShapes = Semantics.StructuralPlacement.shapes := by
  unfold WitnessPlacement.sourceShapes
  exact Semantics.StructuralPlacement.source_shapes

theorem execution_starts :
    WitnessExecution.starts = Semantics.StructuralPlacementData.starts := by
  rw [WitnessPlacement.execution_starts, sourceShapes_eq]
  exact Semantics.StructuralPlacementData.source_starts

theorem execution_place (region : Halo2.RegionIndex) :
    WitnessExecution.place region = Semantics.StructuralPlacementData.starts[region]! := by
  rw [WitnessExecution.place, execution_starts]

theorem execution_place_eq :
    WitnessExecution.place = fun region => Semantics.StructuralPlacementData.starts[region]! := by
  funext region
  exact execution_place region

end Midnight.SHA256.WitnessPlacementCertificate
