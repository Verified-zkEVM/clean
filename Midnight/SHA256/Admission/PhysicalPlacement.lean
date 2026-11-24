import Midnight.Math.FloorPlanner.SimplePlacement
import Clean.Halo2.Keygen.FloorPlanner.Allocations
import Clean.Halo2.Keygen.Layout
import Midnight.SHA256.Semantics.StructuralPlacementData

/-! Physical bounds of the actual source Simple planner. The compact shapes and
starts are already proved projections of the source; the closed check below adds
bounds, not a new placement definition. -/
namespace Midnight.SHA256.Admission.PhysicalPlacement
open Halo2 Halo2.FloorPlanner Midnight.Math.FloorPlanner Semantics

attribute [local irreducible] Synthesis.operations Synthesis.toOperations Synthesis.schedule

def measured : List RegionShape := indexRegionSummaries 0 StructuralPlacementShapes.shapes

def starts : List Nat := StructuralPlacementData.starts.toList

theorem source_measured : measureRegions (Synthesis.operations activation) = measured := by
  rw [measureRegions_eq_synthesisSummary_regionShapes, ← SimpleShapes.observe_eq,
    StructuralPlacement.source_shapes, StructuralPlacementShapes.shapes_eq]
  rfl

theorem source_starts : SimpleFloorPlanner.starts (Synthesis.operations activation) = starts := by
  rw [← SimpleShapes.starts_observe_native, StructuralPlacement.source_shapes,
    StructuralPlacementShapes.shapes_eq, StructuralPlacementData.starts_eq]
  rfl

def ColumnBound : RegionColumn → Prop
  | .column .advice index => index < 8
  | .column .fixed index => index < 16
  | .column .instance index => index < 2
  | .selector index => index < 16

instance (column : RegionColumn) : Decidable (ColumnBound column) := by
  cases column with
  | selector => unfold ColumnBound; infer_instance
  | column kind index => cases kind <;> unfold ColumnBound <;> infer_instance

def PairBound (item : RegionShape × Nat) : Prop :=
  item.2 + item.1.rowCount ≤ 8183 ∧ item.1.columns.Forall ColumnBound

instance (item : RegionShape × Nat) : Decidable (PairBound item) := by
  unfold PairBound
  infer_instance

set_option maxRecDepth 10000 in
private theorem bounds_checked : (measured.zip starts).all (fun item => decide (PairBound item)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
private theorem lengths_checked : measured.length = starts.length := by decide +kernel

private theorem indexed_get (shapes : List RegionShape)
    (indices : shapes.map RegionShape.index = List.range shapes.length)
    (i : Nat) (bound : i < shapes.length) : (shapes[i]).index = i := by
  have same := congrArg (fun list : List Nat => list[i]!) indices
  have ha : i < (shapes.map RegionShape.index).length := by simpa using bound
  have hb : i < (List.range shapes.length).length := by simpa using bound
  change (shapes.map RegionShape.index)[i]! = (List.range shapes.length)[i]! at same
  rw [getElem!_pos (shapes.map RegionShape.index) i ha, getElem!_pos (List.range shapes.length) i hb] at same
  simpa only [List.getElem_map, List.getElem_range] using same

attribute [local irreducible] measured starts

theorem source_shape_bounds (shape : RegionShape)
    (member : shape ∈ measureRegions (Synthesis.operations activation)) :
    shape.index < (SimpleFloorPlanner.starts (Synthesis.operations activation)).length ∧
    (SimpleFloorPlanner.starts (Synthesis.operations activation)).getD shape.index 0 + shape.rowCount ≤ 8183 ∧
    shape.columns.Forall ColumnBound := by
  have indices : measured.map RegionShape.index = List.range measured.length := by
    have original := measureRegions_indices_eq_range (Synthesis.operations activation)
    rw [source_measured] at original
    have lengthEq := congrArg List.length original
    simp only [List.length_map, List.length_range] at lengthEq
    rw [lengthEq]
    exact original
  rw [source_starts]
  rw [source_measured] at member
  obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp member
  have same := indexed_get measured indices i hi
  have hs : i < starts.length := lengths_checked ▸ hi
  have hp : (measured[i], starts[i]) ∈ measured.zip starts := by
    have hz : i < (measured.zip starts).length := by simp [hi, hs]
    have mem := List.getElem_mem hz
    simpa only [List.getElem_zip] using mem
  have bound := of_decide_eq_true (List.all_eq_true.mp bounds_checked _ hp)
  rw [same, List.getD_eq_getElem _ _ hs]
  exact ⟨hs,bound⟩

end Midnight.SHA256.Admission.PhysicalPlacement
