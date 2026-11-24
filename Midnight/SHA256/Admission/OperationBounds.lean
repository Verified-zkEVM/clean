import Midnight.Chips.OperationsLawful

/-! Allocated measured columns and a bounded region interval imply bounds on
its actual writes/enables. Lookup selector shape remains an explicit source fact. -/
namespace Midnight.SHA256.Admission.OperationBounds
open Halo2 Halo2.FloorPlanner Midnight.Chips

def ColumnBound (counts : ConfigureCounts) : RegionColumn → Prop
  | .column .advice column => column < counts.numAdviceColumns
  | .column .fixed column => column < counts.numFixedColumns
  | .column .instance column => column < counts.numInstanceColumns
  | .selector selector => selector < counts.numSelectors

theorem instruction (counts : ConfigureCounts) (index start usable : Nat)
    (body : RegionOperations F)
    (rows : start + (measureRegion index body).rowCount ≤ usable)
    (columns : (measureRegion index body).columns.Forall (ColumnBound counts))
    (lookupShape : ∀ lookup enabled row, .enableLookup lookup enabled row ∈ body →
      enabled = [lookup.masterSelector.toSelector])
    (operation : RegionOperation F) (member : operation ∈ body) :
    OperationsLawful.InstructionValid counts start usable operation := by
  have bounded := regionOperationRowExtent_le_synthesisSummary_of_mem body operation member
  have column (col : RegionColumn) (hc : col ∈ regionOperationShapeColumns operation) :
      ColumnBound counts col :=
    List.forall_iff_forall_mem.mp columns col
      (mem_regionSynthesisSummary_columns_of_mem body operation member col hc)
  cases operation with
  | assignAdvice col row witness =>
    exact column (.column .advice col.index) (by simp [regionOperationShapeColumns])
  | assignFixed col row value =>
    have hc := column (.column .fixed col.index) (by simp [regionOperationShapeColumns])
    exact ⟨hc, by simp only [regionOperationRowExtent, measureRegion_rowCount] at bounded rows; omega⟩
  | enableGate gate row =>
    have hc := column (.selector gate.selector.index) (by simp [regionOperationShapeColumns])
    exact ⟨hc, by simp only [regionOperationRowExtent, measureRegion_rowCount] at bounded rows; omega⟩
  | enableLookup lookup enabled row =>
    have same := lookupShape lookup enabled row member
    have hc := column (.selector lookup.masterSelector.index)
      (by simp [regionOperationShapeColumns, same, ComplexSelector.toSelector])
    exact ⟨same, hc, by simp only [regionOperationRowExtent, measureRegion_rowCount] at bounded rows; omega⟩
  | constrainEqual | constrainConstant | constrainInstance => trivial

/-- The usable-row bound of an assignment, which copy endpoints need. -/
def AssignedRow (start usable : Nat) : RegionOperation F → Prop
  | .assignAdvice _ row _ | .assignFixed _ row _ => start + row < usable
  | _ => True

theorem assignedRow (index start usable : Nat) (body : RegionOperations F)
    (rows : start + (measureRegion index body).rowCount ≤ usable)
    (operation : RegionOperation F) (member : operation ∈ body) :
    AssignedRow start usable operation := by
  have bounded := regionOperationRowExtent_le_synthesisSummary_of_mem body operation member
  cases operation <;> simp only [AssignedRow] <;>
    simp only [regionOperationRowExtent, measureRegion_rowCount] at bounded rows <;> omega

end Midnight.SHA256.Admission.OperationBounds
