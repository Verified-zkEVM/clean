import Midnight.SHA256.Admission.Configuration
import Midnight.SHA256.Admission.Activation
import Midnight.SHA256.Admission.OperationBounds
import Midnight.SHA256.Admission.PhysicalPlacement
import Midnight.SHA256.Admission.Tables

/-! Allocation, usable-row bounds and complete activation closure for the actual
source operation stream at its native Simple placement. -/
namespace Midnight.SHA256.Admission
open Halo2 Halo2.FloorPlanner Midnight.Chips
attribute [local irreducible] Synthesis.operations Synthesis.schedule configured cleanGates cleanLookups

def source_operations : OperationsLawful.Lawful (Synthesis.operations activation)
    cleanGates cleanLookups configured.counts
    (SimpleFloorPlanner.starts (Synthesis.operations activation)) 8183 where
  regions := by
    apply List.forall_iff_forall_mem.mpr
    rintro ⟨index,body⟩ member
    have measured : measureRegion index body ∈ measureRegions (Synthesis.operations activation) :=
      List.mem_map.mpr ⟨(index,body),member,rfl⟩
    obtain ⟨indexBound,rowBound,columns⟩ := PhysicalPlacement.source_shape_bounds _ measured
    refine ⟨indexBound, ?_, source_activationClosed index body member⟩
    have allocated : (measureRegion index body).columns.Forall (OperationBounds.ColumnBound configured.counts) := by
      rw [counts]
      exact columns
    apply List.forall_iff_forall_mem.mpr
    intro operation source
    exact OperationBounds.instruction configured.counts index _ 8183 body rowBound allocated
      (source_lookup_shape index body member) operation source
  tables := source_tables configured.counts (by rw [counts])
  tablesDistinct := source_tablesDistinct
  instanceCopies := source_instanceCopies

theorem source_assignedRows :
    (indexedRegions (Synthesis.operations activation) 0).1.Forall fun (index, body) =>
      body.Forall (OperationBounds.AssignedRow
        ((SimpleFloorPlanner.starts (Synthesis.operations activation)).getD index 0) 8183) := by
  apply List.forall_iff_forall_mem.mpr
  rintro ⟨index,body⟩ member
  have measured : measureRegion index body ∈ measureRegions (Synthesis.operations activation) :=
    List.mem_map.mpr ⟨(index,body),member,rfl⟩
  obtain ⟨-,rowBound,-⟩ := PhysicalPlacement.source_shape_bounds _ measured
  exact List.forall_iff_forall_mem.mpr fun operation source =>
    OperationBounds.assignedRow index _ 8183 body rowBound operation source

end Midnight.SHA256.Admission
