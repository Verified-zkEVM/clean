import Midnight.SHA256.Admission.PhysicalPlacement
import Midnight.SHA256.Admission.PhysicalHelpers
import Midnight.SHA256.Admission.Configuration
import Midnight.SHA256.Admission.Tables
import Midnight.SHA256.Semantics.StructuralBase

/-! Complete fixed/selector layout admission for the actual source Simple
placement. Bounds come from source-certified compact shapes; overlapping fixed
writes need no agreement because the dense compiler keeps the last write. -/
namespace Midnight.SHA256.Admission.Physical
open Halo2 Halo2.FloorPlanner Midnight.Chips Semantics
open PhysicalHelpers PhysicalPlacement

attribute [local irreducible] Synthesis.operations Synthesis.toOperations Synthesis.schedule
  configured

theorem table_bounds (ops : Operations F)
    (tables : ops.Forall (OperationsLawful.TableValid ⟨8,16,2,16⟩ 8183))
    (write : Halo2.Layout.FixedAssignment Nat)
    (member : write ∈ Halo2.Layout.tableFixed scalarNat 8183 ops) :
    write.1 < 16 ∧ write.2.1 < 8183 := by
  induction ops with
  | nil => simp [Halo2.Layout.tableFixed] at member
  | cons op rest ih =>
    rw [List.forall_cons] at tables
    obtain ⟨head,tail⟩ := tables
    cases op with
    | region name body | constrainInstance cell column row => exact ih tail member
    | loadTable table values =>
      change table.inner.index < 16 ∧ values.length < 8183 at head
      simp only [Halo2.Layout.tableFixed, List.mem_append] at member
      rcases member with (block | fill) | later
      · obtain ⟨row,bound,rfl⟩ := List.mem_map.mp block
        have hr := List.mem_range.mp bound
        exact ⟨head.1,by dsimp; omega⟩
      · by_cases empty : values.isEmpty = true
        · simp [empty] at fill
        rw [ite_eq_right empty] at fill
        obtain ⟨row,bound,rfl⟩ := List.mem_map.mp fill
        have hr := List.mem_range.mp bound
        exact ⟨head.1,by dsimp; omega⟩
      · exact ih tail later

theorem region_fixed_bounds (write : Halo2.Layout.FixedAssignment Nat)
    (member : write ∈ Halo2.Layout.regionAssignFixed scalarNat
      (SimpleFloorPlanner.starts (Synthesis.operations activation))
      (indexedRegions (Synthesis.operations activation) 0).1) :
    write.1 < 16 ∧ write.2.1 < 8183 := by
  obtain ⟨original,originalMember,rfl⟩ := regionAssignFixed_refines _ _ _ write member
  obtain ⟨index,body,column,row,region,assigned,hcolumn,hrow⟩ :=
    Halo2.Layout.mem_regionAssignments _ _ originalMember
  have shape := source_shape_bounds (measureRegion index body)
    (List.mem_map.mpr ⟨(index,body),region,rfl⟩)
  have total : (SimpleFloorPlanner.starts (Synthesis.operations activation)).getD index 0 +
      (measureRegion index body).rowCount ≤ 8183 := shape.2.1
  have touched : .column .fixed column.index ∈ (measureRegion index body).columns := by
    exact mem_regionSynthesisSummary_columns_of_mem body (.assignFixed column row original.2.2)
      assigned (.column .fixed column.index) (by simp [regionOperationShapeColumns])
  have columnBound := List.forall_iff_forall_mem.mp shape.2.2 _ touched
  have rowBound := regionOperationRowExtent_le_synthesisSummary_of_mem body
    (.assignFixed column row original.2.2) assigned
  change column.index < 16 at columnBound
  change row + 1 ≤ (measureRegion index body).rowCount at rowBound
  change original.1 < 16 ∧ original.2.1 < 8183
  rw [hcolumn,hrow]
  exact ⟨columnBound,by dsimp only [Halo2.Layout.place]; omega⟩

theorem selector_bounds (entry : Nat × Nat)
    (member : entry ∈ Halo2.activations
      (SimpleFloorPlanner.starts (Synthesis.operations activation))
      (indexedRegions (Synthesis.operations activation) 0).1) :
    entry.1 < 16 ∧ entry.2 < 8183 := by
  obtain ⟨selector,absolute⟩ := entry
  obtain ⟨index,body,operation,row,region,assigned,active,rfl⟩ :=
    (mem_activations_iff _ _ selector absolute).mp member
  have shape := source_shape_bounds (measureRegion index body)
    (List.mem_map.mpr ⟨(index,body),region,rfl⟩)
  have total : (SimpleFloorPlanner.starts (Synthesis.operations activation)).getD index 0 +
      (measureRegion index body).rowCount ≤ 8183 := shape.2.1
  have touched := selector_mem_measureRegion_of_activatesSelectorAt index body assigned active
  have rowBound := row_lt_measureRegion_of_activatesSelectorAt index body assigned active
  have columnBound := List.forall_iff_forall_mem.mp shape.2.2 _ touched
  exact ⟨columnBound,by dsimp; omega⟩

private theorem config_fixed :
    (CertifiedCircuit.layoutConfig configured 13).numFixed = 16 := by
  exact congrArg ConfigureCounts.numFixedColumns Admission.counts

private theorem config_selectors :
    (CertifiedCircuit.layoutConfig configured 13).numSelectors = 16 := by
  exact congrArg ConfigureCounts.numSelectors Admission.counts

def certificate : Layout.CertifiedLayout (Synthesis.operations activation)
    (CertifiedCircuit.permutationColumns configured)
    (CertifiedCircuit.layoutConfig configured 13) .simple where
  fixedCertificate := {
    sourceLawful := {
      bounds := by
        intro write member
        rw [Admission.usableRows,config_fixed]
        replace member := Layout.mem_sourceFixedWrites_none Admission.layoutConstant member
        change write ∈ Halo2.Layout.tableFixed scalarNat
            (CertifiedCircuit.layoutConfig configured 13).usableRows (Synthesis.operations activation) ++
          Halo2.Layout.regionAssignFixed scalarNat
            (SimpleFloorPlanner.starts (Synthesis.operations activation))
            (indexedRegions (Synthesis.operations activation) 0).1 at member
        rw [Admission.usableRows] at member
        rcases List.mem_append.mp member with table | region
        · exact table_bounds _ (Admission.source_tables ⟨8,16,2,16⟩ rfl) write table
        · exact region_fixed_bounds write region }
    usable_le_rows := by rw [Admission.usableRows]; decide
    activationBounds := by
      intro entry member
      rw [Admission.usableRows,config_selectors]
      rw [Admission.layoutConstant] at member
      exact selector_bounds entry member }

end Midnight.SHA256.Admission.Physical
