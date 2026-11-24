import Midnight.SHA256.WitnessErasure
import Midnight.Chips.Relocation

/-! Structural properties insensitive to the erased advice recipes. These
lemmas do not erase or replace witness-extension obligations. -/
namespace Midnight.SHA256.WitnessErasure
open Halo2

@[simp] theorem region_keygen (op : RegionOperation F)
    (gates : List (Gate F)) (lookups : List (LookupArgument F))
    (fixed : List (Column .fixed)) (permutation : List AnyColumn) :
    (regionOperation op).KeygenRegistered gates lookups fixed permutation ↔
      op.KeygenRegistered gates lookups fixed permutation := by
  cases op <;> rfl

@[simp] theorem operation_keygen (op : Operation F)
    (gates : List (Gate F)) (lookups : List (LookupArgument F))
    (fixed : List (Column .fixed)) (permutation : List AnyColumn) :
    (operation op).KeygenRegistered gates lookups fixed permutation ↔
      op.KeygenRegistered gates lookups fixed permutation := by
  cases op <;> simp [operation, Operation.KeygenRegistered, List.forall_iff_forall_mem]

theorem keygen (ops : Operations F)
    (gates : List (Gate F)) (lookups : List (LookupArgument F))
    (fixed : List (Column .fixed)) (permutation : List AnyColumn) :
    (operations ops).KeygenRegistered gates lookups fixed permutation ↔
      ops.KeygenRegistered gates lookups fixed permutation := by
  simp [operations, Operations.KeygenRegistered, List.forall_iff_forall_mem]

@[simp] theorem region_assigned (region : Nat) (op : RegionOperation F) :
    (regionOperation op).assignedCells region = op.assignedCells region := by
  cases op <;> rfl

@[simp] theorem region_assignedAfter (region : Nat) (available : List Cell) (ops : RegionOperations F) :
    RegionOperations.assignedCellsAfter region available (ops.map regionOperation) =
      ops.assignedCellsAfter region available := by
  induction ops generalizing available with
  | nil => rfl
  | cons op rest ih =>
      simp only [List.map_cons, RegionOperations.assignedCellsAfter, List.foldl_cons] at *
      rw [region_assigned]
      exact ih _

theorem region_copyAssigned (region : Nat) (available : List Cell) (ops : RegionOperations F) :
    RegionOperations.CopyCellsAssignedFrom region available (ops.map regionOperation) ↔
      ops.CopyCellsAssignedFrom region available := by
  induction ops generalizing available with
  | nil => rfl
  | cons op rest ih =>
      cases op <;> simp only [List.map_cons, regionOperation,
        RegionOperations.copyCellsAssignedFrom_assignAdvice_iff,
        RegionOperations.copyCellsAssignedFrom_assignFixed_iff,
        RegionOperations.copyCellsAssignedFrom_enableGate_iff,
        RegionOperations.copyCellsAssignedFrom_enableLookup_iff,
        RegionOperations.copyCellsAssignedFrom_constrainEqual_iff,
        RegionOperations.copyCellsAssignedFrom_constrainConstant_iff,
        RegionOperations.copyCellsAssignedFrom_constrainInstance_iff, ih]

theorem copyAssigned (region : Nat) (available : List Cell) (ops : Operations F) :
    (operations ops).CopyCellsAssignedFrom region available ↔
      ops.CopyCellsAssignedFrom region available := by
  induction ops generalizing region available with
  | nil => rfl
  | cons op rest ih =>
      cases op <;> simp only [operations, List.map_cons, operation,
        Operations.copyCellsAssignedFrom_region_iff,
        Operations.copyCellsAssignedFrom_constrainInstance_iff,
        Operations.copyCellsAssignedFrom_loadTable_iff, region_assignedAfter, region_copyAssigned] at *
        <;> rw [ih]

@[simp] theorem fixed_member (ops : RegionOperations F)
    (column : Column .fixed) (row : Nat) (value : F) :
    .assignFixed column row value ∈ ops.map regionOperation ↔
      .assignFixed column row value ∈ ops := by
  induction ops with
  | nil => simp
  | cons op rest ih =>
      cases op <;> simp only [List.map_cons, List.mem_cons, regionOperation, ih, reduceCtorEq, false_or]

theorem region_fixedAgree (ops : RegionOperations F) :
    RegionOperations.FixedAssignmentsAgree (ops.map regionOperation) ↔ ops.FixedAssignmentsAgree := by
  simp only [RegionOperations.FixedAssignmentsAgree, fixed_member]

@[simp] theorem region_fixedColumns (ops : RegionOperations F) :
    RegionOperations.fixedColumns (ops.map regionOperation) = ops.fixedColumns := by
  induction ops with
  | nil => rfl
  | cons op rest ih => cases op <;> simp_all [RegionOperations.fixedColumns, regionOperation]

@[simp] theorem loadedTables (ops : Operations F) :
    (operations ops).loadedTableColumns = ops.loadedTableColumns := by
  induction ops with
  | nil => rfl
  | cons op rest ih =>
      cases op with
      | region name body => exact ih
      | constrainInstance source column row => exact ih
      | loadTable column values =>
          cases values with
          | nil => exact ih
          | cons value values => exact congrArg (column.inner :: ·) ih

@[simp] theorem regionFixedColumns (ops : Operations F) :
    (operations ops).regionFixedColumns = ops.regionFixedColumns := by
  induction ops with
  | nil => rfl
  | cons op rest ih => cases op <;> simp_all [operations, Operations.regionFixedColumns, operation]

@[simp] theorem operation_fixedAgree (op : Operation F) :
    (operation op).FixedAssignmentsAgree ↔ op.FixedAssignmentsAgree := by
  cases op <;> simp [operation, Operation.FixedAssignmentsAgree, region_fixedAgree]

theorem fixedWrites (ops : Operations F) (constants : List (Column .fixed)) :
    (operations ops).FixedWritesLawful constants ↔ ops.FixedWritesLawful constants := by
  constructor <;> intro law
  · exact ⟨by simpa [operations, List.forall_iff_forall_mem] using law.regionAssignmentsAgree,
      by simpa using law.loadedTableColumns_nodup,
      by simpa using law.loadedTableColumns_disjoint_regionFixedColumns,
      by simpa using law.loadedTableColumns_disjoint_constantColumns⟩
  · exact ⟨by simpa [operations, List.forall_iff_forall_mem] using law.regionAssignmentsAgree,
      by simpa using law.loadedTableColumns_nodup,
      by simpa using law.loadedTableColumns_disjoint_regionFixedColumns,
      by simpa using law.loadedTableColumns_disjoint_constantColumns⟩

@[simp] theorem region_lookup (op : RegionOperation F) :
    (regionOperation op).LookupActivationWellFormed ↔ op.LookupActivationWellFormed := by
  cases op <;> rfl

@[simp] theorem operation_lookup (op : Operation F) :
    (operation op).LookupActivationsWellFormed ↔ op.LookupActivationsWellFormed := by
  cases op <;> simp [operation, Operation.LookupActivationsWellFormed,
    RegionOperations.LookupActivationsWellFormed, List.forall_iff_forall_mem]

theorem lookup (ops : Operations F) :
    (operations ops).LookupActivationsWellFormed ↔ ops.LookupActivationsWellFormed := by
  simp [operations, Operations.LookupActivationsWellFormed, List.forall_iff_forall_mem]

@[simp] theorem regionCount (ops : Operations F) :
    (operations ops).regionCount = ops.regionCount := by
  induction ops with
  | nil => rfl
  | cons op rest ih => cases op <;> simp_all [operations, Operations.regionCount, operation]

@[simp] theorem region_operationSummary (op : RegionOperation F) :
    FloorPlanner.RegionSynthesisSummary.ofOperation (regionOperation op) =
      FloorPlanner.RegionSynthesisSummary.ofOperation op := by
  cases op <;> rfl

@[simp] theorem region_summary (ops : RegionOperations F) :
    FloorPlanner.regionSynthesisSummary (ops.map regionOperation) =
      FloorPlanner.regionSynthesisSummary ops := by
  induction ops with
  | nil => rfl
  | cons op rest ih =>
      simp only [List.map_cons, FloorPlanner.regionSynthesisSummary, region_operationSummary, ih]

@[simp] theorem summary (ops : Operations F) :
    FloorPlanner.synthesisSummary (operations ops) = FloorPlanner.synthesisSummary ops := by
  induction ops with
  | nil => rfl
  | cons op rest ih =>
      cases op <;> simp only [operations, List.map_cons, operation, FloorPlanner.synthesisSummary,
        region_summary] at * <;> rw [ih]

end Midnight.SHA256.WitnessErasure
