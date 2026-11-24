import Midnight.Math.Witness.Operations
import Clean.Halo2.Operations.FixedWrites

/-! Connect Clean's fixed-column ownership metadata to the witness executor.
This avoids a second circuit-specific table/write separation assumption. -/
namespace Midnight.Math.Witness.Operations
open Halo2 Execute
variable {F : Type}

theorem regionAssignments_column (place : RegionIndex → Nat) (self : RegionIndex)
    (ops : RegionOperations F) (assignment : Assignment F)
    (member : assignment ∈ regionAssignments place self ops) :
    assignment.destination.1.kind = .advice ∨
      ∃ column ∈ ops.fixedColumns, assignment.destination.1 = column.toAny := by
  induction ops with
  | nil => simp [regionAssignments] at member
  | cons op rest ih =>
    cases op with
    | assignAdvice column row program =>
      rcases List.mem_cons.mp member with same | tail
      · subst assignment; exact Or.inl rfl
      · exact ih tail
    | assignFixed column row value =>
      rcases List.mem_cons.mp member with same | tail
      · subst assignment
        exact Or.inr ⟨column, List.mem_cons_self, rfl⟩
      · rcases ih tail with advice | ⟨col,present,same⟩
        · exact Or.inl advice
        · exact Or.inr ⟨col, List.mem_cons_of_mem column present, same⟩
    | _ => exact ih member

theorem assignments_column (place : RegionIndex → Nat) (self : RegionIndex)
    (ops : Operations F) (assignment : Assignment F)
    (member : assignment ∈ assignments place ops self) :
    assignment.destination.1.kind = .advice ∨
      ∃ column ∈ ops.regionFixedColumns, assignment.destination.1 = column.toAny := by
  induction ops generalizing self with
  | nil => simp [assignments] at member
  | cons op rest ih =>
    cases op with
    | region name body =>
      rcases List.mem_append.mp member with head | tail
      · rcases regionAssignments_column place self body assignment head with advice | ⟨col,present,same⟩
        · exact Or.inl advice
        · exact Or.inr ⟨col, List.mem_append_left _ present, same⟩
      · rcases ih (self+1) tail with advice | ⟨col,present,same⟩
        · exact Or.inl advice
        · exact Or.inr ⟨col, List.mem_append_right _ present, same⟩
    | _ => exact ih self member

/-- The source's fixed-write discipline protects initially loaded table cells
from all subsequent scalar assignments, for any physical placement. -/
theorem assignments_separate_tables (place : RegionIndex → Nat) (self : RegionIndex)
    (ops : Operations F) (constants : List (Column .fixed))
    (lawful : ops.FixedWritesLawful constants) :
    ∀ assignment ∈ assignments place ops self,
      assignment.destination.1 ∉ ops.loadedTableColumns.map Column.toAny := by
  intro assignment member table
  obtain ⟨tableColumn,inTables,same⟩ := List.mem_map.mp table
  rcases assignments_column place self ops assignment member with advice | ⟨column,inRegions,columnEq⟩
  · have kinds := congrArg AnyColumn.kind same
    rw [advice] at kinds
    cases kinds
  · have equal : tableColumn = column := by
      cases tableColumn
      cases column
      simpa only [Column.toAny, AnyColumn.mk.injEq, true_and, Column.mk.injEq] using same.trans columnEq
    subst column
    exact List.disjoint_left.mp lawful.loadedTableColumns_disjoint_regionFixedColumns inTables inRegions

end Midnight.Math.Witness.Operations
