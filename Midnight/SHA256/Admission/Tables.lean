import Midnight.SHA256.SynthesisLayout
import Midnight.SHA256.WitnessInitial
import Midnight.Chips.OperationsLawful

/-! The actual five source table loads are allocated and leave a usable default-
fill row. The schedule itself emits regions and public copies, never tables. -/
namespace Midnight.SHA256.Admission
open Halo2 Midnight.Chips
attribute [local irreducible] Synthesis.schedule byteRangeRows spreadRows

theorem source_tables (counts : ConfigureCounts) (fixedCount : counts.numFixedColumns = 16) :
    (Synthesis.operations activation).Forall (OperationsLawful.TableValid counts 8183) := by
  change (Synthesis.toOperations activation ++ Synthesis.tableOperations).Forall _
  rw [List.forall_append]
  constructor
  · apply List.forall_iff_forall_mem.mpr
    intro op member
    obtain ⟨step, _, rfl⟩ := List.mem_map.mp member
    cases step <;> trivial
  · simp only [Synthesis.tableOperations, List.forall_cons, List.forall_nil,
      OperationsLawful.TableValid, List.length_map, fixedCount, WitnessInitial.range_length,
      WitnessInitial.spread_length]
    decide

private theorem map_isEmpty {α β : Type} {xs : List α} {n : Nat} (length : xs.length = n + 1)
    (f : α → β) : (xs.map f).isEmpty = false := by
  cases xs with
  | nil => simp at length
  | cons _ _ => rfl

theorem source_tableColumns :
    OperationsLawful.tableColumns (Synthesis.operations activation) = [11, 12, 13, 14, 15] := by
  change OperationsLawful.tableColumns
    (Synthesis.toOperations activation ++ Synthesis.tableOperations) = _
  have regions : OperationsLawful.tableColumns (Synthesis.toOperations activation) = [] := by
    apply List.filterMap_eq_nil_iff.mpr
    intro op member
    obtain ⟨step, _, rfl⟩ := List.mem_map.mp member
    cases step <;> rfl
  rw [OperationsLawful.tableColumns, List.filterMap_append, ← OperationsLawful.tableColumns, regions,
    List.nil_append]
  simp only [Synthesis.tableOperations, List.filterMap_cons,
    List.filterMap_nil, map_isEmpty WitnessInitial.range_length,
    map_isEmpty WitnessInitial.spread_length, Bool.false_eq_true, ↓reduceIte]

theorem source_tablesDistinct :
    (OperationsLawful.tableColumns (Synthesis.operations activation)).Nodup := by
  rw [source_tableColumns]
  decide

end Midnight.SHA256.Admission
