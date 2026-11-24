import Clean.Halo2.Operations.FixedWrites
import Clean.Halo2.Operations.LookupSelectors

/-! Region-index relocation of structural operations. Assignment coordinates,
configured equations and lookup tuples are unchanged; explicit copy endpoints
move together. Advice programs are left untouched, so this is a structural
transformation, not a claim about relocated witness execution. -/
namespace Midnight.Chips.Relocation
open Halo2
variable {F : Type}

def cell (offset : Nat) (source : Cell) : Cell :=
  { source with regionIndex := offset + source.regionIndex }

@[simp] theorem cell_column (offset : Nat) (source : Cell) :
    (cell offset source).column = source.column := rfl

@[simp] theorem cell_of (offset region row : Nat) {kind : ColumnKind} (column : Column kind) :
    cell offset (.of region row column) = .of (offset + region) row column := rfl

def regionOperation (offset : Nat) : RegionOperation F → RegionOperation F
  | .constrainEqual left right => .constrainEqual (cell offset left) (cell offset right)
  | .constrainConstant source value => .constrainConstant (cell offset source) value
  | .constrainInstance source column row => .constrainInstance (cell offset source) column row
  | other => other

def regionOperations (offset : Nat) (source : RegionOperations F) : RegionOperations F :=
  source.map (regionOperation offset)

def operation (offset : Nat) : Operation F → Operation F
  | .region name body => .region name (regionOperations offset body)
  | .constrainInstance source column row => .constrainInstance (cell offset source) column row
  | .loadTable column values => .loadTable column values

def operations (offset : Nat) (source : Operations F) : Operations F :=
  source.map (operation offset)

@[simp] theorem region_keygen (offset : Nat) (op : RegionOperation F)
    (gates : List (Gate F)) (lookups : List (LookupArgument F))
    (fixed : List (Column .fixed)) (permutation : List AnyColumn) :
    (regionOperation offset op).KeygenRegistered gates lookups fixed permutation ↔
      op.KeygenRegistered gates lookups fixed permutation := by
  cases op <;> rfl

@[simp] theorem operation_keygen (offset : Nat) (op : Operation F)
    (gates : List (Gate F)) (lookups : List (LookupArgument F))
    (fixed : List (Column .fixed)) (permutation : List AnyColumn) :
    (operation offset op).KeygenRegistered gates lookups fixed permutation ↔
      op.KeygenRegistered gates lookups fixed permutation := by
  cases op <;> simp [operation, regionOperations, Operation.KeygenRegistered, List.forall_iff_forall_mem]

theorem keygen (offset : Nat) (ops : Operations F)
    (gates : List (Gate F)) (lookups : List (LookupArgument F))
    (fixed : List (Column .fixed)) (permutation : List AnyColumn) :
    (operations offset ops).KeygenRegistered gates lookups fixed permutation ↔
      ops.KeygenRegistered gates lookups fixed permutation := by
  simp [operations, Operations.KeygenRegistered, List.forall_iff_forall_mem]

theorem region_assigned (offset region : Nat) (op : RegionOperation F) :
    (regionOperation offset op).assignedCells (offset + region) =
      (op.assignedCells region).map (cell offset) := by
  cases op <;> rfl

theorem region_assignedAfter (offset region : Nat) (available : List Cell) (ops : RegionOperations F) :
    (regionOperations offset ops).assignedCellsAfter (offset + region) (available.map (cell offset)) =
      (ops.assignedCellsAfter region available).map (cell offset) := by
  induction ops generalizing available with
  | nil => rfl
  | cons op rest ih =>
    simp only [regionOperations, List.map_cons, RegionOperations.assignedCellsAfter, List.foldl_cons] at *
    rw [region_assigned, ← List.map_append]
    exact ih _

theorem region_copyAssigned (offset region : Nat) (available : List Cell) (ops : RegionOperations F)
    (lawful : ops.CopyCellsAssignedFrom region available) :
    (regionOperations offset ops).CopyCellsAssignedFrom (offset + region) (available.map (cell offset)) := by
  induction lawful with
  | nil available => exact .nil _
  | assignAdvice available column row compute rest next ih =>
      exact .assignAdvice _ _ _ _ _ ih
  | assignFixed available column row value rest next ih =>
      exact .assignFixed _ _ _ _ _ ih
  | enableGate available gate row rest next ih => exact .enableGate _ _ _ _ ih
  | enableLookup available lookup selectors row rest next ih => exact .enableLookup _ _ _ _ _ ih
  | constrainEqual available left right rest hl hr next ih =>
      exact .constrainEqual _ _ _ _ (List.mem_map.mpr ⟨left,hl,rfl⟩)
        (List.mem_map.mpr ⟨right,hr,rfl⟩) ih
  | constrainConstant available source value rest hs next ih =>
      exact .constrainConstant _ _ _ _ (List.mem_map.mpr ⟨source,hs,rfl⟩) ih
  | constrainInstance available source column row rest hs next ih =>
      exact .constrainInstance _ _ _ _ _ (List.mem_map.mpr ⟨source,hs,rfl⟩) ih

theorem copyAssigned (offset region : Nat) (available : List Cell) (ops : Operations F)
    (lawful : ops.CopyCellsAssignedFrom region available) :
    (operations offset ops).CopyCellsAssignedFrom (offset + region) (available.map (cell offset)) := by
  induction lawful with
  | nil region available => exact .nil _ _
  | region region available name body rest head tail ih =>
      apply Operations.CopyCellsAssignedFrom.region
      · exact region_copyAssigned offset region available body head
      · simpa only [operations, region_assignedAfter, Nat.add_assoc] using ih
  | constrainInstance region available source column row rest hs next ih =>
      exact .constrainInstance _ _ _ _ _ _ (List.mem_map.mpr ⟨source,hs,rfl⟩) ih
  | loadTable region available column values rest next ih => exact .loadTable _ _ _ _ _ ih

@[simp] theorem fixed_member (offset : Nat) (ops : RegionOperations F)
    (column : Column .fixed) (row : Nat) (value : F) :
    .assignFixed column row value ∈ regionOperations offset ops ↔
      .assignFixed column row value ∈ ops := by
  induction ops with
  | nil => simp [regionOperations]
  | cons op rest ih =>
      change .assignFixed column row value ∈ regionOperation offset op :: regionOperations offset rest ↔ _
      cases op <;> simp only [List.mem_cons, regionOperation, ih, reduceCtorEq, false_or]

theorem region_fixedAgree (offset : Nat) (ops : RegionOperations F) :
    (regionOperations offset ops).FixedAssignmentsAgree ↔ ops.FixedAssignmentsAgree := by
  simp only [RegionOperations.FixedAssignmentsAgree, fixed_member]

@[simp] theorem region_fixedColumns (offset : Nat) (ops : RegionOperations F) :
    (regionOperations offset ops).fixedColumns = ops.fixedColumns := by
  induction ops with
  | nil => rfl
  | cons op rest ih => cases op <;> simp_all [regionOperations, RegionOperations.fixedColumns, regionOperation]

@[simp] theorem loadedTables (offset : Nat) (ops : Operations F) :
    (operations offset ops).loadedTableColumns = ops.loadedTableColumns := by
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

@[simp] theorem regionFixedColumns (offset : Nat) (ops : Operations F) :
    (operations offset ops).regionFixedColumns = ops.regionFixedColumns := by
  induction ops with
  | nil => rfl
  | cons op rest ih => cases op <;> simp_all [operations, Operations.regionFixedColumns, operation]

@[simp] theorem operation_fixedAgree (offset : Nat) (op : Operation F) :
    (operation offset op).FixedAssignmentsAgree ↔ op.FixedAssignmentsAgree := by
  cases op <;> simp [operation, Operation.FixedAssignmentsAgree, region_fixedAgree]

theorem fixedWrites (offset : Nat) (ops : Operations F) (constants : List (Column .fixed)) :
    (operations offset ops).FixedWritesLawful constants ↔ ops.FixedWritesLawful constants := by
  constructor <;> intro law
  · exact ⟨by simpa [operations, List.forall_iff_forall_mem] using law.regionAssignmentsAgree,
      by simpa using law.loadedTableColumns_nodup,
      by simpa using law.loadedTableColumns_disjoint_regionFixedColumns,
      by simpa using law.loadedTableColumns_disjoint_constantColumns⟩
  · exact ⟨by simpa [operations, List.forall_iff_forall_mem] using law.regionAssignmentsAgree,
      by simpa using law.loadedTableColumns_nodup,
      by simpa using law.loadedTableColumns_disjoint_regionFixedColumns,
      by simpa using law.loadedTableColumns_disjoint_constantColumns⟩

@[simp] theorem region_lookup (offset : Nat) (op : RegionOperation F) :
    (regionOperation offset op).LookupActivationWellFormed ↔ op.LookupActivationWellFormed := by
  cases op <;> rfl

@[simp] theorem operation_lookup (offset : Nat) (op : Operation F) :
    (operation offset op).LookupActivationsWellFormed ↔ op.LookupActivationsWellFormed := by
  cases op <;> simp [operation, regionOperations, Operation.LookupActivationsWellFormed,
    RegionOperations.LookupActivationsWellFormed, List.forall_iff_forall_mem]

theorem lookup (offset : Nat) (ops : Operations F) :
    (operations offset ops).LookupActivationsWellFormed ↔ ops.LookupActivationsWellFormed := by
  simp [operations, Operations.LookupActivationsWellFormed, List.forall_iff_forall_mem]

@[simp] theorem regionCount (offset : Nat) (ops : Operations F) :
    (operations offset ops).regionCount = ops.regionCount := by
  induction ops with
  | nil => rfl
  | cons op rest ih => cases op <;> simp_all [operations, Operations.regionCount, operation]

@[simp] theorem region_operationSummary (offset : Nat) (op : RegionOperation F) :
    FloorPlanner.RegionSynthesisSummary.ofOperation (regionOperation offset op) =
      FloorPlanner.RegionSynthesisSummary.ofOperation op := by
  cases op <;> rfl

@[simp] theorem region_summary (offset : Nat) (ops : RegionOperations F) :
    FloorPlanner.regionSynthesisSummary (regionOperations offset ops) =
      FloorPlanner.regionSynthesisSummary ops := by
  induction ops with
  | nil => rfl
  | cons op rest ih =>
      change (FloorPlanner.RegionSynthesisSummary.ofOperation (regionOperation offset op)).combine
        (FloorPlanner.regionSynthesisSummary (regionOperations offset rest)) = _
      rw [region_operationSummary, ih]
      rfl

@[simp] theorem summary (offset : Nat) (ops : Operations F) :
    FloorPlanner.synthesisSummary (operations offset ops) = FloorPlanner.synthesisSummary ops := by
  induction ops with
  | nil => rfl
  | cons op rest ih =>
      cases op <;> simp only [operations, List.map_cons, operation, FloorPlanner.synthesisSummary,
        region_summary] at * <;> rw [ih]

end Midnight.Chips.Relocation
