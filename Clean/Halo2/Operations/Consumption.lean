module

public import Clean.Halo2.Operations.Copy
public import Clean.Halo2.WitnessSupport

@[expose] public section

/-!
# Witness reads, and copies and reads together

`RegionOperation.Reads` is the second instance of `AssignedFrom`: an advice assignment reads
the cells of a certified support of its witness program (`WitnessFunctionSupport`), and the
other operations do not read any cells. The read set of a native closure is never computed;
it is whatever a support rule for the closure's shape supplies. `RegionOperation.Consumes` is
the product of copies and reads, so provenance for it is provenance for each.
-/

namespace Halo2

variable {F : Type} [FiniteField F]

/-- An advice assignment reads the advice cells of a certified support of its witness program
(non-advice fixed and instance cells are supplied by `Determined.nonAdvice`); the other
operations do not read any cells. -/
def RegionOperation.Reads : RegionOperation F → Language Cell
  | .assignAdvice _ _ program =>
      {cells | ∃ reads : List (AssignedCell F),
        WitnessFunctionSupport reads (programFunction program) ∧
          ∀ cell ∈ reads, cell.cell.column.kind = .advice → cell.cell ∈ cells}
  | _ => 1

/-- Copies and reads together: everything an operation needs to find already assigned. -/
def RegionOperation.Consumes : Consumption F := RegionOperation.Copies * RegionOperation.Reads

namespace RegionOperation

variable (available : List Cell)

@[keygen_norm]
theorem mem_reads_assignAdvice_iff (column : Column .advice) (row : ℕ) (program : WitgenIR F 1)
    (cells : List Cell) :
    cells ∈ Reads (.assignAdvice column row program) ↔
      ∃ reads : List (AssignedCell F),
        WitnessFunctionSupport reads (programFunction program) ∧
          ∀ cell ∈ reads, cell.cell.column.kind = .advice → cell.cell ∈ cells :=
  Iff.rfl

omit [FiniteField F] in
@[keygen_norm]
theorem assignedCell_of_column_kind (self : RegionIndex) (row : ℕ)
    {kind : ColumnKind} (column : Column kind) :
    (AssignedCell.of (F := F) self row column).cell.column.kind = kind := rfl

@[keygen_norm]
theorem column_toAny_kind {kind : ColumnKind} (column : Column kind) :
    column.toAny.kind = kind := rfl

@[keygen_norm]
theorem columnKind_fixed_eq_advice : (ColumnKind.fixed = ColumnKind.advice) ↔ False := by
  simp

@[keygen_norm]
theorem columnKind_instance_eq_advice : (ColumnKind.instance = ColumnKind.advice) ↔ False := by
  simp

@[keygen_norm]
theorem columnKind_advice_eq_advice : (ColumnKind.advice = ColumnKind.advice) ↔ True := by
  simp

omit [FiniteField F] in
@[keygen_norm ↓]
theorem forall_advice_mem_nil {P : Cell → Prop} :
    (∀ cell ∈ ([] : List (AssignedCell F)), cell.cell.column.kind = .advice → P cell.cell) ↔
      True := by
  simp

omit [FiniteField F] in
@[keygen_norm ↓]
theorem forall_advice_mem_cons {P : Cell → Prop} (head : AssignedCell F)
    (tail : List (AssignedCell F)) :
    (∀ cell ∈ head :: tail, cell.cell.column.kind = .advice → P cell.cell) ↔
      (head.cell.column.kind = .advice → P head.cell) ∧
        ∀ cell ∈ tail, cell.cell.column.kind = .advice → P cell.cell := by
  simp

omit [FiniteField F] in
@[keygen_norm ↓]
theorem forall_advice_mem_append {P : Cell → Prop} (left right : List (AssignedCell F)) :
    (∀ cell ∈ left ++ right, cell.cell.column.kind = .advice → P cell.cell) ↔
      (∀ cell ∈ left, cell.cell.column.kind = .advice → P cell.cell) ∧
        ∀ cell ∈ right, cell.cell.column.kind = .advice → P cell.cell := by
  simp [or_imp, forall_and]

@[keygen_norm]
theorem reads_assignFixed (column : Column .fixed) (row : ℕ) (value : F) :
    Reads (.assignFixed column row value) = 1 := rfl

@[keygen_norm]
theorem reads_enableGate (gate : Gate F) (row : ℕ) :
    Reads (.enableGate gate row) = 1 := rfl

@[keygen_norm]
theorem reads_enableLookup (argument : LookupArgument F) (selectors : List Selector) (row : ℕ) :
    Reads (.enableLookup argument selectors row) = 1 := rfl

@[keygen_norm]
theorem reads_constrainEqual (left right : Cell) :
    Reads (F := F) (.constrainEqual left right) = 1 := rfl

@[keygen_norm]
theorem reads_constrainConstant (cell : Cell) (value : F) :
    Reads (.constrainConstant cell value) = 1 := rfl

@[keygen_norm]
theorem reads_constrainInstance (cell : Cell) (column : Column .instance) (row : ℕ) :
    Reads (F := F) (.constrainInstance cell column row) = 1 := rfl

/-- Reading from a cell state: a certified support of the program whose advice cells are within
`available` for an advice assignment (fixed and instance reads are already determined), and nothing
for the other operations. -/
@[keygen_norm, keygen_spine]
theorem consumesFrom_reads_iff (operation : RegionOperation F) :
    ConsumesFrom Reads available operation ↔
      match operation with
      | .assignAdvice _ _ program =>
          ∃ reads : List (AssignedCell F),
            WitnessFunctionSupport reads (programFunction program) ∧
              ∀ cell ∈ reads, cell.cell.column.kind = .advice → cell.cell ∈ available
      | _ => True := by
  cases operation
  case assignAdvice column row program =>
    simp only [ConsumesFrom, mem_reads_assignAdvice_iff]
    constructor
    · rintro ⟨cs, ⟨reads, hsupport, hcover⟩, havailable⟩
      exact ⟨reads, hsupport, fun cell hcell hadv => havailable _ (hcover cell hcell hadv)⟩
    · rintro ⟨reads, hsupport, havailable⟩
      exact ⟨available, ⟨reads, hsupport, havailable⟩, fun _ h => h⟩
  all_goals exact ⟨fun _ => trivial, fun _ => ⟨[], Language.nil_mem_one, fun _ h => nomatch h⟩⟩

/-- Consuming from a cell state is copying from it and reading from it. -/
@[keygen_norm, keygen_spine]
theorem consumesFrom_consumes_iff (operation : RegionOperation F) :
    ConsumesFrom Consumes available operation ↔
      ConsumesFrom Copies available operation ∧ ConsumesFrom Reads available operation :=
  consumesFrom_mul_iff Copies Reads available operation

/-- Consuming nothing is copying nothing and reading nothing. -/
@[keygen_norm]
theorem nil_mem_consumes_iff (operation : RegionOperation F) :
    [] ∈ Consumes operation ↔ [] ∈ Copies operation ∧ [] ∈ Reads operation :=
  Consumption.nil_mem_mul_iff Copies Reads operation

/-- Under combined provenance, a copy-like operation consumes at least its endpoints. -/
theorem copiedCells_subset_of_consumes
    (operation : RegionOperation F) (cells : List Cell) (hconsumes : cells ∈ Consumes operation) :
    ∀ cell ∈ operation.copiedCells, cell ∈ cells := by
  intro cell hcell
  rw [Consumes, Consumption.mul_apply, Language.mem_mul] at hconsumes
  obtain ⟨copied, hcopied, reads, _, rfl⟩ := hconsumes
  rw [mem_copies_iff] at hcopied
  subst hcopied
  exact List.mem_append_left _ hcell

end RegionOperation

def RegionOperations.ConsumedCellsAssigned (operations : RegionOperations F)
    (region : RegionIndex) (cells : List Cell) : Prop :=
  AssignedFrom RegionOperation.Consumes region cells operations

def Operations.ConsumedCellsAssigned (operations : Operations F)
    (initialRegion : RegionIndex) (cells : List Cell) : Prop :=
  AssignedFrom RegionOperation.Consumes initialRegion cells operations

theorem Operations.copyCellsCovered_of_consumed
    (operations : Operations F) (initialRegion : RegionIndex) (cells : List Cell)
    (hassigned : operations.ConsumedCellsAssigned initialRegion cells) :
    operations.CopyCellsCovered initialRegion cells :=
  operations.copyCellsCovered_of_assignedFrom RegionOperation.copiedCells_subset_of_consumes
    initialRegion cells hassigned

/-- Combined region provenance is copy provenance together with read provenance. -/
theorem RegionOperations.assignedFrom_consumes_iff (region : RegionIndex)
    (available : List Cell) (operations : RegionOperations F) :
    AssignedFrom RegionOperation.Consumes region available operations ↔
      AssignedFrom RegionOperation.Copies region available operations ∧
        AssignedFrom RegionOperation.Reads region available operations :=
  assignedFrom_mul_iff RegionOperation.Copies RegionOperation.Reads region available operations

/-- Combined layouter provenance is copy provenance together with read provenance. -/
theorem Operations.assignedFrom_consumes_iff (region : RegionIndex)
    (available : List Cell) (operations : Operations F) :
    AssignedFrom RegionOperation.Consumes region available operations ↔
      AssignedFrom RegionOperation.Copies region available operations ∧
        AssignedFrom RegionOperation.Reads region available operations :=
  assignedFrom_mul_iff RegionOperation.Copies RegionOperation.Reads region available operations

/-- Project copy provenance out of combined consumed-cell provenance. -/
theorem Operations.copyCellsAssigned_of_consumed
    (operations : Operations F) (initialRegion : RegionIndex) (cells : List Cell)
    (hassigned : operations.ConsumedCellsAssigned initialRegion cells) :
    operations.CopyCellsAssigned initialRegion cells :=
  ((Operations.assignedFrom_consumes_iff initialRegion cells operations).mp hassigned).1

/-- Project witness-read provenance out of combined consumed-cell provenance. -/
theorem Operations.readsAssigned_of_consumed
    (operations : Operations F) (initialRegion : RegionIndex) (cells : List Cell)
    (hassigned : operations.ConsumedCellsAssigned initialRegion cells) :
    operations.AssignedFrom RegionOperation.Reads initialRegion cells :=
  ((Operations.assignedFrom_consumes_iff initialRegion cells operations).mp hassigned).2

end Halo2
