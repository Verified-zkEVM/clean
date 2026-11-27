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

/-- An advice assignment reads a certified support of its witness program; the other
operations do not read any cells. -/
def RegionOperation.Reads : RegionOperation F → Language Cell
  | .assignAdvice _ _ program =>
      {cells | ∃ reads : List (AssignedCell F),
        WitnessFunctionSupport reads (programFunction program) ∧
          cells = reads.map (·.cell)}
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
          cells = reads.map (·.cell) :=
  Iff.rfl

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

/-- Reading from a cell state: a certified support of the program within it for an advice
assignment, nothing for the other operations. -/
@[keygen_norm, keygen_spine]
theorem consumesFrom_reads_iff (operation : RegionOperation F) :
    ConsumesFrom Reads available operation ↔
      match operation with
      | .assignAdvice _ _ program =>
          ∃ reads : List (AssignedCell F),
            WitnessFunctionSupport reads (programFunction program) ∧
              ∀ cell ∈ reads, cell.cell ∈ available
      | _ => True := by
  cases operation
  case assignAdvice column row program =>
    simp only [ConsumesFrom, mem_reads_assignAdvice_iff]
    constructor
    · rintro ⟨_, ⟨reads, hsupport, rfl⟩, havailable⟩
      exact ⟨reads, hsupport, fun cell hcell => havailable _ (List.mem_map_of_mem hcell)⟩
    · rintro ⟨reads, hsupport, havailable⟩
      refine ⟨reads.map (·.cell), ⟨reads, hsupport, rfl⟩, ?_⟩
      intro cell hcell
      obtain ⟨read, hread, rfl⟩ := List.mem_map.mp hcell
      exact havailable read hread
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
