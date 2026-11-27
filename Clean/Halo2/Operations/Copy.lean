module

public import Clean.Halo2.Operations.Provenance

@[expose] public section

namespace Halo2

variable {F : Type}

/-! ## Copy-cell provenance

The instance of `AssignedFrom` at `RegionOperation.Copies`: a copy-like operation consumes
exactly its endpoints, and the other operations consume nothing. -/

/-- Cells referenced as regional endpoints of copy constraints. -/
def RegionOperation.copiedCells : RegionOperation F → List Cell
  | .constrainEqual left right => [left, right]
  | .constrainConstant cell _ => [cell]
  | .constrainInstance cell _ _ => [cell]
  | _ => []

def RegionOperations.copiedCells (operations : RegionOperations F) : List Cell :=
  operations.flatMap RegionOperation.copiedCells

def RegionOperations.CopyCellsCovered (operations : RegionOperations F)
    (region : RegionIndex) (inputCells : List Cell) : Prop :=
  ∀ cell ∈ operations.copiedCells,
    cell ∈ inputCells ++ operations.assignedCells region

/-- A copy-like operation consumes exactly its endpoints; the other operations consume
nothing. -/
def RegionOperation.Copies (operation : RegionOperation F) : Language Cell :=
  {operation.copiedCells}

namespace RegionOperation

variable (available : List Cell)

@[keygen_norm]
theorem mem_copies_iff (operation : RegionOperation F) (cells : List Cell) :
    cells ∈ operation.Copies ↔ cells = operation.copiedCells :=
  Iff.rfl

/-- Copying from a cell state is finding every endpoint there. -/
@[keygen_norm, keygen_spine]
theorem consumesFrom_copies_iff (operation : RegionOperation F) :
    ConsumesFrom Copies available operation ↔
      ∀ cell ∈ operation.copiedCells, cell ∈ available := by
  simp [ConsumesFrom, mem_copies_iff]

end RegionOperation

/-- Copy-provenance abbreviations retained for compatibility with copy-only callers. -/
abbrev RegionOperations.CopyCellsAssignedFrom (operations : RegionOperations F)
    (region : RegionIndex) (available : List Cell) : Prop :=
  operations.AssignedFrom RegionOperation.Copies region available

abbrev RegionOperations.CopyCellsAssigned (operations : RegionOperations F)
    (region : RegionIndex) (inputCells : List Cell) : Prop :=
  operations.CopyCellsAssignedFrom region inputCells

namespace RegionOperations.CopyCellsAssignedFrom

theorem assignAdvice (available : List Cell) (column : Column .advice) (row : ℕ)
    (compute : WitgenIR F 1) (rest : RegionOperations F) {region : RegionIndex}
    (next : rest.CopyCellsAssignedFrom region (Cell.of region row column :: available)) :
    RegionOperations.CopyCellsAssignedFrom
      (RegionOperation.assignAdvice column row compute :: rest) region available :=
  .cons available (.assignAdvice column row compute) rest [] rfl (fun _ h => nomatch h) next

theorem assignFixed (available : List Cell) (column : Column .fixed) (row : ℕ)
    (value : F) (rest : RegionOperations F) {region : RegionIndex}
    (next : rest.CopyCellsAssignedFrom region (Cell.of region row column :: available)) :
    RegionOperations.CopyCellsAssignedFrom
      (RegionOperation.assignFixed column row value :: rest) region available :=
  .cons available (.assignFixed column row value) rest [] rfl (fun _ h => nomatch h) next

theorem enableGate (available : List Cell) (gate : Gate F) (row : ℕ)
    (rest : RegionOperations F) {region : RegionIndex}
    (next : rest.CopyCellsAssignedFrom region available) :
    RegionOperations.CopyCellsAssignedFrom
      (RegionOperation.enableGate gate row :: rest) region available :=
  .cons available (.enableGate gate row) rest [] rfl (fun _ h => nomatch h) next

theorem enableLookup (available : List Cell) (argument : LookupArgument F)
    (selectors : List Selector) (row : ℕ) (rest : RegionOperations F) {region : RegionIndex}
    (next : rest.CopyCellsAssignedFrom region available) :
    RegionOperations.CopyCellsAssignedFrom
      (RegionOperation.enableLookup argument selectors row :: rest) region available :=
  .cons available (.enableLookup argument selectors row) rest [] rfl (fun _ h => nomatch h) next

theorem constrainEqual (available : List Cell) (left right : Cell)
    (rest : RegionOperations F) {region : RegionIndex}
    (hleft : left ∈ available) (hright : right ∈ available)
    (next : rest.CopyCellsAssignedFrom region available) :
    RegionOperations.CopyCellsAssignedFrom
      (RegionOperation.constrainEqual left right :: rest) region available :=
  .cons available (.constrainEqual left right) rest [left, right] rfl
    (fun _ hc => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl <;> assumption) next

theorem constrainConstant (available : List Cell) (cell : Cell) (value : F)
    (rest : RegionOperations F) {region : RegionIndex}
    (hcell : cell ∈ available) (next : rest.CopyCellsAssignedFrom region available) :
    RegionOperations.CopyCellsAssignedFrom
      (RegionOperation.constrainConstant cell value :: rest) region available :=
  .cons available (.constrainConstant cell value) rest [cell] rfl
    (fun _ hc => by
      simp only [List.mem_singleton] at hc
      rwa [hc]) next

theorem constrainInstance (available : List Cell) (cell : Cell)
    (column : Column .instance) (row : ℕ) (rest : RegionOperations F) {region : RegionIndex}
    (hcell : cell ∈ available) (next : rest.CopyCellsAssignedFrom region available) :
    RegionOperations.CopyCellsAssignedFrom
      (RegionOperation.constrainInstance cell column row :: rest) region available :=
  .cons available (.constrainInstance cell column row) rest [cell] rfl
    (fun _ hc => by
      simp only [List.mem_singleton] at hc
      rwa [hc]) next

end RegionOperations.CopyCellsAssignedFrom

theorem RegionOperations.copyCellsAssignedFrom_append_iff
    (left right : RegionOperations F) (region : RegionIndex) (available : List Cell) :
    RegionOperations.CopyCellsAssignedFrom (left ++ right) region available ↔
      left.CopyCellsAssignedFrom region available ∧
        right.CopyCellsAssignedFrom region (left.assignedCellsAfter region available) :=
  RegionOperations.assignedFrom_append_iff RegionOperation.Copies region available left right

theorem RegionOperations.copyCellsAssignedFrom_assignAdvice_iff
    (column : Column .advice) (row : ℕ) (compute : WitgenIR F 1)
    (rest : RegionOperations F) (region : RegionIndex) (available : List Cell) :
    RegionOperations.CopyCellsAssignedFrom
        (RegionOperation.assignAdvice column row compute :: rest) region available ↔
      rest.CopyCellsAssignedFrom region (Cell.of region row column :: available) := by
  rw [CopyCellsAssignedFrom, assignedFrom_cons_iff]
  simp [RegionOperation.consumesFrom_copies_iff, RegionOperation.copiedCells,
    RegionOperation.assignedCells]

theorem RegionOperations.copyCellsAssignedFrom_assignFixed_iff
    (column : Column .fixed) (row : ℕ) (value : F)
    (rest : RegionOperations F) (region : RegionIndex) (available : List Cell) :
    RegionOperations.CopyCellsAssignedFrom
        (RegionOperation.assignFixed column row value :: rest) region available ↔
      rest.CopyCellsAssignedFrom region (Cell.of region row column :: available) := by
  rw [CopyCellsAssignedFrom, assignedFrom_cons_iff]
  simp [RegionOperation.consumesFrom_copies_iff, RegionOperation.copiedCells,
    RegionOperation.assignedCells]

theorem RegionOperations.copyCellsAssignedFrom_constrainEqual_iff
    (left right : Cell) (rest : RegionOperations F) (region : RegionIndex)
    (available : List Cell) :
    RegionOperations.CopyCellsAssignedFrom
        (RegionOperation.constrainEqual left right :: rest) region available ↔
      left ∈ available ∧ right ∈ available ∧ rest.CopyCellsAssignedFrom region available := by
  rw [CopyCellsAssignedFrom, assignedFrom_cons_iff]
  simp [RegionOperation.consumesFrom_copies_iff, RegionOperation.copiedCells,
    RegionOperation.assignedCells, and_assoc]

/-- Cells referenced by one copy-like layouter operation. -/
def Operation.copiedCells : Operation F → List Cell
  | .region _ body => body.copiedCells
  | .constrainInstance cell _ _ => [cell]
  | .loadTable _ _ => []

/-- Cells referenced by every copy-like operation in a layouter stream. -/
def Operations.copiedCells (operations : Operations F) : List Cell :=
  operations.flatMap Operation.copiedCells

/-- Set-level consequence used by compiler proofs. -/
def Operations.CopyCellsCovered (operations : Operations F)
    (initialRegion : RegionIndex) (inputCells : List Cell) : Prop :=
  ∀ cell ∈ operations.copiedCells,
    cell ∈ inputCells ++ operations.assignedCellsFrom initialRegion

abbrev Operations.CopyCellsAssignedFrom (operations : Operations F)
    (initialRegion : RegionIndex) (available : List Cell) : Prop :=
  operations.AssignedFrom RegionOperation.Copies initialRegion available

abbrev Operations.CopyCellsAssigned (operations : Operations F)
    (initialRegion : RegionIndex) (inputCells : List Cell) : Prop :=
  operations.CopyCellsAssignedFrom initialRegion inputCells

theorem Operations.copyCellsAssignedFrom_region_iff
    (name : String) (body : RegionOperations F) (rest : Operations F)
    (region : RegionIndex) (available : List Cell) :
    Operations.CopyCellsAssignedFrom (Operation.region name body :: rest) region available ↔
      body.CopyCellsAssignedFrom region available ∧
        rest.CopyCellsAssignedFrom (region + 1) (body.assignedCellsAfter region available) :=
  Operations.assignedFrom_region_iff RegionOperation.Copies region available name body rest

theorem Operations.copyCellsAssignedFrom_constrainInstance_iff
    (cell : Cell) (column : Column .instance) (row : ℕ) (rest : Operations F)
    (region : RegionIndex) (available : List Cell) :
    Operations.CopyCellsAssignedFrom
        (Operation.constrainInstance cell column row :: rest) region available ↔
      cell ∈ available ∧ rest.CopyCellsAssignedFrom region available :=
  Operations.assignedFrom_constrainInstance_iff RegionOperation.Copies region available
    cell column row rest

/-- Provenance for a relation under which every copy-like operation consumes at least its
endpoints yields the set-level copy coverage. -/
theorem RegionOperations.copyCellsCovered_of_assignedFrom
    {consumption : Consumption F}
    (hcopies : ∀ operation cells, cells ∈ consumption operation →
      ∀ cell ∈ operation.copiedCells, cell ∈ cells)
    (operations : RegionOperations F) (region : RegionIndex)
    (available : List Cell)
    (hassigned : operations.AssignedFrom consumption region available) :
    operations.CopyCellsCovered region available := by
  induction operations generalizing available with
  | nil => simp [CopyCellsCovered, copiedCells]
  | cons operation rest inductionHypothesis =>
      rw [assignedFrom_cons_iff] at hassigned
      obtain ⟨⟨cells, hconsumes, havailable⟩, hrest⟩ := hassigned
      intro cell hcell
      simp only [copiedCells, List.flatMap_cons, List.mem_append] at hcell
      simp only [assignedCells, List.flatMap_cons, List.mem_append]
      rcases hcell with hcurrent | hcell
      · exact Or.inl (havailable cell (hcopies operation cells hconsumes cell hcurrent))
      · have hcovered := inductionHypothesis _ hrest cell hcell
        simp only [List.mem_append] at hcovered
        tauto

theorem Operations.copyCellsCovered_of_assignedFrom
    {consumption : Consumption F}
    (hcopies : ∀ operation cells, cells ∈ consumption operation →
      ∀ cell ∈ operation.copiedCells, cell ∈ cells)
    (operations : Operations F) (initialRegion : RegionIndex)
    (available : List Cell)
    (hassigned : AssignedFrom consumption initialRegion available operations) :
    operations.CopyCellsCovered initialRegion available := by
  induction operations generalizing initialRegion available with
  | nil => simp [CopyCellsCovered, Operations.copiedCells]
  | cons operation rest inductionHypothesis =>
      cases operation with
      | region name body =>
          intro cell hcell
          rw [assignedFrom_region_iff] at hassigned
          rw [Operations.copiedCells, List.mem_flatMap] at hcell
          rcases hcell with ⟨candidate, hcandidate, hcell⟩
          rw [List.mem_cons] at hcandidate
          rcases hcandidate with rfl | hrest
          · have hcovered := RegionOperations.copyCellsCovered_of_assignedFrom hcopies body
              initialRegion available hassigned.1 cell hcell
            rw [List.mem_append] at hcovered
            rw [Operations.assignedCellsFrom, List.mem_append]
            exact Or.imp_right (fun hbody => List.mem_append_left _ hbody) hcovered
          · have hcovered := inductionHypothesis (initialRegion + 1)
              (body.assignedCellsAfter initialRegion available)
              hassigned.2 cell (List.mem_flatMap.mpr ⟨candidate, hrest, hcell⟩)
            rw [List.mem_append] at hcovered
            rw [Operations.assignedCellsFrom, List.mem_append]
            rcases hcovered with hafter | hrestAssigned
            · rw [body.mem_assignedCellsAfter_iff] at hafter
              rw [List.mem_append] at hafter
              exact Or.imp_right (List.mem_append_left _) hafter
            · exact Or.inr (List.mem_append_right _ hrestAssigned)
      | constrainInstance copied column row =>
          intro cell hcell
          rw [Operations.assignedFrom_constrainInstance_iff] at hassigned
          rw [Operations.copiedCells, List.mem_flatMap] at hcell
          rcases hcell with ⟨candidate, hcandidate, hcell⟩
          rw [List.mem_cons] at hcandidate
          rcases hcandidate with rfl | hrest
          · simp only [Operation.copiedCells, List.mem_singleton] at hcell
            subst cell
            exact List.mem_append_left _ hassigned.1
          · exact inductionHypothesis initialRegion available hassigned.2 cell
              (List.mem_flatMap.mpr ⟨candidate, hrest, hcell⟩)
      | loadTable column values =>
          cases hassigned with
          | loadTable _ _ _ _ _ hassignedRest =>
            exact inductionHypothesis initialRegion available hassignedRest

theorem Operations.copyCellsCovered_of_assigned
    (operations : Operations F) (initialRegion : RegionIndex) (cells : List Cell)
    (hassigned : operations.CopyCellsAssigned initialRegion cells) :
    operations.CopyCellsCovered initialRegion cells :=
  operations.copyCellsCovered_of_assignedFrom
    (fun op cs hmem _ hc => (RegionOperation.mem_copies_iff op cs).mp hmem ▸ hc)
    initialRegion cells hassigned

end Halo2
