import Clean.Halo2.Operations.Provenance

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

/-- Copying from a cell state is finding every endpoint there. The keygen simp sets reduce
`copiedCells` per constructor and the memberships to conjunctions. -/
@[keygen_norm, keygen_spine]
theorem consumesFrom_copies_iff (operation : RegionOperation F) :
    ConsumesFrom Copies available operation ↔
      ∀ cell ∈ operation.copiedCells, cell ∈ available := by
  simp [ConsumesFrom, mem_copies_iff]

end RegionOperation

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

end Halo2
