import Clean.Halo2.Operations

namespace Halo2

variable {F : Type}

/-! ## Copy-cell provenance -/

/-- Cells created by assignments in one concrete region. -/
def RegionOperation.assignedCells (region : RegionIndex) : RegionOperation F → List Cell
  | .assignAdvice column row _ => [.of region row column]
  | .assignFixed column row _ => [.of region row column]
  | _ => []

/-- Cells referenced as regional endpoints of copy constraints. -/
def RegionOperation.copiedCells : RegionOperation F → List Cell
  | .constrainEqual left right => [left, right]
  | .constrainConstant cell _ => [cell]
  | .constrainInstance cell _ _ => [cell]
  | _ => []

def RegionOperations.assignedCells (operations : RegionOperations F)
    (region : RegionIndex) : List Cell :=
  operations.flatMap (RegionOperation.assignedCells region)

def RegionOperations.copiedCells (operations : RegionOperations F) : List Cell :=
  operations.flatMap RegionOperation.copiedCells

def RegionOperations.CopyCellsCovered (operations : RegionOperations F)
    (region : RegionIndex) (inputCells : List Cell) : Prop :=
  ∀ cell ∈ operations.copiedCells,
    cell ∈ inputCells ++ operations.assignedCells region

/-- Execution-order-sensitive copy provenance inside one region. -/
inductive RegionOperations.CopyCellsAssignedFrom (region : RegionIndex) :
    List Cell → RegionOperations F → Prop where
  | nil available : CopyCellsAssignedFrom region available []
  | assignAdvice available column row compute rest :
      CopyCellsAssignedFrom region (.of region row column :: available) rest →
        CopyCellsAssignedFrom region available
          (.assignAdvice column row compute :: rest)
  | assignFixed available column row value rest :
      CopyCellsAssignedFrom region (.of region row column :: available) rest →
        CopyCellsAssignedFrom region available (.assignFixed column row value :: rest)
  | enableGate available gate row rest :
      CopyCellsAssignedFrom region available rest →
        CopyCellsAssignedFrom region available (.enableGate gate row :: rest)
  | enableLookup available lookup selectors row rest :
      CopyCellsAssignedFrom region available rest →
        CopyCellsAssignedFrom region available
          (.enableLookup lookup selectors row :: rest)
  | constrainEqual available left right rest :
      left ∈ available → right ∈ available →
        CopyCellsAssignedFrom region available rest →
          CopyCellsAssignedFrom region available (.constrainEqual left right :: rest)
  | constrainConstant available cell value rest :
      cell ∈ available → CopyCellsAssignedFrom region available rest →
        CopyCellsAssignedFrom region available (.constrainConstant cell value :: rest)
  | constrainInstance available cell column row rest :
      cell ∈ available → CopyCellsAssignedFrom region available rest →
        CopyCellsAssignedFrom region available
          (.constrainInstance cell column row :: rest)

def RegionOperations.CopyCellsAssigned (operations : RegionOperations F)
    (region : RegionIndex) (inputCells : List Cell) : Prop :=
  CopyCellsAssignedFrom region inputCells operations

@[keygen_norm, keygen_spine]
theorem RegionOperations.copyCellsAssignedFrom_nil_iff
    (region : RegionIndex) (available : List Cell) :
    CopyCellsAssignedFrom (F := F) region available [] ↔ True := by
  constructor
  · intro _
    trivial
  · intro _
    exact .nil available

@[keygen_norm, keygen_spine]
theorem RegionOperations.copyCellsAssignedFrom_assignAdvice_iff
    (region : RegionIndex) (available : List Cell) (column : Column .advice)
    (row : ℕ) (compute : WitgenIR F 1) (rest : RegionOperations F) :
    CopyCellsAssignedFrom region available (.assignAdvice column row compute :: rest) ↔
      CopyCellsAssignedFrom region (.of region row column :: available) rest := by
  constructor
  · intro h
    cases h with | assignAdvice _ _ _ _ _ hrest => exact hrest
  · exact CopyCellsAssignedFrom.assignAdvice available column row compute rest

@[keygen_norm, keygen_spine]
theorem RegionOperations.copyCellsAssignedFrom_assignFixed_iff
    (region : RegionIndex) (available : List Cell) (column : Column .fixed)
    (row : ℕ) (value : F) (rest : RegionOperations F) :
    CopyCellsAssignedFrom region available (.assignFixed column row value :: rest) ↔
      CopyCellsAssignedFrom region (.of region row column :: available) rest := by
  constructor
  · intro h
    cases h with | assignFixed _ _ _ _ _ hrest => exact hrest
  · exact CopyCellsAssignedFrom.assignFixed available column row value rest

@[keygen_norm, keygen_spine]
theorem RegionOperations.copyCellsAssignedFrom_enableGate_iff
    (region : RegionIndex) (available : List Cell) (gate : Gate F)
    (row : ℕ) (rest : RegionOperations F) :
    CopyCellsAssignedFrom region available (.enableGate gate row :: rest) ↔
      CopyCellsAssignedFrom region available rest := by
  constructor
  · intro h
    cases h with | enableGate _ _ _ _ hrest => exact hrest
  · exact CopyCellsAssignedFrom.enableGate available gate row rest

@[keygen_norm, keygen_spine]
theorem RegionOperations.copyCellsAssignedFrom_enableLookup_iff
    (region : RegionIndex) (available : List Cell) (lookup : LookupArgument F)
    (selectors : List Selector) (row : ℕ) (rest : RegionOperations F) :
    CopyCellsAssignedFrom region available
        (.enableLookup lookup selectors row :: rest) ↔
      CopyCellsAssignedFrom region available rest := by
  constructor
  · intro h
    cases h with | enableLookup _ _ _ _ _ hrest => exact hrest
  · exact CopyCellsAssignedFrom.enableLookup available lookup selectors row rest

@[keygen_norm, keygen_spine]
theorem RegionOperations.copyCellsAssignedFrom_constrainEqual_iff
    (region : RegionIndex) (available : List Cell) (left right : Cell)
    (rest : RegionOperations F) :
    CopyCellsAssignedFrom region available (.constrainEqual left right :: rest) ↔
      left ∈ available ∧ right ∈ available ∧
        CopyCellsAssignedFrom region available rest := by
  constructor
  · intro h
    cases h with | constrainEqual _ _ _ _ hleft hright hrest =>
      exact ⟨hleft, hright, hrest⟩
  · rintro ⟨hleft, hright, hrest⟩
    exact .constrainEqual available left right rest hleft hright hrest

@[keygen_norm, keygen_spine]
theorem RegionOperations.copyCellsAssignedFrom_constrainConstant_iff
    (region : RegionIndex) (available : List Cell) (cell : Cell)
    (value : F) (rest : RegionOperations F) :
    CopyCellsAssignedFrom region available (.constrainConstant cell value :: rest) ↔
      cell ∈ available ∧ CopyCellsAssignedFrom region available rest := by
  constructor
  · intro h
    cases h with | constrainConstant _ _ _ _ hcell hrest => exact ⟨hcell, hrest⟩
  · rintro ⟨hcell, hrest⟩
    exact .constrainConstant available cell value rest hcell hrest

@[keygen_norm, keygen_spine]
theorem RegionOperations.copyCellsAssignedFrom_constrainInstance_iff
    (region : RegionIndex) (available : List Cell) (cell : Cell)
    (column : Column .instance) (row : ℕ) (rest : RegionOperations F) :
    CopyCellsAssignedFrom region available
        (.constrainInstance cell column row :: rest) ↔
      cell ∈ available ∧ CopyCellsAssignedFrom region available rest := by
  constructor
  · intro h
    cases h with | constrainInstance _ _ _ _ _ hcell hrest => exact ⟨hcell, hrest⟩
  · rintro ⟨hcell, hrest⟩
    exact .constrainInstance available cell column row rest hcell hrest

/-- Available cells after executing one region body. -/
def RegionOperations.assignedCellsAfter (region : RegionIndex)
    (available : List Cell) (operations : RegionOperations F) : List Cell :=
  operations.foldl (fun cells operation =>
    operation.assignedCells region ++ cells) available

theorem RegionOperations.assignedCellsAfter_append
    (left right : RegionOperations F) (region : RegionIndex)
    (available : List Cell) :
    (left ++ right).assignedCellsAfter region available =
      right.assignedCellsAfter region
        (left.assignedCellsAfter region available) := by
  simp only [assignedCellsAfter, List.foldl_append]

@[keygen_norm, keygen_spine]
theorem RegionOperations.copyCellsAssignedFrom_append_iff
    (region : RegionIndex) (available : List Cell)
    (left right : RegionOperations F) :
    CopyCellsAssignedFrom region available (left ++ right) ↔
      CopyCellsAssignedFrom region available left ∧
        CopyCellsAssignedFrom region
          (left.assignedCellsAfter region available) right := by
  induction left generalizing available with
  | nil =>
      simp only [List.nil_append, assignedCellsAfter, List.foldl_nil,
        copyCellsAssignedFrom_nil_iff, true_and]
  | cons operation rest inductionHypothesis =>
      cases operation <;>
        simp only [List.cons_append, assignedCellsAfter, List.foldl_cons,
          RegionOperation.assignedCells,
          copyCellsAssignedFrom_assignAdvice_iff,
          copyCellsAssignedFrom_assignFixed_iff,
          copyCellsAssignedFrom_enableGate_iff,
          copyCellsAssignedFrom_enableLookup_iff,
          copyCellsAssignedFrom_constrainEqual_iff,
          copyCellsAssignedFrom_constrainConstant_iff,
          copyCellsAssignedFrom_constrainInstance_iff,
          inductionHypothesis, List.nil_append, and_assoc]

/-- Copy provenance remains valid when the caller makes more cells available. -/
theorem RegionOperations.CopyCellsAssignedFrom.mono
    {operations : RegionOperations F} {region : RegionIndex}
    {available larger : List Cell}
    (hassigned : operations.CopyCellsAssignedFrom region available)
    (havailable : ∀ cell, cell ∈ available → cell ∈ larger) :
    operations.CopyCellsAssignedFrom region larger := by
  induction hassigned generalizing larger with
  | nil => exact .nil larger
  | assignAdvice available column row compute rest hassigned inductionHypothesis =>
      exact .assignAdvice larger column row compute rest
        (inductionHypothesis fun cell hcell => by
          simp only [List.mem_cons] at hcell ⊢
          rcases hcell with rfl | hcell
          · exact Or.inl rfl
          · exact Or.inr (havailable cell hcell))
  | assignFixed available column row value rest hassigned inductionHypothesis =>
      exact .assignFixed larger column row value rest
        (inductionHypothesis fun cell hcell => by
          simp only [List.mem_cons] at hcell ⊢
          rcases hcell with rfl | hcell
          · exact Or.inl rfl
          · exact Or.inr (havailable cell hcell))
  | enableGate available gate row rest hassigned inductionHypothesis =>
      exact .enableGate larger gate row rest
        (inductionHypothesis havailable)
  | enableLookup available lookup selectors row rest hassigned inductionHypothesis =>
      exact .enableLookup larger lookup selectors row rest
        (inductionHypothesis havailable)
  | constrainEqual available left right rest hleft hright hassigned
      inductionHypothesis =>
      exact .constrainEqual larger left right rest
        (havailable left hleft) (havailable right hright)
        (inductionHypothesis havailable)
  | constrainConstant available cell value rest hcell hassigned inductionHypothesis =>
      exact .constrainConstant larger cell value rest
        (havailable cell hcell) (inductionHypothesis havailable)
  | constrainInstance available cell column row rest hcell hassigned
      inductionHypothesis =>
      exact .constrainInstance larger cell column row rest
        (havailable cell hcell) (inductionHypothesis havailable)

/-- A region fragment containing no copy-like operation is lawful for every incoming
cell state. -/
@[keygen_helper]
theorem RegionOperations.copyCellsAssignedFrom_of_forall_copiedCells_eq_nil
    (operations : RegionOperations F) (region : RegionIndex)
    (available : List Cell)
    (hoperations : operations.Forall fun operation =>
      operation.copiedCells = []) :
    operations.CopyCellsAssignedFrom region available := by
  induction operations generalizing available with
  | nil => exact .nil available
  | cons operation rest inductionHypothesis =>
      rw [List.forall_cons] at hoperations
      cases operation with
      | assignAdvice column row compute =>
          exact .assignAdvice available column row compute rest
            (inductionHypothesis _ hoperations.2)
      | assignFixed column row value =>
          exact .assignFixed available column row value rest
            (inductionHypothesis _ hoperations.2)
      | enableGate gate row =>
          exact .enableGate available gate row rest
            (inductionHypothesis _ hoperations.2)
      | enableLookup lookup selectors row =>
          exact .enableLookup available lookup selectors row rest
            (inductionHypothesis _ hoperations.2)
      | constrainEqual left right =>
          cases hoperations.1
      | constrainConstant cell value =>
          cases hoperations.1
      | constrainInstance cell column row =>
          cases hoperations.1

/-- Cells assigned by a layouter stream, with the same region-index walk used by V1. -/
def Operations.assignedCellsFrom : Operations F → RegionIndex → List Cell
  | [], _ => []
  | .region _ body :: rest, region =>
      body.assignedCells region ++ assignedCellsFrom rest (region + 1)
  | .constrainInstance _ _ _ :: rest, region => assignedCellsFrom rest region
  | .loadTable _ _ :: rest, region => assignedCellsFrom rest region

def Operations.assignedCells (operations : Operations F) : List Cell :=
  operations.assignedCellsFrom 0

/-- Cells referenced by one copy-like layouter operation. -/
def Operation.copiedCells : Operation F → List Cell
  | .region _ body => body.copiedCells
  | .constrainInstance cell _ _ => [cell]
  | .loadTable _ _ => []

/-- Cells referenced by every copy-like operation in a layouter stream. -/
def Operations.copiedCells (operations : Operations F) : List Cell :=
  operations.flatMap Operation.copiedCells

/-- Execution-order-sensitive copy provenance through the layouter stream. -/
inductive Operations.CopyCellsAssignedFrom :
    RegionIndex → List Cell → Operations F → Prop where
  | nil region available : CopyCellsAssignedFrom region available []
  | region region available name body rest :
      body.CopyCellsAssignedFrom region available →
        CopyCellsAssignedFrom (region + 1)
          (body.assignedCellsAfter region available) rest →
            CopyCellsAssignedFrom region available (.region name body :: rest)
  | constrainInstance region available cell column row rest :
      cell ∈ available → CopyCellsAssignedFrom region available rest →
        CopyCellsAssignedFrom region available
          (.constrainInstance cell column row :: rest)
  | loadTable region available column values rest :
      CopyCellsAssignedFrom region available rest →
        CopyCellsAssignedFrom region available (.loadTable column values :: rest)

@[keygen_norm, keygen_spine]
theorem Operations.copyCellsAssignedFrom_nil_iff
    (region : RegionIndex) (available : List Cell) :
    CopyCellsAssignedFrom (F := F) region available [] ↔ True := by
  constructor
  · intro _
    trivial
  · intro _
    exact .nil region available

@[keygen_norm, keygen_spine]
theorem Operations.copyCellsAssignedFrom_region_iff
    (region : RegionIndex) (available : List Cell) (name : String)
    (body : RegionOperations F) (rest : Operations F) :
    CopyCellsAssignedFrom region available (.region name body :: rest) ↔
      body.CopyCellsAssignedFrom region available ∧
        CopyCellsAssignedFrom (region + 1)
          (body.assignedCellsAfter region available) rest := by
  constructor
  · intro h
    cases h with | region _ _ _ _ _ hbody hrest => exact ⟨hbody, hrest⟩
  · rintro ⟨hbody, hrest⟩
    exact .region region available name body rest hbody hrest

@[keygen_norm, keygen_spine]
theorem Operations.copyCellsAssignedFrom_constrainInstance_iff
    (region : RegionIndex) (available : List Cell) (cell : Cell)
    (column : Column .instance) (row : ℕ) (rest : Operations F) :
    CopyCellsAssignedFrom region available
        (.constrainInstance cell column row :: rest) ↔
      cell ∈ available ∧ CopyCellsAssignedFrom region available rest := by
  constructor
  · intro h
    cases h with | constrainInstance _ _ _ _ _ _ hcell hrest => exact ⟨hcell, hrest⟩
  · rintro ⟨hcell, hrest⟩
    exact .constrainInstance region available cell column row rest hcell hrest

@[keygen_norm, keygen_spine]
theorem Operations.copyCellsAssignedFrom_loadTable_iff
    (region : RegionIndex) (available : List Cell) (column : TableColumn)
    (values : List F) (rest : Operations F) :
    CopyCellsAssignedFrom region available (.loadTable column values :: rest) ↔
      CopyCellsAssignedFrom region available rest := by
  constructor
  · intro h
    cases h with | loadTable _ _ _ _ _ hrest => exact hrest
  · exact CopyCellsAssignedFrom.loadTable region available column values rest

/-- A layouter stream containing no copy-like operation is lawful for every incoming
cell state. -/
@[keygen_helper]
theorem Operations.copyCellsAssignedFrom_of_forall_copiedCells_eq_nil
    (operations : Operations F) (region : RegionIndex)
    (available : List Cell)
    (hoperations : operations.Forall fun operation =>
      operation.copiedCells = []) :
    operations.CopyCellsAssignedFrom region available := by
  induction operations generalizing region available with
  | nil => exact .nil region available
  | cons operation rest inductionHypothesis =>
      rw [List.forall_cons] at hoperations
      cases operation with
      | region name body =>
          apply Operations.CopyCellsAssignedFrom.region region available name body rest
          · apply RegionOperations.copyCellsAssignedFrom_of_forall_copiedCells_eq_nil
            rw [List.forall_iff_forall_mem]
            simpa only [Operation.copiedCells, RegionOperations.copiedCells,
              List.flatMap_eq_nil_iff] using hoperations.1
          · exact inductionHypothesis (region := region + 1)
              (available := body.assignedCellsAfter region available) hoperations.2
      | constrainInstance cell column row =>
          simp only [Operation.copiedCells, List.cons_ne_nil] at hoperations
          exact False.elim hoperations.1
      | loadTable column values =>
          exact .loadTable region available column values rest
            (inductionHypothesis (region := region) (available := available)
              hoperations.2)

def Operations.CopyCellsAssigned (operations : Operations F)
    (initialRegion : RegionIndex) (inputCells : List Cell) : Prop :=
  CopyCellsAssignedFrom initialRegion inputCells operations

/-- Set-level consequence used by compiler proofs. -/
def Operations.CopyCellsCovered (operations : Operations F)
    (initialRegion : RegionIndex) (inputCells : List Cell) : Prop :=
  ∀ cell ∈ operations.copiedCells,
    cell ∈ inputCells ++ operations.assignedCellsFrom initialRegion

theorem RegionOperations.mem_assignedCellsAfter_iff
    (operations : RegionOperations F) (region : RegionIndex)
    (available : List Cell) (cell : Cell) :
    cell ∈ operations.assignedCellsAfter region available ↔
      cell ∈ available ++ operations.assignedCells region := by
  unfold assignedCellsAfter assignedCells
  induction operations generalizing available with
  | nil => simp
  | cons operation rest inductionHypothesis =>
      simp only [List.foldl_cons, List.flatMap_cons]
      rw [inductionHypothesis]
      cases operation <;> simp [RegionOperation.assignedCells, or_left_comm]

theorem RegionOperations.mem_assignedCellsAfter_of_mem
    (operations : RegionOperations F) (region : RegionIndex)
    (available : List Cell) (cell : Cell) (hcell : cell ∈ available) :
    cell ∈ operations.assignedCellsAfter region available := by
  rw [mem_assignedCellsAfter_iff, List.mem_append]
  exact Or.inl hcell

/-- Layouter-level copy provenance remains valid when the caller makes more cells
available. -/
theorem Operations.CopyCellsAssignedFrom.mono
    {operations : Operations F} {region : RegionIndex}
    {available larger : List Cell}
    (hassigned : operations.CopyCellsAssignedFrom region available)
    (havailable : ∀ cell, cell ∈ available → cell ∈ larger) :
    operations.CopyCellsAssignedFrom region larger := by
  induction hassigned generalizing larger with
  | nil currentRegion => exact .nil currentRegion larger
  | region region available name body rest hbody hrest restInduction =>
      apply Operations.CopyCellsAssignedFrom.region region larger name body rest
      · exact hbody.mono havailable
      · apply restInduction
        intro cell hcell
        rw [RegionOperations.mem_assignedCellsAfter_iff] at hcell ⊢
        simp only [List.mem_append] at hcell ⊢
        rcases hcell with hcell | hcell
        · exact Or.inl (havailable cell hcell)
        · exact Or.inr hcell
  | constrainInstance region available cell column row rest hcell hassigned
      inductionHypothesis =>
      exact .constrainInstance region larger cell column row rest
        (havailable cell hcell) (inductionHypothesis havailable)
  | loadTable region available column values rest hassigned inductionHypothesis =>
      exact .loadTable region larger column values rest
        (inductionHypothesis havailable)

theorem RegionOperations.copyCellsCovered_of_assignedFrom
    (operations : RegionOperations F) (region : RegionIndex)
    (available : List Cell)
    (hassigned : operations.CopyCellsAssignedFrom region available) :
    operations.CopyCellsCovered region available := by
  induction operations generalizing available with
  | nil => simp [CopyCellsCovered, copiedCells]
  | cons operation rest inductionHypothesis =>
      intro cell hcell
      cases operation with
      | assignAdvice column row value =>
          cases hassigned with
          | assignAdvice _ _ _ _ _ hassignedRest =>
          have hrest := inductionHypothesis
            (.of region row column :: available) hassignedRest cell hcell
          simp only [List.mem_append, List.mem_cons,
            assignedCells, List.flatMap_cons, RegionOperation.assignedCells,
            List.singleton_append] at hrest ⊢
          tauto
      | assignFixed column row value =>
          cases hassigned with
          | assignFixed _ _ _ _ _ hassignedRest =>
          have hrest := inductionHypothesis
            (.of region row column :: available) hassignedRest cell hcell
          simp only [List.mem_append, List.mem_cons,
            assignedCells, List.flatMap_cons, RegionOperation.assignedCells,
            List.singleton_append] at hrest ⊢
          tauto
      | enableGate gate row =>
          cases hassigned with
          | enableGate _ _ _ _ hassignedRest =>
            exact inductionHypothesis available hassignedRest cell hcell
      | enableLookup lookup selectors row =>
          cases hassigned with
          | enableLookup _ _ _ _ _ hassignedRest =>
            exact inductionHypothesis available hassignedRest cell hcell
      | constrainEqual left right =>
          rw [copyCellsAssignedFrom_constrainEqual_iff] at hassigned
          simp only [copiedCells, List.flatMap_cons,
            RegionOperation.copiedCells, List.mem_append] at hcell
          simp only [assignedCells, List.flatMap_cons,
            RegionOperation.assignedCells, List.nil_append]
          rcases hcell with hcurrent | hrest
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at hcurrent
            rcases hcurrent with rfl | rfl
            · exact List.mem_append_left _ hassigned.1
            · exact List.mem_append_left _ hassigned.2.1
          · exact inductionHypothesis available hassigned.2.2 cell hrest
      | constrainConstant copied value =>
          rw [copyCellsAssignedFrom_constrainConstant_iff] at hassigned
          simp only [copiedCells, List.flatMap_cons,
            RegionOperation.copiedCells, List.mem_append] at hcell
          simp only [assignedCells, List.flatMap_cons,
            RegionOperation.assignedCells, List.nil_append]
          rcases hcell with hcurrent | hrest
          · rw [List.mem_singleton] at hcurrent
            subst cell
            exact List.mem_append_left _ hassigned.1
          · exact inductionHypothesis available hassigned.2 cell hrest
      | constrainInstance copied column row =>
          rw [RegionOperations.copyCellsAssignedFrom_constrainInstance_iff] at hassigned
          simp only [copiedCells, List.flatMap_cons,
            RegionOperation.copiedCells, List.mem_append] at hcell
          simp only [assignedCells, List.flatMap_cons,
            RegionOperation.assignedCells, List.nil_append]
          rcases hcell with hcurrent | hrest
          · rw [List.mem_singleton] at hcurrent
            subst cell
            exact List.mem_append_left _ hassigned.1
          · exact inductionHypothesis available hassigned.2 cell hrest

theorem Operations.copyCellsCovered_of_assignedFrom
    (operations : Operations F) (initialRegion : RegionIndex)
    (available : List Cell)
    (hassigned : CopyCellsAssignedFrom initialRegion available operations) :
    operations.CopyCellsCovered initialRegion available := by
  induction operations generalizing initialRegion available with
  | nil => simp [CopyCellsCovered, Operations.copiedCells]
  | cons operation rest inductionHypothesis =>
      cases operation with
      | region name body =>
          intro cell hcell
          rw [copyCellsAssignedFrom_region_iff] at hassigned
          rw [Operations.copiedCells, List.mem_flatMap] at hcell
          rcases hcell with ⟨candidate, hcandidate, hcell⟩
          rw [List.mem_cons] at hcandidate
          rcases hcandidate with rfl | hrest
          · have hcovered := body.copyCellsCovered_of_assignedFrom
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
          rw [Operations.copyCellsAssignedFrom_constrainInstance_iff] at hassigned
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
    (operations : Operations F) (initialRegion : RegionIndex)
    (inputCells : List Cell)
    (hassigned : operations.CopyCellsAssigned initialRegion inputCells) :
    operations.CopyCellsCovered initialRegion inputCells :=
  operations.copyCellsCovered_of_assignedFrom initialRegion inputCells hassigned
theorem Operations.assignedCellsFrom_append
    (left right : Operations F) (region : RegionIndex) :
    (left ++ right).assignedCellsFrom region =
      left.assignedCellsFrom region ++
        right.assignedCellsFrom (region + left.regionCount) := by
  induction left generalizing region with
  | nil => simp only [List.nil_append, assignedCellsFrom, regionCount, Nat.add_zero,
      List.nil_append]
  | cons operation rest ih =>
      cases operation <;>
        simp only [List.cons_append, assignedCellsFrom, regionCount, ih,
          List.append_assoc, Nat.add_assoc]

theorem Operations.mem_assignedCellsFrom_append_left
    {left right : Operations F} {region : RegionIndex} {cell : Cell}
    (hcell : cell ∈ left.assignedCellsFrom region) :
    cell ∈ (left ++ right).assignedCellsFrom region := by
  rw [Operations.assignedCellsFrom_append]
  exact List.mem_append_left _ hcell

theorem Operations.mem_assignedCellsFrom_append_right
    {left right : Operations F} {region : RegionIndex} {cell : Cell}
    (hcell : cell ∈ right.assignedCellsFrom (region + left.regionCount)) :
    cell ∈ (left ++ right).assignedCellsFrom region := by
  rw [Operations.assignedCellsFrom_append]
  exact List.mem_append_right _ hcell

/-- Copy provenance composes across appended layouter streams. The second stream may
use every caller cell and every cell assigned by the first stream. -/
theorem Operations.CopyCellsAssignedFrom.append
    {left right : Operations F} {region : RegionIndex} {available : List Cell}
    (hleft : left.CopyCellsAssignedFrom region available)
    (hright : right.CopyCellsAssignedFrom (region + left.regionCount)
      (available ++ left.assignedCellsFrom region)) :
    (left ++ right).CopyCellsAssignedFrom region available := by
  induction hleft with
  | nil => simpa [Operations.regionCount, Operations.assignedCellsFrom] using hright
  | region current available name body rest hbody hrest ih =>
      rw [List.cons_append, Operations.copyCellsAssignedFrom_region_iff]
      refine ⟨hbody, ih ?_⟩
      have h := hright.mono (larger :=
          body.assignedCellsAfter current available ++
            rest.assignedCellsFrom (current + 1)) (by
        intro cell hcell
        simp only [Operations.assignedCellsFrom, List.mem_append] at hcell ⊢
        rcases hcell with hcell | hcell
        · left
          rw [RegionOperations.mem_assignedCellsAfter_iff, List.mem_append]
          exact Or.inl hcell
        · rcases hcell with hbodyCell | hrestCell
          · left
            rw [RegionOperations.mem_assignedCellsAfter_iff, List.mem_append]
            exact Or.inr hbodyCell
          · exact Or.inr hrestCell)
      simpa only [Operations.regionCount, Nat.add_assoc] using h
  | constrainInstance current available cell column row rest hcell hrest ih =>
      rw [List.cons_append, Operations.copyCellsAssignedFrom_constrainInstance_iff]
      refine ⟨hcell, ih ?_⟩
      simpa [Operations.regionCount, Operations.assignedCellsFrom] using hright
  | loadTable current available column values rest hrest ih =>
      rw [List.cons_append, Operations.copyCellsAssignedFrom_loadTable_iff]
      apply ih
      simpa [Operations.regionCount, Operations.assignedCellsFrom] using hright

end Halo2
