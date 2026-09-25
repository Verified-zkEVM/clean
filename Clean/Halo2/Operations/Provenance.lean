import Clean.Halo2.Operations
import Mathlib.Computability.Language

namespace Halo2

variable {F : Type}

/-! ## Execution-order provenance

`RegionOperations.AssignedFrom consumption region available operations` walks a region's
operations with an accumulator: the cells assigned so far in the region, plus the cells the
caller supplies. Each operation consumes some list of cells, drawn from the language that
`consumption` assigns to it, and every consumed cell must be in the accumulator; each
assignment then extends the accumulator. The composition lemmas are stated for an arbitrary
consumption relation, since none of them depends on which cells an operation consumes. Copy
provenance is the instance at `RegionOperation.Copies` (`Operations/Copy.lean`). -/

/-- Cells created by assignments in one concrete region. -/
def RegionOperation.assignedCells (region : RegionIndex) : RegionOperation F → List Cell
  | .assignAdvice column row _ => [.of region row column]
  | .assignFixed column row _ => [.of region row column]
  | _ => []

def RegionOperations.assignedCells (operations : RegionOperations F)
    (region : RegionIndex) : List Cell :=
  operations.flatMap (RegionOperation.assignedCells region)

/-! The keygen sets reduce `RegionOperations.assignedCells` structurally and keep it folded
over an opaque operation list, such as a call's, so that a rule about that list's assigned
cells can match. -/

@[keygen_norm, keygen_spine]
theorem RegionOperations.assignedCells_nil (region : RegionIndex) :
    RegionOperations.assignedCells (F := F) [] region = [] := rfl

@[keygen_norm, keygen_spine]
theorem RegionOperations.assignedCells_cons (operation : RegionOperation F)
    (rest : RegionOperations F) (region : RegionIndex) :
    RegionOperations.assignedCells (operation :: rest) region =
      operation.assignedCells region ++ RegionOperations.assignedCells rest region :=
  List.flatMap_cons ..

@[keygen_norm, keygen_spine]
theorem RegionOperations.assignedCells_append (left right : RegionOperations F)
    (region : RegionIndex) :
    RegionOperations.assignedCells (left ++ right) region =
      RegionOperations.assignedCells left region ++
        RegionOperations.assignedCells right region :=
  List.flatMap_append ..

/-- A consumption relation: for each operation, the cell lists it may consume.

A `Language α` (Mathlib) is a set of strings over the alphabet `α`, strings being lists, with
concatenation lifted to sets as `*` and the language `{[]}` of the empty string as `1`. This
fits consumption. An operation may consume any one of several cell lists: a copy constraint
exactly its endpoints, an advice assignment any certified support of its program. So its
options are a set of cell lists, a language over cells. Consuming under two relations at once
means consuming a list from each, one after the other, which is the product of the two
languages. Consuming nothing is the unit. Provenance uses only this multiplication and unit,
applied operation by operation (`assignedFrom_mul_iff`, `assignedFrom_one`). -/
abbrev Consumption (F : Type) := RegionOperation F → Language Cell

/-- The operation consumes some list of cells, all of them available. -/
def RegionOperation.ConsumesFrom (consumption : Consumption F) (available : List Cell)
    (operation : RegionOperation F) : Prop :=
  ∃ cells ∈ consumption operation, ∀ cell ∈ cells, cell ∈ available

/-- Execution-order provenance inside one region: every operation consumes only cells
assigned earlier in the region or supplied by the caller. -/
inductive RegionOperations.AssignedFrom (consumption : Consumption F) (region : RegionIndex) :
    List Cell → RegionOperations F → Prop where
  | nil available : AssignedFrom consumption region available []
  | cons available operation rest (cells : List Cell) (hconsumes : cells ∈ consumption operation)
      (havailable : ∀ cell ∈ cells, cell ∈ available) :
      AssignedFrom consumption region (operation.assignedCells region ++ available) rest →
        AssignedFrom consumption region available (operation :: rest)

namespace RegionOperations

variable (consumption : Consumption F) (region : RegionIndex) (available : List Cell)

@[keygen_norm, keygen_spine]
theorem assignedFrom_nil_iff : AssignedFrom consumption region available [] ↔ True :=
  ⟨fun _ => trivial, fun _ => .nil available⟩

/-- One step of the walk: the operation consumes from the accumulator, which its assignments
then extend. The keygen simp sets reduce `assignedCells` per constructor. -/
@[keygen_norm, keygen_spine]
theorem assignedFrom_cons_iff (operation : RegionOperation F) (rest : RegionOperations F) :
    AssignedFrom consumption region available (operation :: rest) ↔
      operation.ConsumesFrom consumption available ∧
        AssignedFrom consumption region (operation.assignedCells region ++ available) rest := by
  constructor
  · intro h
    cases h with
    | cons _ _ _ cells hconsumes havailable hrest =>
      exact ⟨⟨cells, hconsumes, havailable⟩, hrest⟩
  · rintro ⟨⟨cells, hconsumes, havailable⟩, hrest⟩
    exact .cons available operation rest cells hconsumes havailable hrest

end RegionOperations

/-- Available cells after executing one region body. -/
def RegionOperations.assignedCellsAfter (region : RegionIndex)
    (available : List Cell) (operations : RegionOperations F) : List Cell :=
  operations.foldl (fun cells operation =>
    operation.assignedCells region ++ cells) available

/-! The keygen sets reduce `assignedCellsAfter` structurally and keep it folded over an
opaque operation list, such as a loop's, so that a rule about that list's assigned cells can
match. -/

@[keygen_norm, keygen_spine]
theorem RegionOperations.assignedCellsAfter_nil (region : RegionIndex)
    (available : List Cell) :
    RegionOperations.assignedCellsAfter (F := F) region available [] = available := rfl

@[keygen_norm, keygen_spine]
theorem RegionOperations.assignedCellsAfter_cons (operation : RegionOperation F)
    (rest : RegionOperations F) (region : RegionIndex) (available : List Cell) :
    RegionOperations.assignedCellsAfter region available (operation :: rest) =
      RegionOperations.assignedCellsAfter region
        (operation.assignedCells region ++ available) rest := rfl

@[keygen_norm, keygen_spine]
theorem RegionOperations.assignedCellsAfter_append
    (left right : RegionOperations F) (region : RegionIndex)
    (available : List Cell) :
    (left ++ right).assignedCellsAfter region available =
      right.assignedCellsAfter region
        (left.assignedCellsAfter region available) := by
  simp only [assignedCellsAfter, List.foldl_append]

/-- Composition, with the accumulator threaded through the first fragment. -/
@[keygen_norm, keygen_spine]
theorem RegionOperations.assignedFrom_append_iff
    (consumption : Consumption F) (region : RegionIndex) (available : List Cell)
    (left right : RegionOperations F) :
    AssignedFrom consumption region available (left ++ right) ↔
      AssignedFrom consumption region available left ∧
        AssignedFrom consumption region
          (left.assignedCellsAfter region available) right := by
  induction left generalizing available with
  | nil =>
      simp only [List.nil_append, assignedCellsAfter, List.foldl_nil,
        assignedFrom_nil_iff, true_and]
  | cons operation rest inductionHypothesis =>
      simp only [List.cons_append, assignedCellsAfter, List.foldl_cons,
        assignedFrom_cons_iff, inductionHypothesis, and_assoc]

/-- Provenance remains valid when the caller makes more cells available. -/
theorem RegionOperations.AssignedFrom.mono
    {consumption : Consumption F} {operations : RegionOperations F}
    {region : RegionIndex} {available larger : List Cell}
    (hassigned : operations.AssignedFrom consumption region available)
    (havailable : ∀ cell, cell ∈ available → cell ∈ larger) :
    operations.AssignedFrom consumption region larger := by
  induction hassigned generalizing larger with
  | nil => exact .nil larger
  | cons available operation rest cells hconsumes hcells _ inductionHypothesis =>
      refine .cons larger operation rest cells hconsumes
        (fun cell hcell => havailable cell (hcells cell hcell)) (inductionHypothesis ?_)
      intro cell hcell
      rw [List.mem_append] at hcell ⊢
      exact hcell.imp_right (havailable cell)

/-- A region fragment whose operations may consume nothing is lawful for every incoming cell
state. -/
theorem RegionOperations.assignedFrom_of_forall_consumes_nil
    (consumption : Consumption F) (region : RegionIndex) (available : List Cell)
    (operations : RegionOperations F)
    (hoperations : operations.Forall fun operation => [] ∈ consumption operation) :
    operations.AssignedFrom consumption region available := by
  induction operations generalizing available with
  | nil => exact .nil available
  | cons operation rest inductionHypothesis =>
      rw [List.forall_cons] at hoperations
      exact .cons available operation rest [] hoperations.1 (fun _ hcell => nomatch hcell)
        (inductionHypothesis _ hoperations.2)

/-! ## The monoid of consumption relations

`(left * right) operation` is `left operation * right operation`, the language of
concatenations `leftCells ++ rightCells` with each half drawn from its factor, and
`(1 : Consumption F) operation` is `{[]}`. Provenance is a homomorphism from this monoid into
conjunction: `assignedFrom_mul_iff` and `assignedFrom_one`. It is not a homomorphism for the
language sum `left + right`: under the sum each operation may choose which of the two
relations to consume under, so provenance for the sum says nothing about provenance for
either relation on its own. -/

theorem Consumption.mul_apply (left right : Consumption F) (operation : RegionOperation F) :
    (left * right) operation = left operation * right operation :=
  rfl

theorem Consumption.one_apply (operation : RegionOperation F) :
    (1 : Consumption F) operation = 1 :=
  rfl

/-- Consuming nothing under a product is consuming nothing under each factor. -/
theorem Consumption.nil_mem_mul_iff (left right : Consumption F) (operation : RegionOperation F) :
    [] ∈ (left * right) operation ↔ [] ∈ left operation ∧ [] ∈ right operation := by
  rw [Consumption.mul_apply, Language.mem_mul]
  constructor
  · rintro ⟨leftCells, hleft, rightCells, hright, hnil⟩
    obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp hnil
    exact ⟨hleft, hright⟩
  · rintro ⟨hleft, hright⟩
    exact ⟨[], hleft, [], hright, rfl⟩

theorem RegionOperation.consumesFrom_mul_iff (left right : Consumption F)
    (available : List Cell) (operation : RegionOperation F) :
    ConsumesFrom (left * right) available operation ↔
      ConsumesFrom left available operation ∧ ConsumesFrom right available operation := by
  simp only [ConsumesFrom, Consumption.mul_apply, Language.mem_mul]
  constructor
  · rintro ⟨_, ⟨leftCells, hleft, rightCells, hright, rfl⟩, havailable⟩
    exact ⟨⟨leftCells, hleft, fun cell hcell => havailable cell (List.mem_append_left _ hcell)⟩,
      ⟨rightCells, hright, fun cell hcell => havailable cell (List.mem_append_right _ hcell)⟩⟩
  · rintro ⟨⟨leftCells, hleft, hleftAvailable⟩, ⟨rightCells, hright, hrightAvailable⟩⟩
    refine ⟨leftCells ++ rightCells, ⟨leftCells, hleft, rightCells, hright, rfl⟩, ?_⟩
    intro cell hcell
    rcases List.mem_append.mp hcell with hcell | hcell
    · exact hleftAvailable cell hcell
    · exact hrightAvailable cell hcell

/-- Provenance for a product of relations is provenance for each factor. -/
theorem RegionOperations.assignedFrom_mul_iff (left right : Consumption F)
    (region : RegionIndex) (available : List Cell) (operations : RegionOperations F) :
    AssignedFrom (left * right) region available operations ↔
      AssignedFrom left region available operations ∧
        AssignedFrom right region available operations := by
  induction operations generalizing available with
  | nil => simp only [assignedFrom_nil_iff, and_self]
  | cons operation rest inductionHypothesis =>
      simp only [assignedFrom_cons_iff, RegionOperation.consumesFrom_mul_iff,
        inductionHypothesis]
      exact and_and_and_comm

/-- Under the unit, every fragment is lawful for every incoming cell state. -/
theorem RegionOperations.assignedFrom_one (region : RegionIndex) (available : List Cell)
    (operations : RegionOperations F) :
    AssignedFrom 1 region available operations :=
  assignedFrom_of_forall_consumes_nil 1 region available operations
    (List.forall_iff_forall_mem.mpr fun _ _ => Language.nil_mem_one)

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

/-- An available cell stays available after any operations. As a rule, it closes a
membership in the set after an opaque loop from the caller's cells. -/
@[keygen_norm]
theorem RegionOperations.mem_assignedCellsAfter_of_mem
    (operations : RegionOperations F) (region : RegionIndex)
    (available : List Cell) (cell : Cell) (hcell : cell ∈ available) :
    cell ∈ operations.assignedCellsAfter region available := by
  rw [mem_assignedCellsAfter_iff, List.mem_append]
  exact Or.inl hcell

/-- Cells assigned by a layouter stream, with the same region-index walk used by V1. -/
def Operations.assignedCellsFrom : Operations F → RegionIndex → List Cell
  | [], _ => []
  | .region _ body :: rest, region =>
      body.assignedCells region ++ assignedCellsFrom rest (region + 1)
  | .constrainInstance _ _ _ :: rest, region => assignedCellsFrom rest region
  | .loadTable _ _ :: rest, region => assignedCellsFrom rest region

def Operations.assignedCells (operations : Operations F) : List Cell :=
  operations.assignedCellsFrom 0

/-- Execution-order provenance through the layouter stream. A public-instance constraint
consumes its cell; regions consume by their bodies. -/
inductive Operations.AssignedFrom (consumption : Consumption F) :
    RegionIndex → List Cell → Operations F → Prop where
  | nil region available : AssignedFrom consumption region available []
  | region region available name body rest :
      body.AssignedFrom consumption region available →
        AssignedFrom consumption (region + 1)
          (body.assignedCellsAfter region available) rest →
            AssignedFrom consumption region available (.region name body :: rest)
  | constrainInstance region available cell column row rest :
      cell ∈ available → AssignedFrom consumption region available rest →
        AssignedFrom consumption region available
          (.constrainInstance cell column row :: rest)
  | loadTable region available column values rest :
      AssignedFrom consumption region available rest →
        AssignedFrom consumption region available (.loadTable column values :: rest)

namespace Operations

variable (consumption : Consumption F) (region : RegionIndex) (available : List Cell)

@[keygen_norm, keygen_spine]
theorem assignedFrom_nil_iff : AssignedFrom consumption region available [] ↔ True :=
  ⟨fun _ => trivial, fun _ => .nil region available⟩

@[keygen_norm, keygen_spine]
theorem assignedFrom_region_iff (name : String) (body : RegionOperations F)
    (rest : Operations F) :
    AssignedFrom consumption region available (.region name body :: rest) ↔
      body.AssignedFrom consumption region available ∧
        AssignedFrom consumption (region + 1)
          (body.assignedCellsAfter region available) rest := by
  constructor
  · intro h
    cases h with | region _ _ _ _ _ hbody hrest => exact ⟨hbody, hrest⟩
  · rintro ⟨hbody, hrest⟩
    exact .region region available name body rest hbody hrest

@[keygen_norm, keygen_spine]
theorem assignedFrom_constrainInstance_iff (cell : Cell) (column : Column .instance) (row : ℕ)
    (rest : Operations F) :
    AssignedFrom consumption region available (.constrainInstance cell column row :: rest) ↔
      cell ∈ available ∧ AssignedFrom consumption region available rest := by
  constructor
  · intro h
    cases h with | constrainInstance _ _ _ _ _ _ hcell hrest => exact ⟨hcell, hrest⟩
  · rintro ⟨hcell, hrest⟩
    exact .constrainInstance region available cell column row rest hcell hrest

@[keygen_norm, keygen_spine]
theorem assignedFrom_loadTable_iff (column : TableColumn) (values : List F)
    (rest : Operations F) :
    AssignedFrom consumption region available (.loadTable column values :: rest) ↔
      AssignedFrom consumption region available rest := by
  constructor
  · intro h
    cases h with | loadTable _ _ _ _ _ hrest => exact hrest
  · exact AssignedFrom.loadTable region available column values rest

end Operations

/-- Layouter-level provenance remains valid when the caller makes more cells available. -/
theorem Operations.AssignedFrom.mono
    {consumption : Consumption F} {operations : Operations F} {region : RegionIndex}
    {available larger : List Cell}
    (hassigned : operations.AssignedFrom consumption region available)
    (havailable : ∀ cell, cell ∈ available → cell ∈ larger) :
    operations.AssignedFrom consumption region larger := by
  induction hassigned generalizing larger with
  | nil currentRegion => exact .nil currentRegion larger
  | region region available name body rest hbody hrest restInduction =>
      apply Operations.AssignedFrom.region region larger name body rest
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

/-- Provenance composes across appended layouter streams. The second stream may use every
caller cell and every cell assigned by the first stream. -/
theorem Operations.AssignedFrom.append
    {consumption : Consumption F} {left right : Operations F} {region : RegionIndex}
    {available : List Cell}
    (hleft : left.AssignedFrom consumption region available)
    (hright : right.AssignedFrom consumption (region + left.regionCount)
      (available ++ left.assignedCellsFrom region)) :
    (left ++ right).AssignedFrom consumption region available := by
  induction hleft with
  | nil => simpa [Operations.regionCount, Operations.assignedCellsFrom] using hright
  | region current available name body rest hbody hrest ih =>
      rw [List.cons_append, Operations.assignedFrom_region_iff]
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
      rw [List.cons_append, Operations.assignedFrom_constrainInstance_iff]
      refine ⟨hcell, ih ?_⟩
      simpa [Operations.regionCount, Operations.assignedCellsFrom] using hright
  | loadTable current available column values rest hrest ih =>
      rw [List.cons_append, Operations.assignedFrom_loadTable_iff]
      apply ih
      simpa [Operations.regionCount, Operations.assignedCellsFrom] using hright

end Halo2
