import Clean.Halo2.SynthesisSummary.Operations
import Clean.Halo2.Operations.LookupSelectors
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.List.Sort
import Mathlib.Data.List.TakeDrop

/-!
# Floor-planner region shapes

Measures each `assignRegion` body into the compact shape consumed by Halo 2's floor
planners. The measurement records the region index, touched columns, row count, and the
reduced synthesis summaries used by compositional planner proofs.

## Region shape — what participates (`layouter.rs`, `impl RegionLayouter for RegionShape`)

A `RegionShape` tracks the SET of `RegionColumn`s the region touches and its `row_count`
(`max(offset+1)`). A `RegionColumn` is either a concrete column OR a *selector* — selectors
participate in the shape and thus in slotting (`layouter.rs:189-200`, `enable_selector`
inserts `(*selector).into()`). Per Halo2-Clean operation (`Clean/Halo2/Operations.lean`):

* `assignAdvice col _ off` — inserts `Column(Advice col)`, `row_count = max(_, off+1)`.
* `assignFixed col off _` — inserts `Column(Fixed col)`, `row_count = max(_, off+1)`.
* `enableGate gate off` — a selector enable: inserts `Selector(gate.selector)`,
  `row_count = max(_, off+1)`.
* `enableLookup _ enabled off` — each gating selector `s` is enabled at `off`, so inserts
  `Selector(s)` for every `s ∈ enabled` and `row_count = max(_, off+1)`.
* `constrainEqual` / `constrainConstant` / (region-level) `constrainInstance` — do NOT
  affect the shape (`layouter.rs:276-284`).
-/

namespace Halo2

variable {F : Type}

/-! ## Indexed region walk

Pairs each `assignRegion` body with its Halo2-Clean region index (only `region`
increments; subcircuit calls appear pre-appended in the op list). Everything downstream
(placement, activations) is a fold over this list. -/

def indexedRegions : Operations F → ℕ → List (ℕ × RegionOperations F) × ℕ
  | [], i => ([], i)
  | .region _ body :: rest, i =>
      let (rs, i') := indexedRegions rest (i + 1)
      ((i, body) :: rs, i')
  | .constrainInstance _ _ _ :: rest, i => indexedRegions rest i
  | .loadTable _ _ :: rest, i => indexedRegions rest i

/-- Every indexed region comes from an actual region operation in the source stream. -/
theorem exists_region_mem_of_mem_indexedRegions
    (operations : Operations F) (initial : ℕ)
    {index : ℕ} {body : RegionOperations F}
    (hregion : (index, body) ∈ (indexedRegions operations initial).1) :
    ∃ name, .region name body ∈ operations := by
  induction operations generalizing initial with
  | nil => simp [indexedRegions] at hregion
  | cons operation rest inductionHypothesis =>
      cases operation with
      | region name currentBody =>
          simp only [indexedRegions, List.mem_cons] at hregion
          rcases hregion with hcurrent | hrest
          · injection hcurrent with _ hbody
            subst body
            exact ⟨name, by simp⟩
          · obtain ⟨sourceName, hsource⟩ :=
              inductionHypothesis (initial + 1) hrest
            exact ⟨sourceName, by simp [hsource]⟩
      | constrainInstance cell column row =>
          obtain ⟨sourceName, hsource⟩ :=
            inductionHypothesis initial hregion
          exact ⟨sourceName, by simp [hsource]⟩
      | loadTable table values =>
          obtain ⟨sourceName, hsource⟩ :=
            inductionHypothesis initial hregion
          exact ⟨sourceName, by simp [hsource]⟩

/-- Selector-activation rows: `(selectorIndex, absRow)` for every `enableGate` (its own
selector) and `enableLookup` (each enabled selector) across all regions. `place` maps a
region index to its start row. -/
def activations (starts : List ℕ) (regions : List (ℕ × RegionOperations F)) : List (ℕ × ℕ) :=
  regions.flatMap fun (idx, body) =>
    body.flatMap fun op =>
      match op with
      | .enableGate gate row => [(gate.selector.index, starts.getD idx 0 + row)]
      | .enableLookup _ enabled row =>
          enabled.map fun s => (s.index, starts.getD idx 0 + row)
      | _ => []

/-- Membership in the selector-activation stream retains its source region,
operation, and region-local row. -/
theorem mem_activations_iff
    (starts : List ℕ) (regions : List (ℕ × RegionOperations F))
    (selector absoluteRow : ℕ) :
    (selector, absoluteRow) ∈ activations starts regions ↔
      ∃ index body operation localRow,
        (index, body) ∈ regions ∧
          operation ∈ body ∧
          operation.ActivatesSelectorAt selector localRow ∧
          absoluteRow = starts.getD index 0 + localRow := by
  rw [activations, List.mem_flatMap]
  constructor
  · rintro ⟨⟨index, body⟩, hregion, hbody⟩
    rw [List.mem_flatMap] at hbody
    obtain ⟨operation, hoperation, hmapped⟩ := hbody
    cases operation with
    | enableGate gate row =>
        simp only [List.mem_singleton, Prod.mk.injEq] at hmapped
        exact ⟨index, body, .enableGate gate row, row,
          hregion, hoperation, ⟨hmapped.1.symm, rfl⟩, hmapped.2⟩
    | enableLookup argument enabled row =>
        rw [List.mem_map] at hmapped
        obtain ⟨candidate, hcandidate, hequal⟩ := hmapped
        simp only [Prod.mk.injEq] at hequal
        exact ⟨index, body, .enableLookup argument enabled row, row,
          hregion, hoperation,
          ⟨⟨candidate, hcandidate, hequal.1⟩, rfl⟩, hequal.2.symm⟩
    | assignAdvice | assignFixed | constrainEqual | constrainConstant |
        constrainInstance =>
        simp at hmapped
  · rintro ⟨index, body, operation, localRow,
      hregion, hoperation, hactivation, rfl⟩
    refine ⟨(index, body), hregion, ?_⟩
    rw [List.mem_flatMap]
    refine ⟨operation, hoperation, ?_⟩
    cases operation with
    | enableGate gate row =>
        rcases hactivation with ⟨rfl, rfl⟩
        simp
    | enableLookup argument enabled row =>
        rcases hactivation with ⟨⟨candidate, hcandidate, rfl⟩, rfl⟩
        exact List.mem_map.mpr ⟨candidate, hcandidate, rfl⟩
    | assignAdvice | assignFixed | constrainEqual | constrainConstant |
        constrainInstance =>
        contradiction

end Halo2

namespace Halo2.FloorPlanner

open Halo2

variable {F : Type}

/-! ## `RegionColumn` and its consensus-critical order

`RegionColumn` (`layouter.rs:126-132`): a concrete column or a virtual selector. Its `Ord`
(`layouter.rs:146-155`) is consensus-critical — the layouters sort a region's columns by it
before first-fit (`strategy.rs:177-178`, `region_columns.sort_unstable()`):

* concrete columns compare by `Column<Any>::Ord` (`plonk/circuit.rs:46-56`): first by the
  column *type* (`Any::Ord`, `plonk/circuit.rs:87-104`: `Instance < Advice < Fixed`), then
  by index;
* every concrete column sorts BEFORE every selector (`Column(_) < Selector(_)`);
* selectors compare by their index (`self.0.cmp(&other.0)`). -/

/- `RegionColumn` and its ordering live in `Operations.lean`, where compositional
circuit summaries can use the planner's canonical column vocabulary. -/

/-- Sort a region's column set by `RegionColumn::Ord` (`strategy.rs:177-178`). The input is a
set (deduplicated), so the order is total. -/
def sortRegionColumns (cols : List RegionColumn) : List RegionColumn :=
  cols.insertionSort fun left right =>
    RegionColumn.lt left right = true

theorem sortRegionColumns_perm (columns : List RegionColumn) :
    (sortRegionColumns columns).Perm columns := by
  exact List.perm_insertionSort
    (r := fun left right : RegionColumn =>
      RegionColumn.lt left right = true) columns

@[keygen_norm] theorem mem_sortRegionColumns_iff
    (column : RegionColumn) (columns : List RegionColumn) :
    column ∈ sortRegionColumns columns ↔ column ∈ columns :=
  (sortRegionColumns_perm columns).mem_iff

private theorem orderedInsert_append_of_rel_right
    {alpha : Type} (relation : alpha → alpha → Prop)
    [DecidableRel relation] (item : alpha) (left right : List alpha)
    (hrel : ∀ candidate ∈ right, relation item candidate) :
    List.orderedInsert relation item (left ++ right) =
      List.orderedInsert relation item left ++ right := by
  induction left with
  | nil =>
      cases right with
      | nil => rfl
      | cons head tail =>
          simp only [List.nil_append, List.orderedInsert_cons]
          rw [if_pos (hrel head (by simp))]
          simp only [List.orderedInsert_nil, List.singleton_append]
  | cons head tail inductionHypothesis =>
      simp only [List.cons_append, List.orderedInsert_cons]
      split <;> rename_i hitemHead
      · rfl
      · simp only [List.cons_append]
        rw [inductionHypothesis]

private theorem orderedInsert_append_of_not_rel_left
    {alpha : Type} (relation : alpha → alpha → Prop)
    [DecidableRel relation] (item : alpha) (left right : List alpha)
    (hrel : ∀ candidate ∈ left, ¬ relation item candidate) :
    List.orderedInsert relation item (left ++ right) =
      left ++ List.orderedInsert relation item right := by
  induction left with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      simp only [List.cons_append, List.orderedInsert_cons]
      rw [if_neg (hrel head (by simp)), inductionHypothesis]
      intro candidate hcandidate
      exact hrel candidate (by simp [hcandidate])

private theorem physical_lt_selector
    (kind : ColumnKind) (column selector : ℕ) :
    RegionColumn.lt (.column kind column) (.selector selector) = true := by
  cases kind <;> simp [RegionColumn.lt, RegionColumn.ordKey,
    RegionColumn.kindRank]

private theorem selector_not_lt_physical
    (kind : ColumnKind) (selector column : ℕ) :
    RegionColumn.lt (.selector selector) (.column kind column) ≠ true := by
  cases kind <;> simp [RegionColumn.lt, RegionColumn.ordKey,
    RegionColumn.kindRank]

private theorem sortRegionColumns_cons
    (head : RegionColumn) (tail : List RegionColumn) :
    sortRegionColumns (head :: tail) =
      List.orderedInsert (fun left right =>
        RegionColumn.lt left right = true) head
        (sortRegionColumns tail) := by
  rfl

private theorem physicalColumns_column_cons
    (kind : ColumnKind) (index : ℕ) (tail : List RegionColumn) :
    physicalColumns (.column kind index :: tail) =
      .column kind index :: physicalColumns tail := by
  rfl

private theorem physicalColumns_selector_cons
    (selector : ℕ) (tail : List RegionColumn) :
    physicalColumns (.selector selector :: tail) = physicalColumns tail := by
  rfl

private theorem selectorColumns_column_cons
    (kind : ColumnKind) (index : ℕ) (tail : List RegionColumn) :
    selectorColumns (.column kind index :: tail) = selectorColumns tail := by
  rfl

private theorem selectorColumns_selector_cons
    (selector : ℕ) (tail : List RegionColumn) :
    selectorColumns (.selector selector :: tail) =
      .selector selector :: selectorColumns tail := by
  rfl

/-- The consensus column order places every concrete column before every virtual
selector column. -/
theorem sortRegionColumns_eq_physical_append_selectors
    (columns : List RegionColumn) :
    sortRegionColumns columns =
      sortRegionColumns (physicalColumns columns) ++
        sortRegionColumns (selectorColumns columns) := by
  induction columns with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      cases head with
      | column kind index =>
          rw [sortRegionColumns_cons, physicalColumns_column_cons,
            selectorColumns_column_cons, sortRegionColumns_cons]
          rw [inductionHypothesis]
          apply orderedInsert_append_of_rel_right
          intro candidate hcandidate
          have hsource := (sortRegionColumns_perm
            (selectorColumns tail)).mem_iff.mp hcandidate
          rw [selectorColumns, List.mem_filter] at hsource
          rcases candidate with _ | selector
          · simp at hsource
          · exact physical_lt_selector kind index selector
      | selector selector =>
          rw [sortRegionColumns_cons, physicalColumns_selector_cons,
            selectorColumns_selector_cons, sortRegionColumns_cons]
          rw [inductionHypothesis]
          apply orderedInsert_append_of_not_rel_left
          intro candidate hcandidate
          have hsource := (sortRegionColumns_perm
            (physicalColumns tail)).mem_iff.mp hcandidate
          rw [physicalColumns, List.mem_filter] at hsource
          rcases candidate with ⟨kind, column⟩ | _
          · exact selector_not_lt_physical kind selector column
          · simp at hsource

/-! ## Measurement pass (`v1.rs` `MeasurementPass` / `layouter.rs` `RegionShape`) -/

/-- The shape of a region: its region index, the SET of columns it touches, and its row
count. Rust `RegionShape` (`layouter.rs:117-122`). -/
structure RegionShape where
  index : ℕ
  columns : List RegionColumn
  rowCount : ℕ
deriving Repr, Inhabited

/-- The local representation facts needed by the generic V1 allocator proof. -/
def RegionShape.WellFormed (shape : RegionShape) : Prop :=
  shape.columns.Nodup ∧
    (shape.columns ≠ [] → 0 < shape.rowCount)

/-- The index-free form of the local representation facts required by V1. -/
def RegionShapeSummary.WellFormed
    (summary : RegionShapeSummary) : Prop :=
  summary.columns.Nodup ∧
    (summary.columns ≠ [] → 0 < summary.rowCount)

/-- Add a column to a shape's set (dedup; first-seen order — the list is re-sorted by
`RegionColumn::Ord` at slotting, and the advice-count/row-count are order-independent). -/
def addCol (cols : List RegionColumn) (c : RegionColumn) : List RegionColumn :=
  addColumn cols c

/- The one-past-last row touched by a region operation is shared with compositional
summaries in `Operations.lean`. -/
-- `regionOperationRowExtent` is shared with compositional summaries in Operations.

/-- Add the columns touched by one operation to a region's measured column set. -/
def addOperationColumns
    (columns : List RegionColumn) (operation : RegionOperation F) :
    List RegionColumn :=
  (regionOperationShapeColumns operation).foldl addCol columns

/-- Measure one region body to its `RegionShape` (`layouter.rs`, `impl RegionLayouter for
RegionShape`). See the module header for the per-operation contribution. -/
def measureRegion (idx : ℕ) (body : RegionOperations F) : RegionShape :=
  let summary := regionSynthesisSummary body
  { index := idx
    columns := summary.columns
    rowCount := summary.rowCount }

/-- Turn an already-reduced region shape summary into V1's measured shape. -/
def measureRegionSummary (idx : ℕ) (summary : RegionShapeSummary) : RegionShape :=
  { index := idx
    columns := summary.columns
    rowCount := summary.rowCount }

/-- Forget the bookkeeping index of a measured region. -/
def RegionShape.toSummary (shape : RegionShape) : RegionShapeSummary where
  columns := shape.columns
  rowCount := shape.rowCount

@[simp] theorem measureRegionSummary_toSummary
    (index : ℕ) (summary : RegionShapeSummary) :
    (measureRegionSummary index summary).toSummary = summary := by
  rfl

/-- Add consecutive region indices to an ordered reduced shape sequence. -/
def indexRegionSummaries : ℕ → List RegionShapeSummary → List RegionShape
  | _, [] => []
  | index, summary :: rest =>
      measureRegionSummary index summary ::
        indexRegionSummaries (index + 1) rest

@[simp] theorem indexRegionSummaries_toSummary
    (initial : ℕ) (summaries : List RegionShapeSummary) :
    (indexRegionSummaries initial summaries).map RegionShape.toSummary =
      summaries := by
  induction summaries generalizing initial with
  | nil => rfl
  | cons summary rest inductionHypothesis =>
      simp only [indexRegionSummaries, List.map_cons,
        measureRegionSummary_toSummary, List.cons.injEq, true_and]
      exact inductionHypothesis (initial + 1)

theorem measureRegion_eq_measureRegionSummary
    (index : ℕ) (body : RegionOperations F) :
    measureRegion index body =
      measureRegionSummary index
        (regionSynthesisSummary body).toRegionShapeSummary := by
  rfl

theorem measureRegion_wellFormed
    (index : ℕ) (operations : RegionOperations F) :
    (measureRegion index operations).WellFormed := by
  constructor
  · exact regionSynthesisSummary_columns_nodup operations
  · intro hcolumns
    exact regionSynthesisSummary_rowCount_pos_of_columns_nonempty
      operations hcolumns

theorem mem_measureRegion_columns_iff
    (index : ℕ) (body : RegionOperations F) (column : RegionColumn) :
    column ∈ (measureRegion index body).columns ↔
      column ∈ (regionSynthesisSummary body).columns := by
  simp only [measureRegion]

@[circuit_norm] theorem measureRegion_rowCount
    (index : ℕ) (body : RegionOperations F) :
    (measureRegion index body).rowCount =
      (regionSynthesisSummary body).rowCount := rfl

private theorem foldl_max_accumulator_le
    {α : Type}
    (values : List α) (value : α → ℕ) (initial : ℕ) :
    initial ≤ values.foldl (fun current next => max current (value next)) initial := by
  induction values generalizing initial with
  | nil =>
      exact le_rfl
  | cons head tail ih =>
      rw [List.foldl_cons]
      exact (Nat.le_max_left _ _).trans (ih _)

/-- A member's value is bounded by a left fold of `max`. -/
theorem value_le_foldl_max_of_mem
    {α : Type}
    (values : List α) (value : α → ℕ) (initial : ℕ)
    (item : α) (hitem : item ∈ values) :
    value item ≤
      values.foldl (fun current next => max current (value next)) initial := by
  induction values generalizing initial with
  | nil =>
      simp at hitem
  | cons head tail ih =>
      rw [List.mem_cons] at hitem
      rw [List.foldl_cons]
      rcases hitem with rfl | htail
      · exact (Nat.le_max_right _ _).trans
          (foldl_max_accumulator_le tail value _)
      · exact ih _ htail

/-- Every lookup activation row is strictly below its measured region extent. -/
theorem row_lt_measureRegion_of_enableLookup_mem
    (idx : ℕ) (body : RegionOperations F)
    (argument : LookupArgument F) (enabled : List Selector) (row : ℕ)
    (hlookup : RegionOperation.enableLookup argument enabled row ∈ body) :
    row < (measureRegion idx body).rowCount := by
  rw [Nat.lt_iff_add_one_le]
  exact regionOperationRowExtent_le_synthesisSummary_of_mem body
    (.enableLookup argument enabled row) hlookup

/-- Measure every `assignRegion` region (in region-index order; `loadTable`/layouter-level
`constrainInstance` are not measured — V1 `assign_table` is a no-op in the measurement pass,
`v1.rs:183-184`). -/
def measureRegions (ops : Operations F) : List RegionShape :=
  (indexedRegions ops 0).1.map fun (idx, body) => measureRegion idx body

theorem measureRegions_wellFormed (operations : Operations F) :
    (measureRegions operations).Forall RegionShape.WellFormed := by
  rw [List.forall_iff_forall_mem]
  intro shape hshape
  rw [measureRegions, List.mem_map] at hshape
  obtain ⟨region, hregion, rfl⟩ := hshape
  exact measureRegion_wellFormed region.1 region.2

/-- V1's complete measurement input is exactly the ordered reduced shape sequence
published by the synthesis summary. -/
theorem measureRegions_eq_synthesisSummary_regionShapes
    (ops : Operations F) :
    measureRegions ops =
      indexRegionSummaries 0 (synthesisSummary ops).regionShapes := by
  have general : ∀ (operations : Operations F) (initial : ℕ),
      (indexedRegions operations initial).1.map
          (fun (index, body) => measureRegion index body) =
        indexRegionSummaries initial
          (synthesisSummary operations).regionShapes := by
    intro operations
    induction operations with
    | nil => intro initial; rfl
    | cons operation rest inductionHypothesis =>
        intro initial
        cases operation with
        | region name body =>
            simp only [indexedRegions, List.map_cons, synthesisSummary,
              SynthesisSummary.combine_regionShapes,
              SynthesisSummary.ofRegion_regionShapes, List.singleton_append,
              indexRegionSummaries, measureRegion_eq_measureRegionSummary]
            congr 1
            simpa only [measureRegion_eq_measureRegionSummary] using
              inductionHypothesis (initial + 1)
        | constrainInstance cell column row =>
            simpa only [indexedRegions, synthesisSummary] using
              inductionHypothesis initial
        | loadTable column values =>
            simpa only [indexedRegions, synthesisSummary] using
              inductionHypothesis initial
  exact general ops 0

/-- Every index-free region summary produced by synthesis satisfies the local
representation facts required by V1. -/
theorem synthesisSummary_regionShapes_wellFormed
    (operations : Operations F) :
    (synthesisSummary operations).regionShapes.Forall
      RegionShapeSummary.WellFormed := by
  have hmeasured := measureRegions_wellFormed operations
  rw [measureRegions_eq_synthesisSummary_regionShapes] at hmeasured
  have general : ∀ (initial : ℕ) (summaries : List RegionShapeSummary),
      (indexRegionSummaries initial summaries).Forall RegionShape.WellFormed →
        summaries.Forall RegionShapeSummary.WellFormed := by
    intro initial summaries
    induction summaries generalizing initial with
    | nil => simp
    | cons summary rest inductionHypothesis =>
        intro hwellFormed
        simp only [indexRegionSummaries, List.forall_cons,
          RegionShape.WellFormed, RegionShapeSummary.WellFormed,
          measureRegionSummary] at hwellFormed ⊢
        exact ⟨hwellFormed.1,
          inductionHypothesis (initial + 1) hwellFormed.2⟩
  exact general 0 _ hmeasured

/-- Total length occupied in one planner column.  Shared-column intervals are
row-disjoint under V1, so this compositional sum is exact. -/
def columnOccupiedLength (shapes : List RegionShape) (column : RegionColumn) : ℕ :=
  match shapes with
  | [] => 0
  | shape :: rest =>
      (if column ∈ shape.columns then shape.rowCount else 0) +
        columnOccupiedLength rest column

theorem columnOccupiedLength_nil (column : RegionColumn) :
    columnOccupiedLength [] column = 0 := rfl

theorem columnOccupiedLength_cons
    (shape : RegionShape) (rest : List RegionShape) (column : RegionColumn) :
    columnOccupiedLength (shape :: rest) column =
      (if column ∈ shape.columns then shape.rowCount else 0) +
        columnOccupiedLength rest column := rfl

theorem indexedRegions_indices_eq_range
    (ops : Operations F) (initial : ℕ) :
    (indexedRegions ops initial).1.map Prod.fst =
      List.range' initial ops.regionCount := by
  induction ops generalizing initial with
  | nil => rfl
  | cons operation rest inductionHypothesis =>
      cases operation with
      | region name body =>
          simp only [indexedRegions, Operations.regionCount,
            List.map_cons]
          rw [inductionHypothesis]
          rw [show 1 + Operations.regionCount rest =
              Operations.regionCount rest + 1 by omega,
            List.range'_succ]
      | constrainInstance cell column row =>
          simpa only [indexedRegions, Operations.regionCount] using
            inductionHypothesis initial
      | loadTable table values =>
          simpa only [indexedRegions, Operations.regionCount] using
            inductionHypothesis initial

private theorem eq_of_mem_of_map_nodup
    {α β : Type} (items : List α) (key : α → β)
    (hnodup : (items.map key).Nodup)
    {left right : α} (hleft : left ∈ items) (hright : right ∈ items)
    (hkey : key left = key right) :
    left = right := by
  induction items with
  | nil => simp at hleft
  | cons head rest inductionHypothesis =>
      rw [List.map_cons, List.nodup_cons] at hnodup
      simp only [List.mem_cons] at hleft hright
      rcases hleft with rfl | hleft <;> rcases hright with rfl | hright
      · rfl
      · exfalso
        exact hnodup.1 (List.mem_map.mpr ⟨right, hright, hkey.symm⟩)
      · exfalso
        exact hnodup.1 (List.mem_map.mpr ⟨left, hleft, hkey⟩)
      · exact inductionHypothesis hnodup.2 hleft hright

/-- The region index assigned by `indexedRegions` uniquely identifies its body. -/
theorem indexedRegions_eq_of_index_eq
    (operations : Operations F) (initial : ℕ)
    {left right : ℕ × RegionOperations F}
    (hleft : left ∈ (indexedRegions operations initial).1)
    (hright : right ∈ (indexedRegions operations initial).1)
    (hindex : left.1 = right.1) :
    left = right := by
  apply eq_of_mem_of_map_nodup
    (indexedRegions operations initial).1 Prod.fst
  · rw [indexedRegions_indices_eq_range]
    exact List.nodup_range'
  · exact hleft
  · exact hright
  · exact hindex

theorem measureRegions_indices_nodup (ops : Operations F) :
    ((measureRegions ops).map (·.index)).Nodup := by
  have hmap :
      (measureRegions ops).map (·.index) =
        (indexedRegions ops 0).1.map Prod.fst := by
    simp [measureRegions, measureRegion]
  rw [hmap, indexedRegions_indices_eq_range]
  exact List.nodup_range'

theorem measureRegions_indices_eq_range (operations : Operations F) :
    (measureRegions operations).map (·.index) =
      List.range operations.regionCount := by
  have hmap :
      (measureRegions operations).map (·.index) =
        (indexedRegions operations 0).1.map Prod.fst := by
    simp [measureRegions, measureRegion]
  rw [hmap, indexedRegions_indices_eq_range]
  exact List.range_eq_range'.symm

theorem synthesisSummary_columnOccupancy_eq
    (ops : Operations F) (column : RegionColumn) :
    (synthesisSummary ops).columnOccupancy column =
      columnOccupiedLength (measureRegions ops) column := by
  have general : ∀ (operations : Operations F) (initial : ℕ),
      (synthesisSummary operations).columnOccupancy column =
        columnOccupiedLength
          ((indexedRegions operations initial).1.map fun (index, body) =>
            measureRegion index body) column := by
    intro operations
    induction operations with
    | nil =>
        intro initial
        rfl
    | cons operation rest inductionHypothesis =>
        intro initial
        cases operation with
        | region name body =>
            simp only [synthesisSummary, SynthesisSummary.combine,
              SynthesisSummary.ofRegion, indexedRegions, List.map_cons,
              columnOccupiedLength_cons]
            simp only [mem_measureRegion_columns_iff,
              measureRegion_rowCount]
            congr 1
            simpa only [] using inductionHypothesis (initial + 1)
        | constrainInstance cell instanceColumn row =>
            simpa only [synthesisSummary, SynthesisSummary.combine,
              SynthesisSummary.ofInstanceRow, Nat.zero_add, indexedRegions] using
              inductionHypothesis initial
        | loadTable table values =>
            simpa only [synthesisSummary, SynthesisSummary.combine,
              SynthesisSummary.ofTableValues, Nat.zero_add, indexedRegions] using
              inductionHypothesis initial
  simpa only [measureRegions] using general ops 0

/-- Number of distinct advice columns the region touches (the V1 sort key's factor). -/
def RegionShape.adviceCols (s : RegionShape) : ℕ :=
  (s.columns.filter RegionColumn.isAdvice).length

/-- The V1 sort key: `advice_cols * row_count` — "advice area", the contention proxy
(`strategy.rs:202-214`). -/
def RegionShape.key (s : RegionShape) : ℕ := s.adviceCols * s.rowCount

/-- Index-free advice-column count used by V1's sort key. -/
def RegionShapeSummary.adviceCols (summary : RegionShapeSummary) : ℕ :=
  (summary.columns.filter RegionColumn.isAdvice).length

/-- The V1 sort key on an index-free reduced region summary. -/
def RegionShapeSummary.key (summary : RegionShapeSummary) : ℕ :=
  summary.adviceCols * summary.rowCount

theorem RegionShape.toSummary_key (shape : RegionShape) :
    shape.toSummary.key = shape.key := rfl

end Halo2.FloorPlanner
