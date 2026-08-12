import Clean.Halo2.Operations
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.List.Sort
import Mathlib.Data.List.TakeDrop

/-!
# Floor planner: deriving region placements from the operation stream

Computes `starts : List ℕ` — the start row per `assignRegion`-index region — purely from
the Halo2-Clean `Operations`, by porting halo2's floor planners. This is the region
placement input to the keygen-view activation table and to the domain-size derivation.

Two planners, matching the Rust module split (`halo2_proofs/src/circuit/floor_planner`):

* **`V1`** (`v1.rs`, `v1/strategy.rs`) — the planner the real orchard `Circuit` declares
  (`orchard/src/circuit.rs`, `type FloorPlanner = V1`, with the
  `floor-planner-v1-legacy-pdqsort` feature). A dual pass:
  a measurement pass computes each region's shape (`measureRegions`/`RegionShape`), then
  a greedy first-fit places the regions biggest-advice-area first
  (`slot_in_biggest_advice_first` + `slot_in` + `first_fit_region`). Drives the Action
  fixtures.
* **`SimpleFloorPlanner`** (`single_pass.rs`) — sequential per-region placement at the
  earliest row where none of the region's columns are in use. Drives the Add/Mul fixtures.

Everything is `#eval`-computable. V1's first-fit allocator is proved generically to
place regions sharing a column in disjoint row intervals. Tests can `#guard`/`#eval`
the derived starts against fixture placements.

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

/-- Concrete columns in a region footprint. -/
def physicalColumns (columns : List RegionColumn) : List RegionColumn :=
  columns.filter fun
    | .column _ _ => true
    | .selector _ => false

/-- Virtual selector columns in a region footprint. -/
def selectorColumns (columns : List RegionColumn) : List RegionColumn :=
  columns.filter fun
    | .column _ _ => false
    | .selector _ => true

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
            simpa only [synthesisSummary, indexedRegions] using
              inductionHypothesis initial
        | loadTable table values =>
            simpa only [synthesisSummary, indexedRegions] using
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

/-! ## Legacy pdqsort (`floor-planner-v1-legacy-pdqsort`)

The Action circuit shapes have MANY tied sort keys (e.g. every "witness message piece"
region shares a shape), and V1 sorts by that key before reversing and slotting
(`strategy.rs:198-242`). With the `floor-planner-v1-legacy-pdqsort` feature — which orchard
enables — pinning the VK against the sort order, the sort is
`halo2_legacy_pdqsort::sort::quicksort`, a byte-for-byte copy of Rust 1.56.1's std
unstable pdqsort (fixed to its 64-bit behaviour). Because the keys tie, that exact
tie-breaking permutation is VK-consensus-critical, so we port the algorithm faithfully
rather than using a stable sort.

The port mirrors `halo2_legacy_pdqsort-0.1.0/src/sort.rs` function-for-function; the sole
representation change is pointers → `Array` indices (`width(l,r) = r - l`). The comparator
is `is_less a b = key a < key b`. -/

namespace Pdqsort

variable {T : Type} [Inhabited T]

/-! ### Ordering vocabulary

The legacy implementation receives a Boolean comparator.  Its floor-planner use is
always a comparison through a natural-number key, so state the semantic contract at
that exact level: this avoids manufacturing an unrelated non-strict order from an
arbitrary Boolean function while remaining generic in the element type and key.
-/

/-- The comparator used by the verified ordering interface. -/
def lessBy (key : T → ℕ) (left right : T) : Bool :=
  decide (key left < key right)

omit [Inhabited T] in
theorem lessBy_eq_true_iff (key : T → ℕ) (left right : T) :
    lessBy key left right = true ↔ key left < key right := by
  simp [lessBy]

omit [Inhabited T] in
theorem lessBy_eq_false_iff (key : T → ℕ) (left right : T) :
    lessBy key left right = false ↔ key right ≤ key left := by
  simp [lessBy]

/-- A list is nondecreasing in the supplied natural-number key. -/
def KeySorted (key : T → ℕ) (items : List T) : Prop :=
  (items.map key).SortedLE

/-- Every key in `items` is at most `bound`. -/
def KeysLE (key : T → ℕ) (items : List T) (bound : ℕ) : Prop :=
  ∀ item ∈ items, key item ≤ bound

/-- Every key in `items` is at least `bound`. -/
def KeysGE (key : T → ℕ) (items : List T) (bound : ℕ) : Prop :=
  ∀ item ∈ items, bound ≤ key item

/-- A pointwise predicate over the half-open array interval `[start, stop)`. -/
def RangeAll (array : Array T) (start stop : ℕ) (predicate : T → Prop) : Prop :=
  ∀ index, start ≤ index → index < stop → predicate array[index]!

theorem RangeAll.mono
    {array : Array T} {outerStart outerStop innerStart innerStop : ℕ}
    {predicate : T → Prop}
    (h : RangeAll array outerStart outerStop predicate)
    (hstart : outerStart ≤ innerStart) (hstop : innerStop ≤ outerStop) :
    RangeAll array innerStart innerStop predicate := by
  intro index hindexStart hindexStop
  exact h index (hstart.trans hindexStart) (hindexStop.trans_le hstop)

theorem RangeAll.empty
    (array : Array T) (index : ℕ) (predicate : T → Prop) :
    RangeAll array index index predicate := by
  intro _ _ h
  omega

theorem RangeAll.append
    {array : Array T} {start middle stop : ℕ}
    {predicate : T → Prop}
    (hleft : RangeAll array start middle predicate)
    (hright : RangeAll array middle stop predicate) :
    RangeAll array start stop predicate := by
  intro index hstart hstop
  by_cases hmiddle : index < middle
  · exact hleft index hstart hmiddle
  · exact hright index (by omega) hstop

theorem RangeAll.transfer
    {before after : Array T} {start stop : ℕ}
    {predicate : T → Prop}
    (hbefore : RangeAll before start stop predicate)
    (heq : ∀ index, start ≤ index → index < stop →
      after[index]! = before[index]!) :
    RangeAll after start stop predicate := by
  intro index hstart hstop
  rw [heq index hstart hstop]
  exact hbefore index hstart hstop

/-- A range predicate applies to every member of the corresponding extracted
array. -/
theorem RangeAll.forall_mem_extract
    {array : Array T} {start stop : ℕ} {predicate : T → Prop}
    (h : RangeAll array start stop predicate)
    (hstart : start ≤ stop) (hstop : stop ≤ array.size) :
    ∀ item ∈ (array.extract start stop).toList, predicate item := by
  intro item hitem
  obtain ⟨position, hposition⟩ := List.get_of_mem hitem
  have hpositionBound : position.val < stop - start := by
    have := position.isLt
    have hbounds : position.val < stop - start ∧
        position.val < array.size - start := by
      simpa [Array.size_extract, Nat.min_eq_left hstop] using this
    exact hbounds.1
  have hitemValue : item = array[start + position.val]! := by
    rw [← hposition, List.get_eq_getElem,
      Array.getElem_toList position.isLt,
      Array.getElem_extract position.isLt]
    rw [getElem!_pos array (start + position.val) (by omega)]
  rw [hitemValue]
  exact h (start + position.val) (by omega) (by omega)

theorem RangeAll.keysLE_extract
    (key : T → ℕ) (array : Array T) (start stop bound : ℕ)
    (h : RangeAll array start stop (fun item => key item ≤ bound))
    (hstart : start ≤ stop) (hstop : stop ≤ array.size) :
    KeysLE key (array.extract start stop).toList bound :=
  h.forall_mem_extract hstart hstop

theorem RangeAll.keysGE_extract
    (key : T → ℕ) (array : Array T) (start stop bound : ℕ)
    (h : RangeAll array start stop (fun item => bound ≤ key item))
    (hstart : start ≤ stop) (hstop : stop ≤ array.size) :
    KeysGE key (array.extract start stop).toList bound :=
  h.forall_mem_extract hstart hstop

omit [Inhabited T] in
theorem KeySorted.of_constant
    (key : T → ℕ) (items : List T) (value : ℕ)
    (h : ∀ item ∈ items, key item = value) :
    KeySorted key items := by
  rw [KeySorted, List.sortedLE_iff_pairwise, List.pairwise_map]
  induction items with
  | nil => exact List.Pairwise.nil
  | cons head rest inductionHypothesis =>
      rw [List.pairwise_cons]
      refine ⟨?_, inductionHypothesis (by
        intro item hitem
        exact h item (by simp [hitem]))⟩
      intro item hitem
      rw [h head (by simp), h item (by simp [hitem])]

omit [Inhabited T] in
theorem KeySorted.nil (key : T → ℕ) : KeySorted key [] := by
  rw [KeySorted, List.sortedLE_iff_pairwise]
  exact List.Pairwise.nil

omit [Inhabited T] in
theorem KeySorted.singleton (key : T → ℕ) (item : T) :
    KeySorted key [item] := by
  rw [KeySorted, List.sortedLE_iff_pairwise]
  exact List.Pairwise.cons (by simp) List.Pairwise.nil

omit [Inhabited T] in
theorem KeySorted.append
    (key : T → ℕ) (left right : List T)
    (hleft : KeySorted key left) (hright : KeySorted key right)
    (hcross : ∀ a ∈ left, ∀ b ∈ right, key a ≤ key b) :
    KeySorted key (left ++ right) := by
  rw [KeySorted, List.map_append, List.sortedLE_iff_pairwise] at *
  exact List.pairwise_append.mpr ⟨hleft, hright, by
    intro a ha b hb
    rw [List.mem_map] at ha hb
    obtain ⟨a, ha, rfl⟩ := ha
    obtain ⟨b, hb, rfl⟩ := hb
    exact hcross a ha b hb⟩

omit [Inhabited T] in
theorem KeysLE.perm
    (key : T → ℕ) {left right : List T}
    (hperm : left.Perm right) {bound : ℕ}
    (h : KeysLE key left bound) : KeysLE key right bound := by
  intro item hitem
  exact h item (hperm.mem_iff.mpr hitem)

omit [Inhabited T] in
theorem KeysGE.perm
    (key : T → ℕ) {left right : List T}
    (hperm : left.Perm right) {bound : ℕ}
    (h : KeysGE key left bound) : KeysGE key right bound := by
  intro item hitem
  exact h item (hperm.mem_iff.mpr hitem)

theorem KeysGE.get!
    (key : T → ℕ) (array : Array T) (bound index : ℕ)
    (h : KeysGE key array.toList bound) (hindex : index < array.size) :
    bound ≤ key array[index]! := by
  apply h array[index]!
  rw [getElem!_pos array index hindex]
  have hlistIndex : index < array.toList.length := by simpa using hindex
  have hmem := List.getElem_mem (l := array.toList) (n := index) hlistIndex
  simpa only [Array.getElem_toList hindex] using hmem

theorem KeysGE.extract
    (key : T → ℕ) (array : Array T) (start stop bound : ℕ)
    (h : KeysGE key array.toList bound)
    (hstart : start ≤ stop) (hstop : stop ≤ array.size) :
    KeysGE key (array.extract start stop).toList bound := by
  apply RangeAll.keysGE_extract key array start stop bound _ hstart hstop
  intro index _ hindex
  exact KeysGE.get! key array bound index h (by omega)

omit [Inhabited T] in
theorem KeySorted.append_pivot
    (key : T → ℕ) (left : List T) (pivot : T) (right : List T)
    (hleft : KeySorted key left) (hright : KeySorted key right)
    (hleftBound : KeysLE key left (key pivot))
    (hrightBound : KeysGE key right (key pivot)) :
    KeySorted key (left ++ pivot :: right) := by
  apply KeySorted.append key left (pivot :: right) hleft
  · rw [KeySorted, List.map_cons, List.sortedLE_iff_pairwise,
      List.pairwise_cons]
    exact ⟨by
      intro value hvalue
      rw [List.mem_map] at hvalue
      obtain ⟨item, hitem, rfl⟩ := hvalue
      exact hrightBound item hitem, hright.pairwise⟩
  · intro leftItem hleftItem rightItem hrightItem
    rw [List.mem_cons] at hrightItem
    rcases hrightItem with rfl | hrightItem
    · exact hleftBound leftItem hleftItem
    · exact (hleftBound leftItem hleftItem).trans
        (hrightBound rightItem hrightItem)

private theorem array_toList_getElem! (array : Array T) (index : ℕ) :
    array.toList[index]! = array[index]! := by
  by_cases hindex : index < array.size
  · rw [getElem!_pos array.toList index (by simpa using hindex),
      getElem!_pos array index hindex]
    simp
  · rw [getElem!_neg array.toList index (by simpa using hindex),
      getElem!_neg array index hindex]

theorem KeySorted.keysLE_take_succ
    (key : T → ℕ) (items : List T) (index : ℕ)
    (hsorted : KeySorted key items) (hindex : index < items.length) :
    KeysLE key (items.take (index + 1)) (key items[index]!) := by
  rw [KeySorted, List.sortedLE_iff_pairwise, List.pairwise_map] at hsorted
  intro item hitem
  obtain ⟨position, hposition⟩ := List.get_of_mem hitem
  have hpositionLe : position.val ≤ index := by
    have := position.isLt
    simp only [List.length_take,
      Nat.min_eq_left (show index + 1 ≤ items.length by omega)] at this
    omega
  have hrelation := hsorted.rel_get_of_le
    (a := ⟨position.val, hpositionLe.trans_lt hindex⟩)
    (b := ⟨index, hindex⟩) hpositionLe
  rw [List.get_eq_getElem, List.get_eq_getElem] at hrelation
  rw [← hposition]
  simpa only [List.get_eq_getElem, List.getElem_take,
    getElem!_pos items index hindex] using hrelation

theorem KeySorted.keysGE_drop_succ
    (key : T → ℕ) (items : List T) (index : ℕ)
    (hsorted : KeySorted key items) (hindex : index < items.length) :
    KeysGE key (items.drop (index + 1)) (key items[index]!) := by
  rw [KeySorted, List.sortedLE_iff_pairwise, List.pairwise_map] at hsorted
  intro item hitem
  obtain ⟨position, hposition⟩ := List.get_of_mem hitem
  have horiginalLt : index + 1 + position.val < items.length := by
    have := position.isLt
    simp only [List.length_drop] at this
    omega
  have hrelation := hsorted.rel_get_of_lt
    (a := ⟨index, hindex⟩)
    (b := ⟨index + 1 + position.val, horiginalLt⟩) (by
      simp only [Fin.mk_lt_mk]
      omega)
  rw [List.get_eq_getElem, List.get_eq_getElem] at hrelation
  rw [← hposition]
  simpa only [List.get_eq_getElem, List.getElem_drop,
    getElem!_pos items index hindex] using hrelation

omit [Inhabited T] in
theorem KeySorted.take (key : T → ℕ) (items : List T) (count : ℕ)
    (h : KeySorted key items) : KeySorted key (items.take count) := by
  rw [KeySorted, List.sortedLE_iff_pairwise, List.pairwise_map] at h ⊢
  exact h.take

omit [Inhabited T] in
theorem KeySorted.drop (key : T → ℕ) (items : List T) (count : ℕ)
    (h : KeySorted key items) : KeySorted key (items.drop count) := by
  rw [KeySorted, List.sortedLE_iff_pairwise, List.pairwise_map] at h ⊢
  exact h.drop

omit [Inhabited T] in
theorem KeySorted.set
    (key : T → ℕ) (items : List T) (index : ℕ) (item : T)
    (hsorted : KeySorted key items) (hindex : index < items.length)
    (hprefix : KeysLE key (items.take index) (key item))
    (hsuffix : KeysGE key (items.drop (index + 1)) (key item)) :
    KeySorted key (items.set index item) := by
  rw [List.set_eq_take_cons_drop item hindex]
  exact KeySorted.append_pivot key _ item _
    (KeySorted.take key items index hsorted)
    (KeySorted.drop key items (index + 1) hsorted)
    hprefix hsuffix

private theorem take_append_last (items : List T) (hitems : 0 < items.length) :
    items.take (items.length - 1) ++ [items[items.length - 1]!] = items := by
  rw [← List.dropLast_eq_take,
    getElem!_pos items (items.length - 1) (by omega),
    ← List.getLast_eq_getElem]
  exact List.dropLast_append_getLast (by
    intro hnil
    simp [hnil] at hitems)

theorem KeySorted.keysLE_last
    (key : T → ℕ) (items : List T)
    (hsorted : KeySorted key items) (hitems : 0 < items.length) :
    KeysLE key items (key items[items.length - 1]!) := by
  rw [KeySorted, List.sortedLE_iff_pairwise, List.pairwise_map] at hsorted
  intro item hitem
  have hrelation := hsorted.rel_getLast hitem
  rw [List.getLast_eq_getElem (by
    intro hnil
    simp [hnil] at hitems)] at hrelation
  simpa [getElem!_pos items (items.length - 1) (by omega)] using hrelation

/-- Stable insertion used to state the pure semantics of pdqsort's shifting
insertion-sort primitive. Equal keys remain in their original order. -/
def insertByKey (key : T → ℕ) (item : T) : List T → List T
  | [] => [item]
  | head :: rest =>
      if key item < key head then
        item :: head :: rest
      else
        head :: insertByKey key item rest

omit [Inhabited T] in
theorem mem_insertByKey_iff
    (key : T → ℕ) (item candidate : T) (items : List T) :
    candidate ∈ insertByKey key item items ↔
      candidate = item ∨ candidate ∈ items := by
  induction items with
  | nil => simp [insertByKey]
  | cons head rest inductionHypothesis =>
      simp only [insertByKey]
      split <;> simp_all [or_left_comm]

omit [Inhabited T] in
theorem insertByKey_perm
    (key : T → ℕ) (item : T) (items : List T) :
    (insertByKey key item items).Perm (item :: items) := by
  induction items with
  | nil => exact .refl _
  | cons head rest inductionHypothesis =>
      simp only [insertByKey]
      split
      · exact .refl _
      · exact (inductionHypothesis.cons head).trans (.swap _ _ _)

omit [Inhabited T] in
theorem insertByKey_eq_append
    (key : T → ℕ) (item : T) (items : List T)
    (hbound : KeysLE key items (key item)) :
    insertByKey key item items = items ++ [item] := by
  induction items with
  | nil => rfl
  | cons head rest inductionHypothesis =>
      have hhead := hbound head (by simp)
      have hnotBefore : ¬key item < key head := by omega
      rw [Pdqsort.insertByKey, if_neg hnotBefore,
        inductionHypothesis (by
          intro candidate hcandidate
          exact hbound candidate (by simp [hcandidate])),
        List.cons_append]

omit [Inhabited T] in
theorem KeySorted.insertByKey
    (key : T → ℕ) (item : T) (items : List T)
    (hitems : KeySorted key items) :
    KeySorted key (insertByKey key item items) := by
  rw [KeySorted, List.sortedLE_iff_pairwise] at hitems ⊢
  induction items with
  | nil =>
      exact List.Pairwise.cons (by simp) List.Pairwise.nil
  | cons head rest inductionHypothesis =>
      change List.Pairwise (fun left right : ℕ => left ≤ right)
        (key head :: rest.map key) at hitems
      rw [List.pairwise_cons] at hitems
      by_cases hbefore : key item < key head
      · rw [Pdqsort.insertByKey, if_pos hbefore, List.map_cons, List.map_cons,
          List.pairwise_cons]
        exact ⟨by
          intro value hvalue
          rw [List.mem_cons] at hvalue
          rcases hvalue with rfl | hvalue
          · exact hbefore.le
          · exact hbefore.le.trans (hitems.1 value hvalue),
          List.Pairwise.cons hitems.1 hitems.2⟩
      · rw [Pdqsort.insertByKey, if_neg hbefore, List.map_cons, List.pairwise_cons]
        have hrestSorted := inductionHypothesis hitems.2
        refine ⟨?_, hrestSorted⟩
        intro value hvalue
        rw [List.mem_map] at hvalue
        obtain ⟨candidate, hcandidate, rfl⟩ := hvalue
        rw [mem_insertByKey_iff] at hcandidate
        rcases hcandidate with rfl | hcandidate
        · omega
        · exact hitems.1 (key candidate) (by
            rw [List.mem_map]
            exact ⟨_, hcandidate, rfl⟩)

/-- Pure left-to-right insertion sort matching the small-slice path's stable
equal-key behavior. -/
def insertionSortByKey (key : T → ℕ) (items : List T) : List T :=
  items.foldl (fun sorted item => insertByKey key item sorted) []

omit [Inhabited T] in
theorem insertionSortByKey_sorted (key : T → ℕ) (items : List T) :
    KeySorted key (insertionSortByKey key items) := by
  unfold insertionSortByKey
  generalize hsorted : ([] : List T) = sorted
  have hinitial : KeySorted key sorted := by
    rw [← hsorted]
    exact KeySorted.nil key
  clear hsorted
  induction items generalizing sorted with
  | nil => exact hinitial
  | cons item rest inductionHypothesis =>
      simp only [List.foldl_cons]
      exact inductionHypothesis _
        (KeySorted.insertByKey key item sorted hinitial)

omit [Inhabited T] in
theorem insertionSortByKey_perm (key : T → ℕ) (items : List T) :
    (insertionSortByKey key items).Perm items := by
  unfold insertionSortByKey
  have hfold : ∀ (remaining accumulator : List T),
      (remaining.foldl
        (fun sorted item => insertByKey key item sorted) accumulator).Perm
        (remaining.reverse ++ accumulator) := by
    intro remaining
    induction remaining with
    | nil => intro accumulator; exact .refl _
    | cons item rest inductionHypothesis =>
        intro accumulator
        simp only [List.foldl_cons, List.reverse_cons, List.append_assoc]
        exact (inductionHypothesis (insertByKey key item accumulator)).trans
          ((List.Perm.refl rest.reverse).append
            (insertByKey_perm key item accumulator))
  have hresult := hfold items []
  rw [List.append_nil] at hresult
  exact hresult.trans (List.reverse_perm items)

/-- Swap two array entries by index (`slice::swap`). -/
@[inline] def swp (a : Array T) (i j : ℕ) : Array T :=
  let x := a[i]!
  let y := a[j]!
  (a.set! i y).set! j x

theorem swp_size (array : Array T) (left right : ℕ) :
    (swp array left right).size = array.size := by
  simp [swp, Array.set!]

theorem swp_get!
    (array : Array T) (left right index : ℕ)
    (hleft : left < array.size) (hright : right < array.size) :
    (swp array left right)[index]! =
      if index = left then array[right]!
      else if index = right then array[left]!
      else array[index]! := by
  by_cases hindex : index < array.size
  · rw [getElem!_pos _ _ (by simpa [swp_size] using hindex)]
    simp only [swp, Array.set!]
    rw [Array.getElem_setIfInBounds (xs :=
      array.setIfInBounds left array[right]!) (by simpa using hindex)]
    by_cases hindexRight : right = index
    · rw [if_pos hindexRight]
      subst index
      by_cases heq : right = left
      · subst left
        simp
      · simp [heq]
    · rw [if_neg hindexRight, Array.getElem_setIfInBounds hindex]
      by_cases hindexLeft : left = index
      · rw [if_pos hindexLeft]
        subst index
        simp
      · rw [if_neg hindexLeft]
        simp [Ne.symm hindexLeft, Ne.symm hindexRight,
          getElem!_pos array index hindex]
  · have hindexLeft : index ≠ left := by
      intro heq
      subst index
      exact hindex hleft
    have hindexRight : index ≠ right := by
      intro heq
      subst index
      exact hindex hright
    rw [getElem!_neg _ _ (by simpa [swp_size] using hindex)]
    simp [hindexLeft, hindexRight,
      getElem!_neg array index hindex]

theorem set!_get!
    (array : Array T) (target index : ℕ) (value : T)
    (htarget : target < array.size) :
    (array.set! target value)[index]! =
      if index = target then value else array[index]! := by
  by_cases hindex : index < array.size
  · rw [getElem!_pos _ _ (by simpa [Array.set!] using hindex)]
    simp only [Array.set!]
    rw [Array.getElem_setIfInBounds (by simpa using hindex)]
    by_cases heq : target = index
    · rw [if_pos heq]
      subst index
      simp
    · rw [if_neg heq]
      simp [Ne.symm heq, getElem!_pos array index hindex]
  · have hne : index ≠ target := by
      intro heq
      subst index
      exact hindex htarget
    rw [getElem!_neg _ _ (by simpa [Array.set!] using hindex)]
    simp [hne, getElem!_neg array index hindex]

theorem RangeAll.swp
    (array : Array T) (left right start stop : ℕ)
    (predicate : T → Prop)
    (hleft : left < array.size) (hright : right < array.size)
    (h : RangeAll array start stop predicate)
    (hleftValue : start ≤ left → left < stop → predicate array[right]!)
    (hrightValue : start ≤ right → right < stop → predicate array[left]!) :
    RangeAll (swp array left right) start stop predicate := by
  intro index hindexStart hindexStop
  rw [swp_get! array left right index hleft hright]
  by_cases hindexLeft : index = left
  · rw [if_pos hindexLeft]
    exact hleftValue (hindexLeft ▸ hindexStart) (hindexLeft ▸ hindexStop)
  · rw [if_neg hindexLeft]
    by_cases hindexRight : index = right
    · rw [if_pos hindexRight]
      exact hrightValue (hindexRight ▸ hindexStart)
        (hindexRight ▸ hindexStop)
    · rw [if_neg hindexRight]
      exact h index hindexStart hindexStop

/-- Write `sub` back into `a` starting at `start` (reflecting a mutated sub-slice). -/
def overwrite (a : Array T) (start : ℕ) (sub : Array T) : Array T := Id.run do
  let mut a := a
  for i in [0:sub.size] do
    a := a.set! (start + i) (sub[i]!)
  return a

/-- `shift_tail` (`sort.rs:81-123`): shift the last element left to its sorted position. -/
def shiftTail (v : Array T) (isLess : T → T → Bool) : Array T := Id.run do
  let len := v.size
  if len < 2 then return v
  if !isLess (v[len-1]!) (v[len-2]!) then return v
  let mut v := v
  let tmp := v[len-1]!
  let mut hole := len - 2
  v := v.set! (len-1) (v[len-2]!)
  for i in (List.range (len-2)).reverse do
    if !isLess tmp (v[i]!) then break
    v := v.set! (i+1) (v[i]!)
    hole := i
  v := v.set! hole tmp
  return v

private theorem shiftTail_loop_sorted
    (tmp : T) (key : T → ℕ) :
    ∀ (n : ℕ) (array : Array T),
      n < array.size →
      KeySorted key array.toList →
      KeysGE key (array.toList.drop (n + 1)) (key tmp) →
      let output : Array T := Id.run do
        pure PUnit.unit
        pure PUnit.unit
        let result ← forIn (List.range n).reverse
          (⟨n, array⟩ : MProd ℕ (Array T))
          fun index (result : MProd ℕ (Array T)) =>
            if !lessBy key tmp (result.snd[index]!) then
              pure (.done ⟨result.fst, result.snd⟩)
            else do
              pure PUnit.unit
              pure PUnit.unit
              pure (.yield ⟨index,
                result.snd.set! (index + 1) (result.snd[index]!)⟩)
        pure (result.snd.set! result.fst tmp)
      KeySorted key output.toList := by
  intro n
  induction n with
  | zero =>
      intro array hindex hsorted hsuffix
      have hresult := KeySorted.set key array.toList 0 tmp hsorted
        (by simpa using hindex) (by simp [KeysLE]) (by simpa using hsuffix)
      simpa [Array.set!] using hresult
  | succ n inductionHypothesis =>
      intro array hindex hsorted hsuffix
      rw [List.range_succ, List.reverse_append]
      simp only [List.reverse_singleton, List.singleton_append, List.forIn_cons]
      split
      · have hn : n < array.size :=
          Nat.lt_trans (Nat.lt_succ_self n) hindex
        have hbound := KeySorted.keysLE_take_succ key array.toList n hsorted
          (by simpa using hn)
        rw [array_toList_getElem!] at hbound
        have hcompare : key array[n]! ≤ key tmp := by
          simpa [lessBy] using (show (!lessBy key tmp array[n]!) = true from ‹_›)
        have hresult := KeySorted.set key array.toList (n + 1) tmp hsorted
          (by simpa using hindex) (by
            intro item hitem
            exact (hbound item hitem).trans hcompare)
          (by simpa [Nat.add_assoc] using hsuffix)
        simpa [Array.set!] using hresult
      · let shifted := array.set! (n + 1) array[n]!
        have hn : n < array.size := Nat.lt_trans (Nat.lt_succ_self n) hindex
        have hshiftedSorted : KeySorted key shifted.toList := by
          simp only [shifted, Array.set!, Array.toList_setIfInBounds]
          apply KeySorted.set key array.toList (n + 1) array[n]! hsorted
              (by simpa using hindex)
          · have hbound :=
              KeySorted.keysLE_take_succ key array.toList n hsorted hn
            rw [array_toList_getElem!] at hbound
            exact hbound
          · have htail :=
              KeySorted.keysGE_drop_succ key array.toList n hsorted hn
            rw [array_toList_getElem!] at htail
            intro item hitem
            apply htail item
            have hdrop : array.toList.drop (n + 1 + 1) =
                (array.toList.drop (n + 1)).drop 1 := by
              rw [List.drop_drop]
            rw [hdrop] at hitem
            exact List.drop_subset 1 _ hitem
        have hshiftedSize : shifted.size = array.size := by
          simp [shifted]
        have hshiftedAt : shifted[n]! = array[n]! := by
          simp [shifted, hn]
        have hshiftedSuffix :
            KeysGE key (shifted.toList.drop (n + 1)) (key tmp) := by
          have htail := KeySorted.keysGE_drop_succ key shifted.toList n
            hshiftedSorted (by simpa [hshiftedSize] using hn)
          rw [array_toList_getElem!] at htail
          intro item hitem
          have hcompare : key tmp ≤ key shifted[n]! := by
            have hless : key tmp < key array[n]! := by
              simpa [lessBy] using
                (show ¬(!lessBy key tmp array[n]!) = true from ‹_›)
            simpa [hshiftedAt] using hless.le
          exact hcompare.trans (htail item hitem)
        simpa [shifted] using inductionHypothesis shifted
          (by simpa [hshiftedSize] using hn) hshiftedSorted hshiftedSuffix

/-- `shiftTail` preserves ordering when its initial prefix is already ordered. -/
theorem shiftTail_sorted
    (array : Array T) (key : T → ℕ)
    (hprefix : KeySorted key
      (array.toList.take (array.size - 1))) :
    KeySorted key (shiftTail array (lessBy key)).toList := by
  simp only [shiftTail]
  split
  · have hsize : array.size ≤ 1 := by omega
    have hsmall : KeySorted key array.toList := by
      rw [KeySorted, List.sortedLE_iff_pairwise,
        List.pairwise_map, List.pairwise_iff_get]
      intro left right horder
      have hleft := left.isLt
      have hright := right.isLt
      simp only [Array.length_toList] at hleft hright
      omega
    simpa using hsmall
  split
  · have hsize : 2 ≤ array.size := by omega
    have hbound := KeySorted.keysLE_last key
      (array.toList.take (array.size - 1)) hprefix (by simp; omega)
    have hlast :
        (array.toList.take (array.size - 1))[
          (array.toList.take (array.size - 1)).length - 1]! =
          array[array.size - 2]! := by
      rw [getElem!_pos _ _ (by simp; omega), getElem!_pos array _ (by omega)]
      simp [List.getElem_take]
      congr 1
    rw [hlast] at hbound
    have hcompare : key array[array.size - 2]! ≤
        key array[array.size - 1]! := by
      simpa [lessBy] using
        (show (!lessBy key array[array.size - 1]!
          array[array.size - 2]!) = true from ‹_›)
    have hprefixBound : KeysLE key
        (array.toList.take (array.size - 1))
        (key array[array.size - 1]!) := by
      intro item hitem
      exact (hbound item hitem).trans hcompare
    have hresult := KeySorted.append_pivot key _ array[array.size - 1]! []
      hprefix (KeySorted.nil key) hprefixBound (by simp [KeysGE])
    have hdecomposition :
        array.toList.take (array.size - 1) ++
          [array[array.size - 1]!] = array.toList := by
      have hdecomposition := take_append_last array.toList (by simp; omega)
      simp only [Array.length_toList] at hdecomposition
      rw [array_toList_getElem!] at hdecomposition
      exact hdecomposition
    rw [hdecomposition] at hresult
    simpa using hresult
  · have hsize : 2 ≤ array.size := by omega
    let shifted := array.set! (array.size - 1) array[array.size - 2]!
    have hshiftedSorted : KeySorted key shifted.toList := by
      simp only [shifted, Array.set!, Array.toList_setIfInBounds]
      rw [List.set_eq_take_cons_drop array[array.size - 2]!
        (by simp; omega)]
      have hdrop : array.toList.drop (array.size - 1 + 1) = [] := by
        simp
        omega
      rw [hdrop]
      have hbound := KeySorted.keysLE_last key
        (array.toList.take (array.size - 1)) hprefix (by simp; omega)
      have hlast :
          (array.toList.take (array.size - 1))[
            (array.toList.take (array.size - 1)).length - 1]! =
            array[array.size - 2]! := by
        rw [getElem!_pos _ _ (by simp; omega), getElem!_pos array _ (by omega)]
        simp [List.getElem_take]
        congr 1
      rw [hlast] at hbound
      exact KeySorted.append_pivot key _ array[array.size - 2]! []
        hprefix (KeySorted.nil key) hbound (by simp [KeysGE])
    have hshiftedSuffix : KeysGE key
        (shifted.toList.drop (array.size - 2 + 1))
        (key array[array.size - 1]!) := by
      have htail := KeySorted.keysGE_drop_succ key shifted.toList
        (array.size - 2) hshiftedSorted (by simp [shifted]; omega)
      rw [array_toList_getElem!] at htail
      have hshiftedAt : shifted[array.size - 2]! =
          array[array.size - 2]! := by
        have hne : array.size - 2 ≠ array.size - 1 := by omega
        unfold shifted
        rw [getElem!_pos _ _ (by simp; omega),
          getElem!_pos array _ (by omega)]
        simp only [Array.set!]
        rw [Array.getElem_setIfInBounds (by omega), if_neg hne.symm,
          ← getElem!_pos array _ (by omega)]
      rw [hshiftedAt] at htail
      have hless : key array[array.size - 1]! <
          key array[array.size - 2]! := by
        simpa [lessBy] using
          (show ¬(!lessBy key array[array.size - 1]!
            array[array.size - 2]!) = true from ‹_›)
      intro item hitem
      exact hless.le.trans (htail item hitem)
    simpa [shifted] using shiftTail_loop_sorted array[array.size - 1]! key
      (array.size - 2) shifted (by simp [shifted]; omega)
      hshiftedSorted hshiftedSuffix

/-- `shift_head` (`sort.rs:35-78`): shift the first element right to its sorted position. -/
def shiftHead (v : Array T) (isLess : T → T → Bool) : Array T := Id.run do
  let len := v.size
  if len < 2 then return v
  if !isLess (v[1]!) (v[0]!) then return v
  let mut v := v
  let tmp := v[0]!
  let mut hole := 1
  v := v.set! 0 (v[1]!)
  for i in [2:len] do
    if !isLess (v[i]!) tmp then break
    v := v.set! (i-1) (v[i]!)
    hole := i
  v := v.set! hole tmp
  return v

/-- `insertion_sort` (`sort.rs:175-182`). -/
def insertionSort (v : Array T) (isLess : T → T → Bool) : Array T := Id.run do
  let mut v := v
  for i in [1:v.size] do
    v := overwrite v 0 (shiftTail (v.extract 0 (i+1)) isLess)
  return v

/-- One `sift_down` step of `heapsort` (`sort.rs:191-210`). -/
def siftDown (v : Array T) (isLess : T → T → Bool) (node0 : ℕ) : Array T := Id.run do
  let mut v := v
  let mut node := node0
  for _ in [0:v.size+1] do
    let left := 2*node + 1
    let right := 2*node + 2
    let greater := if right < v.size && isLess (v[left]!) (v[right]!) then right else left
    if greater ≥ v.size || !isLess (v[node]!) (v[greater]!) then break
    v := swp v node greater
    node := greater
  return v

/-- `heapsort` (`sort.rs:186-222`). -/
def heapsort (v : Array T) (isLess : T → T → Bool) : Array T := Id.run do
  let mut v := v
  let n := v.size
  for i in (List.range (n/2)).reverse do
    v := siftDown v isLess i
  for i in (List.range n).reverse do
    if i ≥ 1 then
      v := swp v 0 i
      v := overwrite v 0 (siftDown (v.extract 0 i) isLess 0)
  return v

/- Proof-facing decomposition of legacy `partition_in_blocks`. The helpers
mirror the source phases while exposing local permutation and bounds invariants. -/
/-- The block-size update at the head of `partitionInBlocks`' outer loop.
The Boolean arguments are the source conditions `start_l < end_l` and
`start_r < end_r`. -/
def adjustBlockSizes
    (gap blockLeft blockRight : ℕ)
    (pendingLeft pendingRight : Bool) : ℕ × ℕ :=
  if gap ≤ 2 * 128 then
    let remaining :=
      if pendingLeft || pendingRight then gap - 128 else gap
    if pendingLeft then
      (blockLeft, remaining)
    else if pendingRight then
      (remaining, blockRight)
    else
      (remaining / 2, remaining - remaining / 2)
  else
    (blockLeft, blockRight)

/-- When the outer loop is done, a pending side retains its full 128-entry
block and the other side receives the remainder. With no pending side, the
gap is split in half. In every case the adjusted sizes exactly cover `gap`
and neither exceeds 128. -/
theorem adjustBlockSizes_done
    (gap blockLeft blockRight : ℕ)
    (pendingLeft pendingRight : Bool)
    (hdone : gap ≤ 2 * 128)
    (hpendingLeft : pendingLeft = true →
      blockLeft = 128 ∧ 128 ≤ gap)
    (hpendingRight : pendingRight = true →
      blockRight = 128 ∧ 128 ≤ gap) :
    let adjusted :=
      adjustBlockSizes gap blockLeft blockRight
        pendingLeft pendingRight
    adjusted.1 ≤ 128 ∧ adjusted.2 ≤ 128 ∧
      adjusted.1 + adjusted.2 = gap := by
  unfold adjustBlockSizes
  simp only [hdone, ↓reduceIte]
  by_cases hleft : pendingLeft = true
  · have hfull := hpendingLeft hleft
    simp [hleft]
    omega
  · have hleftFalse : pendingLeft = false := by
      cases pendingLeft <;> simp_all
    by_cases hright : pendingRight = true
    · have hfull := hpendingRight hright
      simp [hleftFalse, hright]
      omega
    · have hrightFalse : pendingRight = false := by
        cases pendingRight <;> simp_all
      simp [hleftFalse, hrightFalse]
      omega

/-- Above the done threshold the source adjustment is the identity, so the
ready-state component and sum bounds are inherited unchanged. -/
theorem adjustBlockSizes_not_done
    (gap blockLeft blockRight : ℕ)
    (pendingLeft pendingRight : Bool)
    (hnotDone : 2 * 128 < gap)
    (hleft : blockLeft ≤ 128)
    (hright : blockRight ≤ 128)
    (hsum : blockLeft + blockRight ≤ gap) :
    let adjusted :=
      adjustBlockSizes gap blockLeft blockRight
        pendingLeft pendingRight
    adjusted.1 ≤ 128 ∧ adjusted.2 ≤ 128 ∧
      adjusted.1 + adjusted.2 ≤ gap := by
  simp [adjustBlockSizes, show ¬gap ≤ 2 * 128 by omega,
    hleft, hright, hsum]

/-- A branch-independent form suited to the outer-loop invariant. The
pre-adjustment bounds are needed only in the not-done branch; the pending
full-block hypotheses are needed only in the done branch. -/
theorem adjustBlockSizes_bounds
    (gap blockLeft blockRight : ℕ)
    (pendingLeft pendingRight : Bool)
    (hbefore : 2 * 128 < gap →
      blockLeft ≤ 128 ∧ blockRight ≤ 128 ∧
        blockLeft + blockRight ≤ gap)
    (hpendingLeft : gap ≤ 2 * 128 →
      pendingLeft = true →
        blockLeft = 128 ∧ 128 ≤ gap)
    (hpendingRight : gap ≤ 2 * 128 →
      pendingRight = true →
        blockRight = 128 ∧ 128 ≤ gap) :
    let adjusted :=
      adjustBlockSizes gap blockLeft blockRight
        pendingLeft pendingRight
    adjusted.1 ≤ 128 ∧ adjusted.2 ≤ 128 ∧
      adjusted.1 + adjusted.2 ≤ gap := by
  by_cases hdone : gap ≤ 2 * 128
  · have hresult :=
      adjustBlockSizes_done gap blockLeft blockRight
        pendingLeft pendingRight hdone
        (hpendingLeft hdone) (hpendingRight hdone)
    exact ⟨hresult.1, hresult.2.1, hresult.2.2.le⟩
  · have hnotDone : 2 * 128 < gap := by omega
    have hready := hbefore hnotDone
    exact adjustBlockSizes_not_done gap blockLeft blockRight
      pendingLeft pendingRight hnotDone
      hready.1 hready.2.1 hready.2.2

/-- At most one pending side is preserved as an explicit source-facing
shape fact: if the left side is pending, the right side is not, and the
adjustment is exactly `(128, gap - 128)`; symmetrically on the right. -/
theorem adjustBlockSizes_pending_shape
    (gap blockLeft blockRight : ℕ)
    (pendingLeft pendingRight : Bool)
    (hdone : gap ≤ 2 * 128)
    (hatMostOne :
      ¬(pendingLeft = true ∧ pendingRight = true))
    (hpendingLeft : pendingLeft = true →
      blockLeft = 128)
    (hpendingRight : pendingRight = true →
      blockRight = 128) :
    (pendingLeft = true →
        adjustBlockSizes gap blockLeft blockRight
          pendingLeft pendingRight = (128, gap - 128)) ∧
      (pendingRight = true →
        adjustBlockSizes gap blockLeft blockRight
          pendingLeft pendingRight = (gap - 128, 128)) := by
  constructor
  · intro hleft
    simp [adjustBlockSizes, hdone, hleft, hpendingLeft hleft]
  · intro hright
    have hleft : pendingLeft = false := by
      cases h : pendingLeft
      · rfl
      · exfalso
        exact hatMostOne ⟨h, hright⟩
    simp [adjustBlockSizes, hdone, hleft, hright,
      hpendingRight hright]

omit [Inhabited T] in
private theorem pull_set_perm (value : T) :
    ∀ (items : List T) (index : ℕ) (hindex : index < items.length),
      List.Perm
        (items[index] :: items.set index value)
        (value :: items) := by
  intro items index
  induction items generalizing index with
  | nil => simp
  | cons head tail ih =>
      cases index with
      | zero =>
          intro _
          simp only [List.getElem_cons_zero, List.set_cons_zero]
          exact .swap _ _ _
      | succ index =>
          intro hindex
          simp only [List.getElem_cons_succ, List.set_cons_succ]
          exact (List.Perm.swap _ _ _).trans
            (((ih index (by simpa using hindex)).cons head).trans
              (List.Perm.swap _ _ _))

omit [Inhabited T] in
private theorem set_set_swap_perm
    (items : List T) (left right : ℕ)
    (hleft : left < items.length)
    (hright : right < items.length) :
    List.Perm
      ((items.set left items[right]).set right items[left])
      items := by
  induction items generalizing left right with
  | nil => simp at hleft
  | cons head tail ih =>
      cases left with
      | zero =>
          cases right with
          | zero => simp
          | succ right =>
              simpa only [List.getElem_cons_zero,
                List.getElem_cons_succ, List.set_cons_zero,
                List.set_cons_succ] using
                pull_set_perm head tail right (by simpa using hright)
      | succ left =>
          cases right with
          | zero =>
              simpa only [List.getElem_cons_zero,
                List.getElem_cons_succ, List.set_cons_zero,
                List.set_cons_succ] using
                pull_set_perm head tail left (by simpa using hleft)
          | succ right =>
              simpa only [List.getElem_cons_succ,
                List.set_cons_succ] using
                (ih left right (by simpa using hleft)
                  (by simpa using hright)).cons head

private theorem swp_perm
    (array : Array T) (left right : ℕ)
    (hleft : left < array.size)
    (hright : right < array.size) :
    List.Perm (swp array left right).toList array.toList := by
  unfold swp
  simp only [Array.set!, Array.toList_setIfInBounds]
  rw [show array[left]! = array.toList[left] by simp [hleft],
    show array[right]! = array.toList[right] by simp [hright]]
  exact set_set_swap_perm array.toList left right
    (by simpa using hleft) (by simpa using hright)

/-- The final left-offset cleanup loop. The state fields are
`(endLeft, right, array)`. -/
def cleanupLeft
    (indices : List ℕ) (startLeft left : ℕ)
    (offsetsLeft : Array ℕ)
    (state : MProd ℕ (MProd ℕ (Array T))) :
    MProd ℕ (MProd ℕ (Array T)) := Id.run <|
  forIn indices state fun _ state =>
    let ⟨endLeft, right, array⟩ := state
    if startLeft < endLeft then
      let endLeft := endLeft - 1
      let array :=
        swp array (left + offsetsLeft[endLeft]!) (right - 1)
      let right := right - 1
      pure (.yield ⟨endLeft, right, array⟩)
    else
      pure (.done state)

/-- The final right-offset cleanup loop. The state fields are
`(endRight, left, array)`. -/
def cleanupRight
    (indices : List ℕ) (startRight right : ℕ)
    (offsetsRight : Array ℕ)
    (state : MProd ℕ (MProd ℕ (Array T))) :
    MProd ℕ (MProd ℕ (Array T)) := Id.run <|
  forIn indices state fun _ state =>
    let ⟨endRight, left, array⟩ := state
    if startRight < endRight then
      let endRight := endRight - 1
      let array :=
        swp array left (right - offsetsRight[endRight]! - 1)
      let left := left + 1
      pure (.yield ⟨endRight, left, array⟩)
    else
      pure (.done state)

private theorem cleanupLeft_cons
    (index : ℕ) (indices : List ℕ)
    (startLeft left : ℕ) (offsetsLeft : Array ℕ)
    (endLeft right : ℕ) (array : Array T) :
    cleanupLeft (index :: indices) startLeft left offsetsLeft
        ⟨endLeft, right, array⟩ =
      if startLeft < endLeft then
        cleanupLeft indices startLeft left offsetsLeft
          ⟨endLeft - 1, right - 1,
            swp array (left + offsetsLeft[endLeft - 1]!)
              (right - 1)⟩
      else
        ⟨endLeft, right, array⟩ := by
  by_cases hactive : startLeft < endLeft
  · simp [cleanupLeft, hactive]
  · simp [cleanupLeft, hactive]

private theorem cleanupRight_cons
    (index : ℕ) (indices : List ℕ)
    (startRight right : ℕ) (offsetsRight : Array ℕ)
    (endRight left : ℕ) (array : Array T) :
    cleanupRight (index :: indices) startRight right offsetsRight
        ⟨endRight, left, array⟩ =
      if startRight < endRight then
        cleanupRight indices startRight right offsetsRight
          ⟨endRight - 1, left + 1,
            swp array left
              (right - offsetsRight[endRight - 1]! - 1)⟩
      else
        ⟨endRight, left, array⟩ := by
  by_cases hactive : startRight < endRight
  · simp [cleanupRight, hactive]
  · simp [cleanupRight, hactive]

/-- Cleanup of outstanding left offsets preserves the array multiset and
returns a right boundary no larger than the original array size.

The arithmetic invariant `endLeft - startLeft ≤ right` is precisely what
keeps `right - 1` in bounds through every remaining cleanup iteration. -/
theorem cleanupLeft_contract
    (indices : List ℕ)
    (startLeft left : ℕ) (offsetsLeft : Array ℕ)
    (endLeft right : ℕ) (array original : Array T)
    (hstart : startLeft ≤ endLeft)
    (hremaining : endLeft - startLeft ≤ right)
    (hright : right ≤ array.size)
    (hoffsets : ∀ index, index < endLeft →
      left + offsetsLeft[index]! < array.size)
    (hperm : List.Perm array.toList original.toList) :
    let result :=
      cleanupLeft indices startLeft left offsetsLeft
        ⟨endLeft, right, array⟩
    result.2.1 ≤ original.size ∧
      List.Perm result.2.2.toList original.toList := by
  induction indices generalizing endLeft right array with
  | nil =>
      change right ≤ original.size ∧
        List.Perm array.toList original.toList
      have hsize : array.size = original.size := by
        simpa using hperm.length_eq
      exact ⟨by omega, hperm⟩
  | cons index indices ih =>
      rw [cleanupLeft_cons]
      by_cases hactive : startLeft < endLeft
      · rw [if_pos hactive]
        have hend : startLeft ≤ endLeft - 1 := by omega
        have hrightPositive : 0 < right := by omega
        have hleftIndex :
            left + offsetsLeft[endLeft - 1]! < array.size :=
          hoffsets (endLeft - 1) (by omega)
        have hrightIndex : right - 1 < array.size := by omega
        let next :=
          swp array (left + offsetsLeft[endLeft - 1]!) (right - 1)
        have hnextPerm :
            List.Perm next.toList original.toList :=
          (swp_perm array
            (left + offsetsLeft[endLeft - 1]!) (right - 1)
            hleftIndex hrightIndex).trans hperm
        have hnextSize : next.size = array.size := by
          simp [next, swp, Array.set!]
        apply ih (endLeft - 1) (right - 1) next
        · exact hend
        · omega
        · omega
        · intro offsetIndex hoffsetIndex
          rw [hnextSize]
          exact hoffsets offsetIndex (by omega)
        · exact hnextPerm
      · rw [if_neg hactive]
        change right ≤ original.size ∧
          List.Perm array.toList original.toList
        have hsize : array.size = original.size := by
          simpa using hperm.length_eq
        exact ⟨by omega, hperm⟩

/-- Cleanup of outstanding right offsets preserves the array multiset and
returns a left boundary no larger than the original array size.

The arithmetic invariant `endRight - startRight ≤ right - left` is exactly
what keeps the moving left boundary in range. Active right offsets only
need to be smaller than `right`. -/
theorem cleanupRight_contract
    (indices : List ℕ)
    (startRight right : ℕ) (offsetsRight : Array ℕ)
    (endRight left : ℕ) (array original : Array T)
    (hstart : startRight ≤ endRight)
    (hlr : left ≤ right)
    (hremaining : endRight - startRight ≤ right - left)
    (hright : right ≤ array.size)
    (hoffsets : ∀ index, index < endRight →
      offsetsRight[index]! < right)
    (hperm : List.Perm array.toList original.toList) :
    let result :=
      cleanupRight indices startRight right offsetsRight
        ⟨endRight, left, array⟩
    result.2.1 ≤ original.size ∧
      List.Perm result.2.2.toList original.toList := by
  induction indices generalizing endRight left array with
  | nil =>
      change left ≤ original.size ∧
        List.Perm array.toList original.toList
      have hsize : array.size = original.size := by
        simpa using hperm.length_eq
      exact ⟨by omega, hperm⟩
  | cons index indices ih =>
      rw [cleanupRight_cons]
      by_cases hactive : startRight < endRight
      · rw [if_pos hactive]
        have hend : startRight ≤ endRight - 1 := by omega
        have hltr : left < right := by omega
        have hoffset :
            offsetsRight[endRight - 1]! < right :=
          hoffsets (endRight - 1) (by omega)
        have hrightIndex :
            right - offsetsRight[endRight - 1]! - 1 <
              array.size := by
          omega
        let next :=
          swp array left
            (right - offsetsRight[endRight - 1]! - 1)
        have hnextPerm :
            List.Perm next.toList original.toList :=
          (swp_perm array left
            (right - offsetsRight[endRight - 1]! - 1)
            (by omega) hrightIndex).trans hperm
        have hnextSize : next.size = array.size := by
          simp [next, swp, Array.set!]
        apply ih (endRight - 1) (left + 1) next
        · exact hend
        · omega
        · omega
        · omega
        · intro offsetIndex hoffsetIndex
          exact hoffsets offsetIndex (by omega)
        · exact hnextPerm
      · rw [if_neg hactive]
        change left ≤ original.size ∧
          List.Perm array.toList original.toList
        have hsize : array.size = original.size := by
          simpa using hperm.length_eq
        exact ⟨by omega, hperm⟩

private theorem cycle_repair_eq_swp
    (a : Array T) (tmp : T) (hole next : ℕ)
    (hhole : hole < a.size) (hnext : next < a.size) :
    (a.set! hole a[next]!).set! next tmp =
      swp (a.set! hole tmp) hole next := by
  apply Array.toList_inj.mp
  unfold swp
  simp only [Array.set!, Array.toList_setIfInBounds]
  by_cases heq : hole = next
  · subst next
    simp [Array.setIfInBounds, hhole]
  ·
    have hreadHole :
        (a.setIfInBounds hole tmp)[hole]! = tmp := by
      simp [Array.setIfInBounds, hhole]
    have hreadNext :
        (a.setIfInBounds hole tmp)[next]! = a[next]! := by
      have hh : hole < a.size := hhole
      rw [show a.setIfInBounds hole tmp = a.set hole tmp hh by
        simp [Array.setIfInBounds, hh]]
      simp [heq, hnext]
    rw [hreadHole, hreadNext]
    simp [hnext]

private theorem cycle_set_loop_perm :
    ∀ (nexts : List ℕ) (current : Array T)
      (hole : ℕ) (tmp : T) (original : Array T),
      hole < current.size →
      (∀ j ∈ nexts, j < current.size) →
      List.Perm (current.set! hole tmp).toList original.toList →
      let result : MProd (Array T) ℕ := Id.run <|
        forIn nexts (⟨current, hole⟩ : MProd (Array T) ℕ)
          fun next state =>
            pure (.yield
              ⟨state.fst.set! state.snd state.fst[next]!, next⟩)
      List.Perm
        (result.fst.set! result.snd tmp).toList
        original.toList := by
  intro nexts
  induction nexts with
  | nil =>
      intro current hole tmp original _ _ hperm
      simpa using hperm
  | cons next nexts ih =>
      intro current hole tmp original hhole hnexts hperm
      simp only [List.forIn_cons]
      apply ih
      ·
        simpa [Array.set!] using hnexts next (by simp)
      ·
        intro j hj
        simpa [Array.set!] using hnexts j (by simp [hj])
      ·
        rw [cycle_repair_eq_swp current tmp hole next hhole
          (hnexts next (by simp))]
        exact (swp_perm (current.set! hole tmp) hole next
          (by simpa [Array.set!] using hhole)
          (by
            simpa [Array.set!] using hnexts next (by simp))).trans
          hperm

private theorem cycle_set_perm
    (a : Array T) (hole : ℕ) (nexts : List ℕ)
    (hhole : hole < a.size)
    (hnexts : ∀ j ∈ nexts, j < a.size) :
    let tmp := a[hole]!
    let result : MProd (Array T) ℕ := Id.run <|
      forIn nexts (⟨a, hole⟩ : MProd (Array T) ℕ)
        fun next state =>
          pure (.yield
            ⟨state.fst.set! state.snd state.fst[next]!, next⟩)
    List.Perm
      (result.fst.set! result.snd tmp).toList
      a.toList := by
  apply cycle_set_loop_perm nexts a hole a[hole]! a hhole hnexts
  rw [show a.set! hole a[hole]! = a by
    apply Array.toList_inj.mp
    simpa [Array.set!, hhole] using
      (List.set_getElem_self (as := a.toList) (i := hole)
        (by simpa using hhole))]

private theorem alternating_set_loop_perm
    (n : ℕ) (left right : ℕ → ℕ) :
    ∀ (indices : List ℕ) (a' : Array T) (sl sr : ℕ)
      (tmp : T) (original : Array T),
      a'.size = n →
      (∀ k, k ≤ indices.length → left (sl + k) < n) →
      (∀ k, k ≤ indices.length → right (sr + k) < n) →
      List.Perm (a'.set! (right sr) tmp).toList
        original.toList →
      let result : ℕ × ℕ × Array T := Id.run <|
        forIn indices (sl, sr, a') fun _ state =>
          let sl' := state.1 + 1
          let afterLeft := state.2.2.set! (right state.2.1)
            state.2.2[left sl']!
          let sr' := state.2.1 + 1
          let afterRight := afterLeft.set! (left sl')
            afterLeft[right sr']!
          pure (.yield (sl', sr', afterRight))
      List.Perm
        (result.2.2.set! (right result.2.1) tmp).toList
        original.toList := by
  intro indices
  induction indices with
  | nil =>
      intro a' sl sr tmp original _ _ _ hperm
      simpa using hperm
  | cons index indices ih =>
      intro a' sl sr tmp original hsize hleft hright hperm
      simp only [List.forIn_cons]
      let sl' := sl + 1
      let afterLeft := a'.set! (right sr) a'[left sl']!
      let sr' := sr + 1
      let afterRight := afterLeft.set! (left sl')
        afterLeft[right sr']!
      apply ih afterRight sl' sr' tmp original
      · simp [afterRight, afterLeft, hsize]
      ·
        intro k hk
        have hb := hleft (k + 1) (by simp; omega)
        simpa [sl', Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
          using hb
      ·
        intro k hk
        have hb := hright (k + 1) (by simp; omega)
        simpa [sr', Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
          using hb
      ·
        have hrightOld : right sr < a'.size := by
          simpa [hsize] using hright 0 (by simp)
        have hleftNew : left sl' < a'.size := by
          simpa [sl', hsize] using hleft 1 (by simp)
        have hrightNew : right sr' < afterLeft.size := by
          simpa [sr', afterLeft, Array.set!, hsize] using
            hright 1 (by simp)
        have hleftAfter : left sl' < afterLeft.size := by
          simpa [sl', afterLeft, Array.set!, hsize] using
            hleft 1 (by simp)
        have hpLeft :
            List.Perm (afterLeft.set! (left sl') tmp).toList
              original.toList := by
          rw [cycle_repair_eq_swp a' tmp (right sr) (left sl')
            hrightOld hleftNew]
          exact (swp_perm (a'.set! (right sr) tmp)
            (right sr) (left sl')
            (by simpa [Array.set!] using hrightOld)
            (by simpa [Array.set!] using hleftNew)).trans hperm
        rw [cycle_repair_eq_swp afterLeft tmp (left sl')
          (right sr') hleftAfter hrightNew]
        exact (swp_perm (afterLeft.set! (left sl') tmp)
          (left sl') (right sr')
          (by simpa [Array.set!] using hleftAfter)
          (by simpa [Array.set!] using hrightNew)).trans hpLeft

private def CycleStateInvariant
    (arraySize : ℕ) (left right : ℕ → ℕ)
    (sl sr count step : ℕ) (leftGood rightGood : T → Prop)
    (state : ℕ × ℕ × Array T) : Prop :=
  state.1 = sl + step ∧ state.2.1 = sr + step ∧
    state.2.2.size = arraySize ∧
    (∀ index, index ≤ step → index < count →
      rightGood state.2.2[left (sl + index)]!) ∧
    (∀ index, index < step →
      leftGood state.2.2[right (sr + index)]!) ∧
    (∀ index, step < index → index < count →
      leftGood state.2.2[left (sl + index)]!) ∧
    (∀ index, step ≤ index → index < count →
      rightGood state.2.2[right (sr + index)]!)

private theorem cycleStateInvariant_initial
    (array : Array T) (left right : ℕ → ℕ)
    (sl sr count : ℕ) (leftGood rightGood : T → Prop)
    (hcount : 0 < count)
    (hleftBound : ∀ index, index < count →
      left (sl + index) < array.size)
    (hleftInjective : ∀ i, i < count → ∀ j, j < count →
      left (sl + i) = left (sl + j) → i = j)
    (hcross : ∀ i, i < count → ∀ j, j < count →
      left (sl + i) ≠ right (sr + j))
    (hleftGood : ∀ index, index < count →
      leftGood array[left (sl + index)]!)
    (hrightGood : ∀ index, index < count →
      rightGood array[right (sr + index)]!) :
    CycleStateInvariant array.size left right sl sr count 0
      leftGood rightGood
      (sl, sr, array.set! (left sl) array[right sr]!) := by
  unfold CycleStateInvariant
  have hleftZero := hleftBound 0 hcount
  refine ⟨rfl, rfl, by simp [Array.set!], ?_, ?_, ?_, ?_⟩
  · intro index hindexZero hindexCount
    have hindex : index = 0 := by omega
    subst index
    simp only [Nat.add_zero]
    rw [set!_get! array (left sl) (left sl) array[right sr]!
      hleftZero, if_pos rfl]
    simpa using hrightGood 0 hcount
  · intro index hindex
    omega
  · intro index hindexPositive hindexCount
    rw [set!_get! array (left sl) (left (sl + index))
      array[right sr]! hleftZero, if_neg]
    · exact hleftGood index hindexCount
    · intro heq
      have := hleftInjective 0 hcount index hindexCount
        (by simpa using heq.symm)
      omega
  · intro index hindexZero hindexCount
    rw [set!_get! array (left sl) (right (sr + index))
      array[right sr]! hleftZero, if_neg]
    · exact hrightGood index hindexCount
    · exact Ne.symm (hcross 0 hcount index hindexCount)

private theorem cycleStateInvariant_step
    (arraySize : ℕ) (left right : ℕ → ℕ)
    (sl sr count step : ℕ) (leftGood rightGood : T → Prop)
    (current : Array T)
    (hnext : step + 1 < count)
    (hleftBound : ∀ index, index < count →
      left (sl + index) < arraySize)
    (hrightBound : ∀ index, index < count →
      right (sr + index) < arraySize)
    (hleftInjective : ∀ i, i < count → ∀ j, j < count →
      left (sl + i) = left (sl + j) → i = j)
    (hrightInjective : ∀ i, i < count → ∀ j, j < count →
      right (sr + i) = right (sr + j) → i = j)
    (hcross : ∀ i, i < count → ∀ j, j < count →
      left (sl + i) ≠ right (sr + j))
    (hinvariant : CycleStateInvariant arraySize left right sl sr count step
      leftGood rightGood (sl + step, sr + step, current)) :
    let nextStep := step + 1
    let afterLeft := current.set! (right (sr + step))
      current[left (sl + nextStep)]!
    let afterRight := afterLeft.set! (left (sl + nextStep))
      afterLeft[right (sr + nextStep)]!
    CycleStateInvariant arraySize left right sl sr count nextStep
      leftGood rightGood
      (sl + nextStep, sr + nextStep, afterRight) := by
  rcases hinvariant with
    ⟨_, _, hsize, hleftDone, hrightDone, hleftFuture, hrightFuture⟩
  let nextStep := step + 1
  let targetRight := right (sr + step)
  let targetLeft := left (sl + nextStep)
  let sourceLeft := left (sl + nextStep)
  let sourceRight := right (sr + nextStep)
  let afterLeft := current.set! targetRight current[sourceLeft]!
  let afterRight := afterLeft.set! targetLeft afterLeft[sourceRight]!
  have htargetRight : targetRight < current.size := by
    rw [hsize]
    exact hrightBound step (by omega)
  have htargetLeft : targetLeft < afterLeft.size := by
    simp only [afterLeft, Array.set!, Array.size_setIfInBounds]
    rw [hsize]
    exact hleftBound nextStep hnext
  have hsourceRightNeTargetRight : sourceRight ≠ targetRight := by
    intro heq
    have := hrightInjective nextStep hnext step (by omega) (by
      simpa [sourceRight, targetRight] using heq)
    omega
  have hsourceRightValue : afterLeft[sourceRight]! = current[sourceRight]! := by
    simp only [afterLeft]
    rw [set!_get! current targetRight sourceRight
      current[sourceLeft]! htargetRight, if_neg hsourceRightNeTargetRight]
  unfold CycleStateInvariant
  refine ⟨rfl, rfl, by simp [hsize], ?_, ?_, ?_, ?_⟩
  · intro index hindexDone hindexCount
    rw [set!_get! afterLeft targetLeft
      (left (sl + index)) afterLeft[sourceRight]! htargetLeft]
    by_cases hnew : index = nextStep
    · subst index
      rw [if_pos rfl, hsourceRightValue]
      exact hrightFuture nextStep (by omega) hnext
    · rw [if_neg (by
          intro heq
          exact hnew (hleftInjective index hindexCount nextStep hnext
            (by simpa [targetLeft] using heq)))]
      simp only [afterLeft]
      rw [set!_get! current targetRight
        (left (sl + index)) current[sourceLeft]! htargetRight,
        if_neg (hcross index hindexCount step (by omega))]
      exact hleftDone index (by omega) hindexCount
  · intro index hindexDone
    have hindexCount : index < count := hindexDone.trans_le (by omega)
    rw [set!_get! afterLeft targetLeft
      (right (sr + index)) afterLeft[sourceRight]! htargetLeft,
      if_neg (Ne.symm (hcross nextStep hnext index hindexCount))]
    simp only [afterLeft]
    rw [set!_get! current targetRight
      (right (sr + index)) current[sourceLeft]! htargetRight]
    by_cases hnew : index = step
    · subst index
      rw [if_pos rfl]
      exact hleftFuture nextStep (by omega) hnext
    · rw [if_neg (by
          intro heq
          exact hnew (hrightInjective index hindexCount step (by omega)
            (by simpa [targetRight] using heq)))]
      exact hrightDone index (by omega)
  · intro index hindexFuture hindexCount
    rw [set!_get! afterLeft targetLeft
      (left (sl + index)) afterLeft[sourceRight]! htargetLeft,
      if_neg (by
        intro heq
        have := hleftInjective index hindexCount nextStep hnext
          (by simpa [targetLeft] using heq)
        omega)]
    simp only [afterLeft]
    rw [set!_get! current targetRight
      (left (sl + index)) current[sourceLeft]! htargetRight,
      if_neg (hcross index hindexCount step (by omega))]
    exact hleftFuture index (by omega) hindexCount
  · intro index hindexFuture hindexCount
    rw [set!_get! afterLeft targetLeft
      (right (sr + index)) afterLeft[sourceRight]! htargetLeft,
      if_neg (Ne.symm (hcross nextStep hnext index hindexCount))]
    simp only [afterLeft]
    rw [set!_get! current targetRight
      (right (sr + index)) current[sourceLeft]! htargetRight,
      if_neg (by
        intro heq
        have := hrightInjective index hindexCount step (by omega)
          (by simpa [targetRight] using heq)
        omega)]
    exact hrightFuture index (by omega) hindexCount

private theorem cycleStateInvariant_loop
    (arraySize : ℕ) (left right : ℕ → ℕ)
    (sl sr count : ℕ) (leftGood rightGood : T → Prop)
    (hleftBound : ∀ index, index < count →
      left (sl + index) < arraySize)
    (hrightBound : ∀ index, index < count →
      right (sr + index) < arraySize)
    (hleftInjective : ∀ i, i < count → ∀ j, j < count →
      left (sl + i) = left (sl + j) → i = j)
    (hrightInjective : ∀ i, i < count → ∀ j, j < count →
      right (sr + i) = right (sr + j) → i = j)
    (hcross : ∀ i, i < count → ∀ j, j < count →
      left (sl + i) ≠ right (sr + j)) :
    ∀ (indices : List ℕ) (step : ℕ) (current : Array T),
      step + indices.length = count - 1 →
      CycleStateInvariant arraySize left right sl sr count step
        leftGood rightGood (sl + step, sr + step, current) →
      CycleStateInvariant arraySize left right sl sr count
        (step + indices.length) leftGood rightGood
        (Id.run <| forIn indices (sl + step, sr + step, current)
          fun _ state =>
            let nextStepLeft := state.1 + 1
            let afterLeft := state.2.2.set! (right state.2.1)
              state.2.2[left nextStepLeft]!
            let nextStepRight := state.2.1 + 1
            let afterRight := afterLeft.set! (left nextStepLeft)
              afterLeft[right nextStepRight]!
            pure (.yield (nextStepLeft, nextStepRight, afterRight))) := by
  intro indices
  induction indices with
  | nil =>
      intro step current hsteps hinvariant
      simpa using hinvariant
  | cons index indices inductionHypothesis =>
      intro step current hsteps hinvariant
      have hnext : step + 1 < count := by
        simp only [List.length_cons] at hsteps
        omega
      have hstep := cycleStateInvariant_step arraySize left right
        sl sr count step leftGood rightGood current hnext
        hleftBound hrightBound hleftInjective hrightInjective hcross
        hinvariant
      let afterLeft := current.set! (right (sr + step))
        current[left (sl + (step + 1))]!
      let afterRight := afterLeft.set! (left (sl + (step + 1)))
        afterLeft[right (sr + (step + 1))]!
      change CycleStateInvariant arraySize left right sl sr count
          (step + 1) leftGood rightGood
          (sl + (step + 1), sr + (step + 1), afterRight) at hstep
      simp only [List.forIn_cons, pure_bind]
      have hrest := inductionHypothesis (step + 1) afterRight
        (by
          simp only [List.length_cons] at hsteps
          omega)
        hstep
      simpa [afterLeft, afterRight, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using hrest

private theorem block_cycle_classifies
    (array : Array T) (left right : ℕ → ℕ)
    (sl sr count : ℕ) (leftGood rightGood : T → Prop)
    (hcount : 0 < count)
    (hleftBound : ∀ index, index < count →
      left (sl + index) < array.size)
    (hrightBound : ∀ index, index < count →
      right (sr + index) < array.size)
    (hleftInjective : ∀ i, i < count → ∀ j, j < count →
      left (sl + i) = left (sl + j) → i = j)
    (hrightInjective : ∀ i, i < count → ∀ j, j < count →
      right (sr + i) = right (sr + j) → i = j)
    (hcross : ∀ i, i < count → ∀ j, j < count →
      left (sl + i) ≠ right (sr + j))
    (hleftGood : ∀ index, index < count →
      leftGood array[left (sl + index)]!)
    (hrightGood : ∀ index, index < count →
      rightGood array[right (sr + index)]!) :
    let tmp := array[left sl]!
    let afterFirst := array.set! (left sl) array[right sr]!
    let result : ℕ × ℕ × Array T := Id.run <|
      forIn (List.range' 0 (count - 1))
        (sl, sr, afterFirst) fun _ state =>
          let nextStepLeft := state.1 + 1
          let afterLeft := state.2.2.set! (right state.2.1)
            state.2.2[left nextStepLeft]!
          let nextStepRight := state.2.1 + 1
          let afterRight := afterLeft.set! (left nextStepLeft)
            afterLeft[right nextStepRight]!
          pure (.yield (nextStepLeft, nextStepRight, afterRight))
    let output := result.2.2.set! (right result.2.1) tmp
    (∀ index, index < count →
      rightGood output[left (sl + index)]!) ∧
    (∀ index, index < count →
      leftGood output[right (sr + index)]!) := by
  let tmp := array[left sl]!
  let afterFirst := array.set! (left sl) array[right sr]!
  let result : ℕ × ℕ × Array T := Id.run <|
    forIn (List.range' 0 (count - 1))
      (sl, sr, afterFirst) fun _ state =>
        let nextStepLeft := state.1 + 1
        let afterLeft := state.2.2.set! (right state.2.1)
          state.2.2[left nextStepLeft]!
        let nextStepRight := state.2.1 + 1
        let afterRight := afterLeft.set! (left nextStepLeft)
          afterLeft[right nextStepRight]!
        pure (.yield (nextStepLeft, nextStepRight, afterRight))
  have hinitial := cycleStateInvariant_initial array left right sl sr count
    leftGood rightGood hcount hleftBound hleftInjective hcross
    hleftGood hrightGood
  have hloop := cycleStateInvariant_loop array.size left right sl sr count
    leftGood rightGood hleftBound hrightBound hleftInjective
    hrightInjective hcross (List.range' 0 (count - 1)) 0 afterFirst
    (by simp) (by simpa [afterFirst] using hinitial)
  have hloopResult : CycleStateInvariant array.size left right sl sr count
      (count - 1) leftGood rightGood result := by
    simpa only [result, Nat.zero_add, List.length_range'] using hloop
  rcases hloopResult with
    ⟨hresultLeft, hresultRight, hresultSize,
      hleftDone, hrightDone, hleftFuture, hrightFuture⟩
  have hlast : count - 1 < count := by omega
  have htarget : right result.2.1 < result.2.2.size := by
    rw [hresultRight, hresultSize]
    exact hrightBound (count - 1) hlast
  let output := result.2.2.set! (right result.2.1) tmp
  refine ⟨?_, ?_⟩
  · intro index hindex
    rw [set!_get! result.2.2 (right result.2.1)
      (left (sl + index)) tmp htarget, if_neg]
    · exact hleftDone index (by omega) hindex
    · rw [hresultRight]
      exact hcross index hindex (count - 1) hlast
  · intro index hindex
    rw [set!_get! result.2.2 (right result.2.1)
      (right (sr + index)) tmp htarget]
    by_cases hlastIndex : index = count - 1
    · subst index
      rw [hresultRight, if_pos rfl]
      simpa [tmp] using hleftGood 0 hcount
    · rw [hresultRight, if_neg (by
          intro heq
          exact hlastIndex (hrightInjective index hindex
            (count - 1) hlast heq))]
      exact hrightDone index (by omega)

private theorem cycle_loop_outside
    (array : Array T) (left right : ℕ → ℕ)
    (sl sr count position : ℕ)
    (hleftBound : ∀ index, index < count →
      left (sl + index) < array.size)
    (hrightBound : ∀ index, index < count →
      right (sr + index) < array.size)
    (houtLeft : ∀ index, index < count →
      position ≠ left (sl + index))
    (houtRight : ∀ index, index < count →
      position ≠ right (sr + index)) :
    ∀ (indices : List ℕ) (step : ℕ) (current : Array T),
      step + indices.length = count - 1 →
      current.size = array.size → current[position]! = array[position]! →
      let result : ℕ × ℕ × Array T := Id.run <|
        forIn indices (sl + step, sr + step, current) fun _ state =>
          let nextStepLeft := state.1 + 1
          let afterLeft := state.2.2.set! (right state.2.1)
            state.2.2[left nextStepLeft]!
          let nextStepRight := state.2.1 + 1
          let afterRight := afterLeft.set! (left nextStepLeft)
            afterLeft[right nextStepRight]!
          pure (.yield (nextStepLeft, nextStepRight, afterRight))
      result.2.2[position]! = array[position]! := by
  intro indices
  induction indices with
  | nil =>
      intro step current hsteps hsize hvalue
      simpa using hvalue
  | cons index indices inductionHypothesis =>
      intro step current hsteps hsize hvalue
      have hnext : step + 1 < count := by
        simp only [List.length_cons] at hsteps
        omega
      let afterLeft := current.set! (right (sr + step))
        current[left (sl + (step + 1))]!
      let afterRight := afterLeft.set! (left (sl + (step + 1)))
        afterLeft[right (sr + (step + 1))]!
      have htargetRight : right (sr + step) < current.size := by
        rw [hsize]
        exact hrightBound step (by omega)
      have htargetLeft : left (sl + (step + 1)) < afterLeft.size := by
        simp only [afterLeft, Array.set!, Array.size_setIfInBounds]
        rw [hsize]
        exact hleftBound (step + 1) hnext
      have hafterLeft : afterLeft[position]! = array[position]! := by
        simp only [afterLeft]
        rw [set!_get! current (right (sr + step)) position
          current[left (sl + (step + 1))]! htargetRight,
          if_neg (houtRight step (by omega)), hvalue]
      have hafterRight : afterRight[position]! = array[position]! := by
        simp only [afterRight]
        rw [set!_get! afterLeft (left (sl + (step + 1))) position
          afterLeft[right (sr + (step + 1))]! htargetLeft,
          if_neg (houtLeft (step + 1) hnext), hafterLeft]
      simp only [List.forIn_cons, pure_bind]
      have hrest := inductionHypothesis (step + 1) afterRight
        (by
          simp only [List.length_cons] at hsteps
          omega)
        (by simp [afterRight, afterLeft, hsize]) hafterRight
      simpa [afterLeft, afterRight, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using hrest

private theorem cycle_loop_shape
    (left right : ℕ → ℕ) (sl sr : ℕ) :
    ∀ (indices : List ℕ) (step : ℕ) (current : Array T),
      let result : ℕ × ℕ × Array T := Id.run <|
        forIn indices (sl + step, sr + step, current) fun _ state =>
          let nextStepLeft := state.1 + 1
          let afterLeft := state.2.2.set! (right state.2.1)
            state.2.2[left nextStepLeft]!
          let nextStepRight := state.2.1 + 1
          let afterRight := afterLeft.set! (left nextStepLeft)
            afterLeft[right nextStepRight]!
          pure (.yield (nextStepLeft, nextStepRight, afterRight))
      result.1 = sl + step + indices.length ∧
      result.2.1 = sr + step + indices.length ∧
      result.2.2.size = current.size := by
  intro indices
  induction indices with
  | nil => simp
  | cons index indices inductionHypothesis =>
      intro step current
      let afterLeft := current.set! (right (sr + step))
        current[left (sl + (step + 1))]!
      let afterRight := afterLeft.set! (left (sl + (step + 1)))
        afterLeft[right (sr + (step + 1))]!
      simp only [List.forIn_cons, pure_bind]
      have hrest := inductionHypothesis (step + 1) afterRight
      simpa [afterLeft, afterRight, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using hrest

private theorem block_cycle_outside
    (array : Array T) (left right : ℕ → ℕ)
    (sl sr count position : ℕ) (hcount : 0 < count)
    (hleftBound : ∀ index, index < count →
      left (sl + index) < array.size)
    (hrightBound : ∀ index, index < count →
      right (sr + index) < array.size)
    (houtLeft : ∀ index, index < count →
      position ≠ left (sl + index))
    (houtRight : ∀ index, index < count →
      position ≠ right (sr + index)) :
    let tmp := array[left sl]!
    let afterFirst := array.set! (left sl) array[right sr]!
    let result : ℕ × ℕ × Array T := Id.run <|
      forIn (List.range' 0 (count - 1))
        (sl, sr, afterFirst) fun _ state =>
          let nextStepLeft := state.1 + 1
          let afterLeft := state.2.2.set! (right state.2.1)
            state.2.2[left nextStepLeft]!
          let nextStepRight := state.2.1 + 1
          let afterRight := afterLeft.set! (left nextStepLeft)
            afterLeft[right nextStepRight]!
          pure (.yield (nextStepLeft, nextStepRight, afterRight))
    let output := result.2.2.set! (right result.2.1) tmp
    output[position]! = array[position]! := by
  let tmp := array[left sl]!
  let afterFirst := array.set! (left sl) array[right sr]!
  let result : ℕ × ℕ × Array T := Id.run <|
    forIn (List.range' 0 (count - 1))
      (sl, sr, afterFirst) fun _ state =>
        let nextStepLeft := state.1 + 1
        let afterLeft := state.2.2.set! (right state.2.1)
          state.2.2[left nextStepLeft]!
        let nextStepRight := state.2.1 + 1
        let afterRight := afterLeft.set! (left nextStepLeft)
          afterLeft[right nextStepRight]!
        pure (.yield (nextStepLeft, nextStepRight, afterRight))
  have hleftZero := hleftBound 0 hcount
  have hafterFirst : afterFirst[position]! = array[position]! := by
    simp only [afterFirst]
    rw [set!_get! array (left sl) position array[right sr]!
      hleftZero, if_neg (by simpa using houtLeft 0 hcount)]
  have hloop := cycle_loop_outside array left right sl sr count position
    hleftBound hrightBound houtLeft houtRight
    (List.range' 0 (count - 1)) 0 afterFirst
    (by simp) (by simp [afterFirst]) hafterFirst
  have hresultValue : result.2.2[position]! = array[position]! := by
    simpa only [result, Nat.zero_add] using hloop
  have hshape := cycle_loop_shape (T := T) left right sl sr
    (List.range' 0 (count - 1)) 0 afterFirst
  have hresultRight : result.2.1 = sr + (count - 1) := by
    simpa only [result, Nat.zero_add, List.length_range'] using hshape.2.1
  have hresultSize : result.2.2.size = array.size := by
    simpa [result, afterFirst] using hshape.2.2
  have htarget : right result.2.1 < result.2.2.size := by
    rw [hresultRight, hresultSize]
    exact hrightBound (count - 1) (by omega)
  show (result.2.2.set! (right result.2.1) tmp)[position]! = array[position]!
  rw [set!_get! result.2.2 (right result.2.1) position tmp htarget,
    if_neg]
  · exact hresultValue
  · rw [hresultRight]
    exact houtRight (count - 1) (by omega)

private theorem block_cycle_perm
    (a : Array T) (left right : ℕ → ℕ)
    (sl sr count : ℕ)
    (hleft : ∀ k, k ≤ count - 1 →
      left (sl + k) < a.size)
    (hright : ∀ k, k ≤ count - 1 →
      right (sr + k) < a.size) :
    let tmp := a[left sl]!
    let afterFirst := a.set! (left sl) a[right sr]!
    let result : ℕ × ℕ × Array T := Id.run <|
      forIn (List.range' 0 (count - 1))
        (sl, sr, afterFirst) fun _ state =>
          let sl' := state.1 + 1
          let afterLeft := state.2.2.set! (right state.2.1)
            state.2.2[left sl']!
          let sr' := state.2.1 + 1
          let afterRight := afterLeft.set! (left sl')
            afterLeft[right sr']!
          pure (.yield (sl', sr', afterRight))
    List.Perm
      (result.2.2.set! (right result.2.1) tmp).toList
      a.toList := by
  let tmp := a[left sl]!
  let afterFirst := a.set! (left sl) a[right sr]!
  have hleftStart : left sl < a.size := by
    simpa using hleft 0 (by omega)
  have hrightStart : right sr < a.size := by
    simpa using hright 0 (by omega)
  have hpFirst :
      List.Perm (afterFirst.set! (right sr) tmp).toList
        a.toList := by
    rw [cycle_repair_eq_swp a tmp (left sl) (right sr)
      hleftStart hrightStart]
    have hself : a.set! (left sl) tmp = a := by
      apply Array.toList_inj.mp
      simpa [tmp, Array.set!, hleftStart] using
        (List.set_getElem_self (as := a.toList) (i := left sl)
          (by simpa using hleftStart))
    rw [hself]
    exact swp_perm a (left sl) (right sr)
      hleftStart hrightStart
  apply alternating_set_loop_perm a.size left right
    (List.range' 0 (count - 1)) afterFirst sl sr tmp a
    (by simp [afterFirst])
  · simpa using hleft
  · simpa using hright
  · exact hpFirst

private theorem scan_offsets_aux
    (block : ℕ) (keep : ℕ → Bool) :
    ∀ (indices : List ℕ) (endIdx : ℕ) (offsets : Array ℕ),
      endIdx + indices.length ≤ offsets.size →
      (∀ j, j < endIdx → offsets[j]! < block) →
      (∀ i ∈ indices, i < block) →
      let result : ℕ × Array ℕ := Id.run <|
        forIn indices (endIdx, offsets) fun i state =>
          let offsets' := state.2.set! state.1 i
          let endIdx' :=
            if keep i = true then state.1 + 1 else state.1
          pure (.yield (endIdx', offsets'))
      result.1 ≤ endIdx + indices.length ∧
        result.2.size = offsets.size ∧
        ∀ j, j < result.1 → result.2[j]! < block := by
  intro indices
  induction indices with
  | nil =>
      intro endIdx offsets _ hactive _
      exact ⟨by simp, rfl, hactive⟩
  | cons i indices ih =>
      intro endIdx offsets hcapacity hactive hindices
      simp only [List.forIn_cons]
      have hend : endIdx < offsets.size := by
        have : endIdx + 1 ≤ endIdx + (indices.length + 1) := by omega
        simpa only [List.length_cons] using
          this.trans hcapacity
      let offsets' := offsets.set! endIdx i
      let endIdx' :=
        if keep i = true then endIdx + 1 else endIdx
      have hsize : offsets'.size = offsets.size := by
        simp [offsets']
      have hendStep : endIdx' ≤ endIdx + 1 := by
        by_cases hkeep : keep i = true <;>
          simp [endIdx', hkeep]
      have hcapacity' :
          endIdx' + indices.length ≤ offsets'.size := by
        rw [hsize]
        simp only [List.length_cons] at hcapacity
        omega
      have hactive' :
          ∀ j, j < endIdx' → offsets'[j]! < block := by
        intro j hj
        by_cases hkeep : keep i = true
        · have hjle : j ≤ endIdx := by
            simp [endIdx', hkeep] at hj
            omega
          by_cases hjeq : j = endIdx
          · subst j
            have hi : i < block :=
              hindices i (by simp)
            simpa [offsets', Array.set!, hend] using hi
          ·
            have hjold : j < endIdx := by omega
            have hjbound := hactive j hjold
            have hjsize : j < offsets.size := hjold.trans hend
            have hne' : endIdx ≠ j := Ne.symm hjeq
            simpa [offsets', Array.set!, hjsize, hne'] using
              hjbound
        · have hjold : j < endIdx := by
            simpa [endIdx', hkeep] using hj
          have hjbound := hactive j hjold
          have hne : j ≠ endIdx := by omega
          have hjsize : j < offsets.size := hjold.trans hend
          have hne' : endIdx ≠ j := Ne.symm hne
          simpa [offsets', Array.set!, hjsize, hne'] using
            hjbound
      have hrest : ∀ k ∈ indices, k < block := by
        intro k hk
        exact hindices k (by simp [hk])
      have hout := ih endIdx' offsets' hcapacity' hactive' hrest
      have htotal :
          (Id.run <|
            forIn indices (endIdx', offsets') fun i state =>
              let offsets' := state.2.set! state.1 i
              let endIdx' :=
                if keep i = true then state.1 + 1 else state.1
              pure (.yield (endIdx', offsets'))).1 ≤
            endIdx + (i :: indices).length := by
        calc
          _ ≤ endIdx' + indices.length := hout.1
          _ ≤ endIdx + (i :: indices).length := by
            simp only [List.length_cons]
            omega
      simpa [offsets', endIdx'] using And.intro htotal hout.2

omit [Inhabited T] in
private theorem take_set!_self_succ
    {U : Type} (array : Array U) (index : ℕ) (value : U)
    (hindex : index < array.size) :
    (array.set! index value).toList.take (index + 1) =
      array.toList.take index ++ [value] := by
  simp only [Array.set!, Array.toList_setIfInBounds]
  rw [List.set_eq_take_cons_drop value (by simpa using hindex),
    List.take_append]
  have hlength : (array.toList.take index).length = index := by
    simp
    omega
  simp [hlength]

omit [Inhabited T] in
private theorem scan_offsets_prefix
    (keep : ℕ → Bool) :
    ∀ (indices : List ℕ) (endIdx : ℕ) (offsets : Array ℕ),
      endIdx + indices.length ≤ offsets.size →
      let result : ℕ × Array ℕ := Id.run <|
        forIn indices (endIdx, offsets) fun i state =>
          let offsets' := state.2.set! state.1 i
          let endIdx' :=
            if keep i = true then state.1 + 1 else state.1
          pure (.yield (endIdx', offsets'))
      let kept := indices.filter (fun index => keep index = true)
      result.1 = endIdx + kept.length ∧
        result.2.toList.take result.1 =
          offsets.toList.take endIdx ++ kept := by
  intro indices
  induction indices with
  | nil =>
      intro endIdx offsets hcapacity
      simp
  | cons index indices inductionHypothesis =>
      intro endIdx offsets hcapacity
      simp only [List.forIn_cons, pure_bind]
      let offsets' := offsets.set! endIdx index
      by_cases hkeep : keep index = true
      · have hend : endIdx < offsets.size := by
          simp only [List.length_cons] at hcapacity
          omega
        have hrestCapacity : endIdx + 1 + indices.length ≤ offsets'.size := by
          simp [offsets']
          simp only [List.length_cons] at hcapacity
          omega
        have hrest := inductionHypothesis (endIdx + 1) offsets'
          hrestCapacity
        dsimp only at hrest
        dsimp only [offsets'] at hrest
        have hkeepBool : decide (keep index = true) = true := by
          simp [hkeep]
        rw [List.filter_cons]
        simp only [hkeepBool, if_true]
        simp only [hkeep, if_true]
        constructor
        · simp only [List.length_cons]
          omega
        · rw [hrest.2, take_set!_self_succ offsets endIdx index hend]
          simp only [List.append_assoc, List.singleton_append]
      · have hrestCapacity : endIdx + indices.length ≤ offsets'.size := by
          simp [offsets']
          simp only [List.length_cons] at hcapacity
          omega
        have hrest := inductionHypothesis endIdx offsets' hrestCapacity
        dsimp only at hrest
        dsimp only [offsets'] at hrest
        have hkeepBool : decide (keep index = true) ≠ true := by
          simp [hkeep]
        rw [List.filter_cons]
        simp only [hkeepBool]
        simp only [hkeep, Bool.false_eq_true, if_false]
        constructor
        · exact hrest.1
        · rw [hrest.2]
          simp [List.take_set_of_le]

private theorem scan_offsets_bounds
    (block : ℕ) (offsets : Array ℕ) (keep : ℕ → Bool)
    (hblock : block ≤ offsets.size) :
    let result : ℕ × Array ℕ := Id.run <|
      forIn (List.range' 0 block) (0, offsets) fun i state =>
        let offsets' := state.2.set! state.1 i
        let endIdx' :=
          if keep i = true then state.1 + 1 else state.1
        pure (.yield (endIdx', offsets'))
    result.1 ≤ block ∧
      result.2.size = offsets.size ∧
      ∀ j, j < result.1 → result.2[j]! < block := by
  have hout := scan_offsets_aux block keep
    (List.range' 0 block) 0 offsets
    (by simpa using hblock)
    (by simp)
    (by
      intro i hi
      simpa using List.mem_range'.mp hi)
  simpa only [List.length_range', Nat.zero_add] using hout

private theorem scanned_block_cycle_perm
    (a : Array T) (l r blockL blockR : ℕ)
    (offsetsL offsetsR : Array ℕ)
    (startL endL startR endR count : ℕ)
    (hlr : l ≤ r) (hrsize : r ≤ a.size)
    (hblockL : blockL ≤ r - l)
    (hblockR : blockR ≤ r - l)
    (hstartL : startL ≤ endL)
    (hstartR : startR ≤ endR)
    (hcount : 0 < count)
    (hcountL : count ≤ endL - startL)
    (hcountR : count ≤ endR - startR)
    (hactiveL : ∀ j, j < endL →
      offsetsL[j]! < blockL)
    (hactiveR : ∀ j, j < endR →
      offsetsR[j]! < blockR) :
    let left := fun i => l + offsetsL[i]!
    let right := fun i => r - offsetsR[i]! - 1
    let tmp := a[left startL]!
    let afterFirst := a.set! (left startL) a[right startR]!
    let result : ℕ × ℕ × Array T := Id.run <|
      forIn (List.range' 0 (count - 1))
        (startL, startR, afterFirst) fun _ state =>
          let startL' := state.1 + 1
          let afterLeft := state.2.2.set! (right state.2.1)
            state.2.2[left startL']!
          let startR' := state.2.1 + 1
          let afterRight := afterLeft.set! (left startL')
            afterLeft[right startR']!
          pure (.yield (startL', startR', afterRight))
    List.Perm
      (result.2.2.set! (right result.2.1) tmp).toList
      a.toList := by
  let left := fun (i : ℕ) => l + offsetsL[i]!
  let right := fun (i : ℕ) => r - offsetsR[i]! - 1
  apply block_cycle_perm a left right startL startR count
  · intro k hk
    have hidx : startL + k < endL := by omega
    have hoff : offsetsL[startL + k]! < blockL :=
      hactiveL (startL + k) hidx
    simp only [left]
    omega
  · intro k hk
    have hidx : startR + k < endR := by omega
    have hoff : offsetsR[startR + k]! < blockR :=
      hactiveR (startR + k) hidx
    simp only [right]
    omega

private def refreshOffsets
    (block startIdx endIdx : ℕ) (offsets : Array ℕ)
    (keep : ℕ → Bool) : ℕ × ℕ × Array ℕ :=
  if startIdx = endIdx then
    let result : ℕ × Array ℕ := Id.run <|
      forIn (List.range' 0 block) (0, offsets) fun i state =>
        let offsets' := state.2.set! state.1 i
        let endIdx' :=
          if keep i = true then state.1 + 1 else state.1
        pure (.yield (endIdx', offsets'))
    (0, result.1, result.2)
  else
    (startIdx, endIdx, offsets)

private theorem refreshOffsets_fresh_prefix
    (block startIdx endIdx : ℕ) (offsets : Array ℕ)
    (keep : ℕ → Bool) (hblock : block ≤ offsets.size)
    (hfresh : startIdx = endIdx) :
    let result := refreshOffsets block startIdx endIdx offsets keep
    let kept := (List.range block).filter
      (fun index => keep index = true)
    result.1 = 0 ∧ result.2.1 = kept.length ∧
      result.2.2.toList.take result.2.1 = kept := by
  simp only [refreshOffsets, hfresh, ↓reduceIte]
  have hscan := scan_offsets_prefix keep
    (List.range' 0 block) 0 offsets (by simpa using hblock)
  dsimp only at hscan
  have hrange : List.range' 0 block = List.range block := by
    simp [List.range'_eq_map_range]
  rw [hrange] at hscan
  refine ⟨trivial, ?_⟩
  rw [hrange]
  simpa only [Nat.zero_add, List.take_zero, List.nil_append] using hscan

private def OffsetScanExact
    (block startIdx endIdx : ℕ) (offsets : Array ℕ)
    (keep : ℕ → Bool) : Prop :=
  offsets.toList.extract startIdx endIdx =
    (List.range block).filter (fun index => keep index = true)

private theorem refreshOffsets_exact
    (block startIdx endIdx : ℕ) (offsets : Array ℕ)
    (keep : ℕ → Bool) (hblock : block ≤ offsets.size)
    (hpending : startIdx ≠ endIdx →
      OffsetScanExact block startIdx endIdx offsets keep) :
    let result := refreshOffsets block startIdx endIdx offsets keep
    OffsetScanExact block result.1 result.2.1 result.2.2 keep := by
  by_cases hfresh : startIdx = endIdx
  · have hfacts := refreshOffsets_fresh_prefix block startIdx endIdx
      offsets keep hblock hfresh
    let result := refreshOffsets block startIdx endIdx offsets keep
    change result.1 = 0 ∧
      result.2.1 = ((List.range block).filter
        (fun index => keep index = true)).length ∧
      result.2.2.toList.take result.2.1 =
        (List.range block).filter (fun index => keep index = true)
      at hfacts
    change OffsetScanExact block result.1 result.2.1 result.2.2 keep
    rw [hfacts.1, hfacts.2.1]
    simp only [OffsetScanExact, List.extract_eq_take_drop,
      List.drop_zero, Nat.sub_zero]
    simpa only [hfacts.2.1] using hfacts.2.2
  · simpa [refreshOffsets, hfresh] using hpending hfresh

private theorem offset_active_mem
    (offsets : Array ℕ) (startIdx endIdx index : ℕ)
    (hstart : startIdx ≤ index) (hend : index < endIdx)
    (hbound : endIdx ≤ offsets.size) :
    offsets[index]! ∈ offsets.toList.extract startIdx endIdx := by
  rw [List.extract_eq_take_drop]
  let position := index - startIdx
  have hposition : position <
      ((offsets.toList.drop startIdx).take
        (endIdx - startIdx)).length := by
    simp [position]
    omega
  have hmem := List.getElem_mem
    (l := (offsets.toList.drop startIdx).take (endIdx - startIdx))
    (n := position) hposition
  have hindex : index < offsets.size := hend.trans_le hbound
  have hvalue :
      ((offsets.toList.drop startIdx).take
        (endIdx - startIdx))[position] = offsets[index]! := by
    rw [getElem!_pos offsets index hindex]
    simp only [List.getElem_take, List.getElem_drop,
      Array.getElem_toList]
    congr
    simp [position]
    omega
  rw [hvalue] at hmem
  exact hmem

private theorem OffsetScanExact.mem_iff
    (block startIdx endIdx : ℕ) (offsets : Array ℕ)
    (keep : ℕ → Bool)
    (hexact : OffsetScanExact block startIdx endIdx offsets keep)
    (offset : ℕ) :
    offset ∈ offsets.toList.extract startIdx endIdx ↔
      offset < block ∧ keep offset = true := by
  rw [hexact, List.mem_filter, List.mem_range]
  simp

private theorem OffsetScanExact.active
    (block startIdx endIdx : ℕ) (offsets : Array ℕ)
    (keep : ℕ → Bool)
    (hexact : OffsetScanExact block startIdx endIdx offsets keep)
    (hbound : endIdx ≤ offsets.size)
    (index : ℕ) (hstart : startIdx ≤ index) (hend : index < endIdx) :
    offsets[index]! < block ∧ keep offsets[index]! = true := by
  rw [← hexact.mem_iff]
  exact offset_active_mem offsets startIdx endIdx index
    hstart hend hbound

private theorem offset_active_get!
    (offsets : Array ℕ) (startIdx endIdx position : ℕ)
    (hposition : position < endIdx - startIdx)
    (hbound : endIdx ≤ offsets.size) :
    (offsets.toList.extract startIdx endIdx)[position]'(by
      simp [List.extract_eq_take_drop]
      omega) =
      offsets[startIdx + position]! := by
  have hindex : startIdx + position < offsets.size := by omega
  rw [getElem!_pos offsets (startIdx + position) hindex]
  simp only [List.extract_eq_take_drop, List.getElem_take,
    List.getElem_drop, Array.getElem_toList]

private theorem OffsetScanExact.injective
    (block startIdx endIdx : ℕ) (offsets : Array ℕ)
    (keep : ℕ → Bool)
    (hexact : OffsetScanExact block startIdx endIdx offsets keep)
    (hbound : endIdx ≤ offsets.size) :
    ∀ i, i < endIdx - startIdx → ∀ j, j < endIdx - startIdx →
      offsets[startIdx + i]! = offsets[startIdx + j]! → i = j := by
  intro i hi j hj hequal
  have hnodup : (offsets.toList.extract startIdx endIdx).Nodup := by
    rw [hexact]
    exact (List.nodup_range (n := block)).filter _
  rw [← offset_active_get! offsets startIdx endIdx i hi hbound,
    ← offset_active_get! offsets startIdx endIdx j hj hbound] at hequal
  exact hnodup.getElem_inj_iff.mp hequal

private theorem OffsetScanExact.nodup
    (block startIdx endIdx : ℕ) (offsets : Array ℕ)
    (keep : ℕ → Bool)
    (hexact : OffsetScanExact block startIdx endIdx offsets keep) :
    (offsets.toList.extract startIdx endIdx).Nodup := by
  rw [hexact]
  exact (List.nodup_range (n := block)).filter _

omit [Inhabited T] in
private theorem List.extract_advance
    (items : List T) (start stop count : ℕ)
    (hstart : start ≤ stop) :
    items.extract (start + count) stop =
      (items.extract start stop).drop count := by
  have hstop : stop = start + (stop - start) := by omega
  rw [hstop]
  simp only [List.extract_eq_take_drop, List.drop_take,
    List.drop_drop]
  congr 1
  omega

omit [Inhabited T] in
private theorem List.extract_shrink
    (items : List T) (start stop : ℕ) (hstart : start < stop)
    (hstop : stop ≤ items.length) :
    items.extract start (stop - 1) =
      (items.extract start stop).dropLast := by
  have hlength : (items.extract start stop).length = stop - start := by
    simp [List.extract_eq_take_drop]
    omega
  rw [List.dropLast_eq_take, hlength]
  simp only [List.extract_eq_take_drop]
  rw [List.take_take, Nat.min_eq_left (by omega)]
  apply congrArg (fun count => (items.drop start).take count)
  omega

private theorem OffsetScanExact.mem_take_iff
    (block startIdx endIdx count : ℕ) (offsets : Array ℕ)
    (keep : ℕ → Bool)
    (hexact : OffsetScanExact block startIdx endIdx offsets keep)
    (hend : endIdx ≤ offsets.size)
    (hcount : count ≤ endIdx - startIdx) (offset : ℕ) :
    offset ∈ ((List.range block).filter
        (fun index => keep index = true)).take count ↔
      ∃ index, index < count ∧
        offset = offsets[startIdx + index]! := by
  let active := (List.range block).filter
    (fun index => keep index = true)
  have hactiveEq :
      active = offsets.toList.extract startIdx endIdx := by
    exact hexact.symm
  have hactiveLength : active.length = endIdx - startIdx := by
    rw [hactiveEq]
    simp [List.extract_eq_take_drop]
    omega
  constructor
  · intro hmem
    obtain ⟨index, hindex, hvalue⟩ := List.mem_iff_getElem.mp hmem
    have hindexCount : index < count := by
      rw [List.length_take, hactiveLength,
        Nat.min_eq_left hcount] at hindex
      exact hindex
    have hindexRemaining : index < endIdx - startIdx :=
      hindexCount.trans_le hcount
    have hactiveValue :
        active[index]'(by omega) = offsets[startIdx + index]! := by
      have hvalue := offset_active_get! offsets startIdx endIdx index
        hindexRemaining hend
      simpa only [hactiveEq] using hvalue
    refine ⟨index, hindexCount, ?_⟩
    rw [← hvalue]
    simpa only [List.getElem_take] using hactiveValue
  · rintro ⟨index, hindexCount, rfl⟩
    have hindexRemaining : index < endIdx - startIdx :=
      hindexCount.trans_le hcount
    have hactiveValue :
        active[index]'(by omega) = offsets[startIdx + index]! := by
      have hvalue := offset_active_get! offsets startIdx endIdx index
        hindexRemaining hend
      simpa only [hactiveEq] using hvalue
    have hindexTake : index < (active.take count).length := by
      simp [hactiveLength, Nat.min_eq_left hcount]
      exact hindexCount
    have hmem := List.getElem_mem (l := active.take count)
      (n := index) hindexTake
    simpa only [List.getElem_take, hactiveValue] using hmem

private theorem OffsetScanExact.getLast
    (block startIdx endIdx : ℕ) (offsets : Array ℕ)
    (keep : ℕ → Bool)
    (hexact : OffsetScanExact block startIdx endIdx offsets keep)
    (hstart : startIdx < endIdx) (hend : endIdx ≤ offsets.size) :
    let active := (List.range block).filter
      (fun index => keep index = true)
    active.getLast (by
      intro heq
      have := congrArg List.length heq
      simp only [List.length_nil] at this
      have hlength : active.length = endIdx - startIdx := by
        have hactiveEq : active = offsets.toList.extract startIdx endIdx :=
          hexact.symm
        rw [hactiveEq]
        simp [List.extract_eq_take_drop]
        omega
      omega) = offsets[endIdx - 1]! := by
  let active := (List.range block).filter
    (fun index => keep index = true)
  have hactiveEq : active = offsets.toList.extract startIdx endIdx :=
    hexact.symm
  have hlength : active.length = endIdx - startIdx := by
    rw [hactiveEq]
    simp [List.extract_eq_take_drop]
    omega
  have hremaining : endIdx - startIdx - 1 < endIdx - startIdx := by omega
  have hvalue := offset_active_get! offsets startIdx endIdx
    (endIdx - startIdx - 1) hremaining hend
  show active.getLast _ = offsets[endIdx - 1]!
  rw [List.getLast_eq_getElem]
  have hindex : startIdx + (endIdx - startIdx - 1) = endIdx - 1 := by
    omega
  have hextractLength :
      (offsets.toList.extract startIdx endIdx).length =
        endIdx - startIdx := by
    rw [← hactiveEq]
    exact hlength
  simpa only [hactiveEq, hextractLength, hindex] using hvalue

private theorem OffsetScanExact.gt_last_false
    (block startIdx endIdx : ℕ) (offsets : Array ℕ)
    (keep : ℕ → Bool)
    (hexact : OffsetScanExact block startIdx endIdx offsets keep)
    (hstart : startIdx < endIdx) (hend : endIdx ≤ offsets.size)
    (offset : ℕ) (hoffset : offset < block)
    (hgt : offsets[endIdx - 1]! < offset) : keep offset = false := by
  let active := (List.range block).filter
    (fun index => keep index = true)
  have hsorted : active.SortedLT :=
    ((List.sortedLT_range block).pairwise.filter _).sortedLT
  have hnonempty : active ≠ [] := by
    intro heq
    have hlength : active.length = endIdx - startIdx := by
      have hactiveEq : active =
          offsets.toList.extract startIdx endIdx := hexact.symm
      rw [hactiveEq]
      simp [List.extract_eq_take_drop]
      omega
    rw [heq] at hlength
    simp at hlength
    omega
  have hlast : active.getLast hnonempty = offsets[endIdx - 1]! := by
    simpa only [active] using OffsetScanExact.getLast
      block startIdx endIdx offsets keep hexact hstart hend
  by_cases hkeep : keep offset = true
  · have hmem : offset ∈ active := by
      simp [active, hoffset, hkeep]
    have hne : offset ≠ active.getLast hnonempty := by
      rw [hlast]
      omega
    have hdrop : offset ∈ active.dropLast :=
      List.mem_dropLast_of_mem_of_ne_getLast hmem hne
    have hlt := hsorted.pairwise.rel_dropLast_getLast hdrop
    rw [hlast] at hlt
    omega
  · exact Bool.eq_false_of_not_eq_true hkeep

omit [Inhabited T] in
private theorem List.mem_drop_iff_of_nodup
    (items : List T) (count : ℕ) (item : T)
    (hnodup : items.Nodup) :
    item ∈ items.drop count ↔
      item ∈ items ∧ item ∉ items.take count := by
  constructor
  · intro hdrop
    refine ⟨List.mem_of_mem_drop hdrop, ?_⟩
    intro htake
    exact (List.disjoint_take_drop hnodup (m := count)
      (n := count) le_rfl) htake hdrop
  · rintro ⟨hmem, hnotTake⟩
    rw [← List.take_append_drop count items] at hmem
    rcases List.mem_append.mp hmem with htake | hdrop
    · exact (hnotTake htake).elim
    · exact hdrop

private theorem OffsetScanExact.consume
    (block startIdx endIdx count : ℕ) (offsets : Array ℕ)
    (before after : ℕ → Bool)
    (hexact : OffsetScanExact block startIdx endIdx offsets before)
    (hstart : startIdx ≤ endIdx) (hend : endIdx ≤ offsets.size)
    (hcount : count ≤ endIdx - startIdx)
    (hconsumed : ∀ index, index < count →
      after offsets[startIdx + index]! = false)
    (houtside : ∀ offset, offset < block →
      (∀ index, index < count →
        offset ≠ offsets[startIdx + index]!) →
      after offset = before offset) :
    OffsetScanExact block (startIdx + count) endIdx offsets after := by
  let oldActive := (List.range block).filter
    (fun index => before index = true)
  let newActive := (List.range block).filter
    (fun index => after index = true)
  have holdNodup : oldActive.Nodup := by
    exact (List.nodup_range (n := block)).filter _
  have holdSorted : oldActive.SortedLT :=
    ((List.sortedLT_range block).pairwise.filter _).sortedLT
  have hnewSorted : newActive.SortedLT :=
    ((List.sortedLT_range block).pairwise.filter _).sortedLT
  have htailSorted : (oldActive.drop count).SortedLT :=
    holdSorted.pairwise.drop.sortedLT
  have htailEq : oldActive.drop count = newActive := by
    apply htailSorted.eq_of_mem_iff hnewSorted
    intro offset
    rw [List.mem_drop_iff_of_nodup oldActive count offset holdNodup]
    change
      (offset ∈ (List.range block).filter
          (fun index => before index = true) ∧
        offset ∉ ((List.range block).filter
          (fun index => before index = true)).take count) ↔
      offset ∈ (List.range block).filter
        (fun index => after index = true)
    simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
    constructor
    · rintro ⟨⟨hoffset, hbefore⟩, hnotConsumed⟩
      have hnotAddress : ∀ index, index < count →
          offset ≠ offsets[startIdx + index]! := by
        intro index hindex heq
        apply hnotConsumed
        rw [OffsetScanExact.mem_take_iff block startIdx endIdx count
          offsets before hexact hend hcount offset]
        exact ⟨index, hindex, heq⟩
      exact ⟨hoffset, by rw [houtside offset hoffset hnotAddress, hbefore]⟩
    · rintro ⟨hoffset, hafter⟩
      have hnotAddress : ∀ index, index < count →
          offset ≠ offsets[startIdx + index]! := by
        intro index hindex heq
        have := hconsumed index hindex
        rw [← heq, hafter] at this
        contradiction
      have hnotConsumed :
          offset ∉ ((List.range block).filter
            (fun index => before index = true)).take count := by
        rw [OffsetScanExact.mem_take_iff block startIdx endIdx count
          offsets before hexact hend hcount offset]
        rintro ⟨index, hindex, heq⟩
        exact hnotAddress index hindex heq
      refine ⟨⟨hoffset, ?_⟩, hnotConsumed⟩
      rw [← houtside offset hoffset hnotAddress]
      exact hafter
  rw [OffsetScanExact, List.extract_advance offsets.toList
    startIdx endIdx count hstart, hexact]
  exact htailEq

private theorem OffsetScanExact.shrinkLast
    (block startIdx endIdx : ℕ) (offsets : Array ℕ)
    (before after : ℕ → Bool)
    (hexact : OffsetScanExact block startIdx endIdx offsets before)
    (hstart : startIdx < endIdx) (hend : endIdx ≤ offsets.size)
    (hlast : offsets[endIdx - 1]! < block - 1 →
      after offsets[endIdx - 1]! = false)
    (houtside : ∀ offset, offset < block - 1 →
      offset ≠ offsets[endIdx - 1]! →
      after offset = before offset) :
    OffsetScanExact (block - 1) startIdx (endIdx - 1) offsets after := by
  let oldActive := (List.range block).filter
    (fun offset => before offset = true)
  let newActive := (List.range (block - 1)).filter
    (fun offset => after offset = true)
  have holdSorted : oldActive.SortedLT :=
    ((List.sortedLT_range block).pairwise.filter _).sortedLT
  have hnewSorted : newActive.SortedLT :=
    ((List.sortedLT_range (block - 1)).pairwise.filter _).sortedLT
  have holdNonempty : oldActive ≠ [] := by
    intro heq
    have hlength : oldActive.length = endIdx - startIdx := by
      have hactiveEq : oldActive =
          offsets.toList.extract startIdx endIdx := hexact.symm
      rw [hactiveEq]
      simp [List.extract_eq_take_drop]
      omega
    rw [heq] at hlength
    simp at hlength
    omega
  have hgetLast : oldActive.getLast holdNonempty = offsets[endIdx - 1]! := by
    simpa only [oldActive] using OffsetScanExact.getLast
      block startIdx endIdx offsets before hexact hstart hend
  have hlastActive := OffsetScanExact.active block startIdx endIdx offsets
    before hexact hend (endIdx - 1) (by omega) (by omega)
  have htailSorted : oldActive.dropLast.SortedLT := by
    rw [List.dropLast_eq_take]
    exact holdSorted.pairwise.take.sortedLT
  have htailEq : oldActive.dropLast = newActive := by
    apply htailSorted.eq_of_mem_iff hnewSorted
    intro offset
    change
      (offset ∈ ((List.range block).filter
        (fun offset => before offset = true)).dropLast) ↔
      offset ∈ (List.range (block - 1)).filter
        (fun offset => after offset = true)
    simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
    constructor
    · intro hmem
      have hbeforeMem := List.mem_of_mem_dropLast hmem
      have hbefore : before offset = true := by
        simpa [oldActive] using (List.mem_filter.mp hbeforeMem).2
      have hoffsetLast : offset < offsets[endIdx - 1]! := by
        have hrel := holdSorted.pairwise.rel_dropLast_getLast hmem
        simpa only [hgetLast] using hrel
      have hoffset : offset < block - 1 := by omega
      have hne : offset ≠ offsets[endIdx - 1]! := by omega
      exact ⟨hoffset, by rw [houtside offset hoffset hne, hbefore]⟩
    · rintro ⟨hoffset, hafter⟩
      have hne : offset ≠ offsets[endIdx - 1]! := by
        intro heq
        have hlastFalse := hlast (by omega)
        rw [← heq, hafter] at hlastFalse
        contradiction
      have hbefore : before offset = true := by
        rw [← houtside offset hoffset hne]
        exact hafter
      have hmem : offset ∈ oldActive := by
        simp [oldActive, show offset < block by omega, hbefore]
      apply List.mem_dropLast_of_mem_of_ne_getLast hmem
      simpa only [hgetLast] using hne
  rw [OffsetScanExact, List.extract_shrink offsets.toList
    startIdx endIdx hstart hend, hexact]
  exact htailEq

private theorem OffsetScanExact.exhausted
    (block index : ℕ) (offsets : Array ℕ) (keep : ℕ → Bool)
    (hexact : OffsetScanExact block index index offsets keep) :
    ∀ offset, offset < block → keep offset = false := by
  have hnone : (List.range block).filter
      (fun offset => keep offset = true) = [] := by
    rw [← hexact]
    simp [List.extract_eq_take_drop]
  intro offset hoffset
  by_cases hkeep : keep offset = true
  · have hmem : offset ∈ (List.range block).filter
        (fun offset => keep offset = true) := by
      simp [hoffset, hkeep]
    rw [hnone] at hmem
    simp at hmem
  · exact Bool.eq_false_of_not_eq_true hkeep

private theorem exhausted_left_block_rangeAll
    (array : Array T) (pivot : T) (isLess : T → T → Bool)
    (l block index : ℕ) (offsets : Array ℕ)
    (hexact : OffsetScanExact block index index offsets
      (fun offset => !isLess array[l + offset]! pivot)) :
    RangeAll array l (l + block)
      (fun item => isLess item pivot = true) := by
  intro position hposition hstop
  let offset := position - l
  have hoffset : offset < block := by omega
  have haddress : l + offset = position := by omega
  have hgood := OffsetScanExact.exhausted block index offsets
    (fun offset => !isLess array[l + offset]! pivot) hexact
    offset hoffset
  have hgood' : (!isLess array[l + offset]! pivot) = false := by
    simpa only using hgood
  rw [haddress] at hgood'
  simpa using hgood'

private theorem exhausted_right_block_rangeAll
    (array : Array T) (pivot : T) (isLess : T → T → Bool)
    (r block index : ℕ) (offsets : Array ℕ)
    (hblock : block ≤ r)
    (hexact : OffsetScanExact block index index offsets
      (fun offset => isLess array[r - 1 - offset]! pivot)) :
    RangeAll array (r - block) r
      (fun item => isLess item pivot = false) := by
  intro position hposition hstop
  let offset := r - 1 - position
  have hoffset : offset < block := by omega
  have haddress : r - 1 - offset = position := by omega
  have hgood := OffsetScanExact.exhausted block index offsets
    (fun offset => isLess array[r - 1 - offset]! pivot) hexact
    offset hoffset
  simpa only [haddress] using hgood

private def blockCycleOutput
    (array : Array T) (l r : ℕ)
    (offsetsL offsetsR : Array ℕ)
    (startL startR count : ℕ) : Array T :=
  let left := fun (index : ℕ) => l + offsetsL[index]!
  let right := fun (index : ℕ) => r - offsetsR[index]! - 1
  let tmp := array[left startL]!
  let afterFirst := array.set! (left startL) array[right startR]!
  let result : ℕ × ℕ × Array T := Id.run <|
    forIn (List.range' 0 (count - 1))
      (startL, startR, afterFirst) fun _ state =>
        let nextStepLeft := state.1 + 1
        let afterLeft := state.2.2.set! (right state.2.1)
          state.2.2[left nextStepLeft]!
        let nextStepRight := state.2.1 + 1
        let afterRight := afterLeft.set! (left nextStepLeft)
          afterLeft[right nextStepRight]!
        pure (.yield (nextStepLeft, nextStepRight, afterRight))
  result.2.2.set! (right result.2.1) tmp

private theorem blockCycleOutput_size
    (array : Array T) (l r : ℕ)
    (offsetsL offsetsR : Array ℕ)
    (startL startR count : ℕ) :
    (blockCycleOutput array l r offsetsL offsetsR
      startL startR count).size = array.size := by
  let left := fun (index : ℕ) => l + offsetsL[index]!
  let right := fun (index : ℕ) => r - offsetsR[index]! - 1
  let afterFirst := array.set! (left startL) array[right startR]!
  let result : ℕ × ℕ × Array T := Id.run <|
    forIn (List.range' 0 (count - 1))
      (startL, startR, afterFirst) fun _ state =>
        let nextStepLeft := state.1 + 1
        let afterLeft := state.2.2.set! (right state.2.1)
          state.2.2[left nextStepLeft]!
        let nextStepRight := state.2.1 + 1
        let afterRight := afterLeft.set! (left nextStepLeft)
          afterLeft[right nextStepRight]!
        pure (.yield (nextStepLeft, nextStepRight, afterRight))
  have hshape := cycle_loop_shape (T := T) left right startL startR
    (List.range' 0 (count - 1)) 0 afterFirst
  have hresultSize : result.2.2.size = array.size := by
    simpa [result, afterFirst] using hshape.2.2
  simpa [blockCycleOutput, left, right, result, Array.set!]
    using hresultSize

private theorem scanned_block_cycle_classifies
    (array : Array T) (pivot : T) (isLess : T → T → Bool)
    (l r blockL blockR : ℕ)
    (offsetsL offsetsR : Array ℕ)
    (startL endL startR endR count : ℕ)
    (hlr : l ≤ r) (hrsize : r ≤ array.size)
    (hblocks : blockL + blockR ≤ r - l)
    (hstartL : startL ≤ endL) (hstartR : startR ≤ endR)
    (hendL : endL ≤ offsetsL.size) (hendR : endR ≤ offsetsR.size)
    (hcount : 0 < count)
    (hcountL : count ≤ endL - startL)
    (hcountR : count ≤ endR - startR)
    (hexactL : OffsetScanExact blockL startL endL offsetsL
      (fun index => !isLess array[l + index]! pivot))
    (hexactR : OffsetScanExact blockR startR endR offsetsR
      (fun index => isLess array[r - 1 - index]! pivot)) :
    (∀ index, index < count →
      isLess (blockCycleOutput array l r offsetsL offsetsR
        startL startR count)[l + offsetsL[startL + index]!]! pivot = true) ∧
    (∀ index, index < count →
      isLess (blockCycleOutput array l r offsetsL offsetsR
        startL startR count)[r - offsetsR[startR + index]! - 1]!
          pivot = false) := by
  simp only [blockCycleOutput]
  let left := fun (index : ℕ) => l + offsetsL[index]!
  let right := fun (index : ℕ) => r - offsetsR[index]! - 1
  apply block_cycle_classifies array left right startL startR count
    (fun item => isLess item pivot = false)
    (fun item => isLess item pivot = true) hcount
  · intro index hindex
    have hactive := OffsetScanExact.active blockL startL endL offsetsL
      _ hexactL hendL (startL + index)
      (by omega) (by omega)
    simp only [left]
    omega
  · intro index hindex
    have hactive := OffsetScanExact.active blockR startR endR offsetsR
      _ hexactR hendR (startR + index)
      (by omega) (by omega)
    simp only [right]
    omega
  · intro i hi j hj heq
    have hoffset : offsetsL[startL + i]! = offsetsL[startL + j]! := by
      simpa only [left, Nat.add_left_cancel_iff] using heq
    exact OffsetScanExact.injective blockL startL endL offsetsL _
      hexactL hendL i (by omega) j (by omega) hoffset
  · intro i hi j hj heq
    have hiActive := OffsetScanExact.active blockR startR endR offsetsR
      _ hexactR hendR (startR + i)
      (by omega) (by omega)
    have hjActive := OffsetScanExact.active blockR startR endR offsetsR
      _ hexactR hendR (startR + j)
      (by omega) (by omega)
    have hoffset : offsetsR[startR + i]! = offsetsR[startR + j]! := by
      simp only [right] at heq
      omega
    exact OffsetScanExact.injective blockR startR endR offsetsR _
      hexactR hendR i (by omega) j (by omega) hoffset
  · intro i hi j hj heq
    have hleftActive := OffsetScanExact.active blockL startL endL offsetsL
      _ hexactL hendL (startL + i)
      (by omega) (by omega)
    have hrightActive := OffsetScanExact.active blockR startR endR offsetsR
      _ hexactR hendR (startR + j)
      (by omega) (by omega)
    simp only [left, right] at heq
    omega
  · intro index hindex
    have hactive := OffsetScanExact.active blockL startL endL offsetsL
      _ hexactL hendL (startL + index)
      (by omega) (by omega)
    simpa only [left, Bool.not_eq_true'] using hactive.2
  · intro index hindex
    have hactive := OffsetScanExact.active blockR startR endR offsetsR
      _ hexactR hendR (startR + index)
      (by omega) (by omega)
    have haddress :
        r - 1 - offsetsR[startR + index]! =
          r - offsetsR[startR + index]! - 1 := by
      omega
    simpa only [right, haddress] using hactive.2

private theorem scanned_block_cycle_outside
    (array : Array T) (pivot : T) (isLess : T → T → Bool)
    (l r blockL blockR : ℕ)
    (offsetsL offsetsR : Array ℕ)
    (startL endL startR endR count position : ℕ)
    (hlr : l ≤ r) (hrsize : r ≤ array.size)
    (hblocks : blockL + blockR ≤ r - l)
    (hstartL : startL ≤ endL) (hstartR : startR ≤ endR)
    (hendL : endL ≤ offsetsL.size) (hendR : endR ≤ offsetsR.size)
    (hcount : 0 < count)
    (hcountL : count ≤ endL - startL)
    (hcountR : count ≤ endR - startR)
    (hexactL : OffsetScanExact blockL startL endL offsetsL
      (fun index => !isLess array[l + index]! pivot))
    (hexactR : OffsetScanExact blockR startR endR offsetsR
      (fun index => isLess array[r - 1 - index]! pivot))
    (houtL : ∀ index, index < count →
      position ≠ l + offsetsL[startL + index]!)
    (houtR : ∀ index, index < count →
      position ≠ r - offsetsR[startR + index]! - 1) :
    (blockCycleOutput array l r offsetsL offsetsR
      startL startR count)[position]! = array[position]! := by
  simp only [blockCycleOutput]
  let left := fun (index : ℕ) => l + offsetsL[index]!
  let right := fun (index : ℕ) => r - offsetsR[index]! - 1
  apply block_cycle_outside array left right startL startR count position
    hcount
  · intro index hindex
    have hactive := OffsetScanExact.active blockL startL endL offsetsL
      _ hexactL hendL (startL + index) (by omega) (by omega)
    simp only [left]
    omega
  · intro index hindex
    have hactive := OffsetScanExact.active blockR startR endR offsetsR
      _ hexactR hendR (startR + index) (by omega) (by omega)
    simp only [right]
    omega
  · simpa only [left] using houtL
  · simpa only [right] using houtR

omit [Inhabited T] in
private theorem left_block_address_lt_right_block_address
    (l r blockL blockR leftOffset rightOffset : ℕ)
    (hblocks : blockL + blockR ≤ r - l)
    (hleft : leftOffset < blockL) (hright : rightOffset < blockR) :
    l + leftOffset < r - rightOffset - 1 := by
  omega

omit [Inhabited T] in
private theorem right_block_address_eq
    (r blockR offset : ℕ) (hblockR : blockR ≤ r)
    (hoffset : offset < blockR) :
    r - 1 - offset = r - offset - 1 := by
  omega

omit [Inhabited T] in
private theorem right_block_le
    (l r blockL blockR : ℕ)
    (hblocks : blockL + blockR ≤ r - l) : blockR ≤ r := by
  omega

omit [Inhabited T] in
private theorem right_block_address_injective
    (r leftOffset rightOffset : ℕ)
    (hleft : leftOffset < r) (hright : rightOffset < r)
    (heq : r - leftOffset - 1 = r - rightOffset - 1) :
    leftOffset = rightOffset := by
  omega

omit [Inhabited T] in
private theorem left_block_address_mem_interval
    (l r blockL blockR offset : ℕ)
    (hblocks : blockL + blockR ≤ r - l)
    (hoffset : offset < blockL) :
    l ≤ l + offset ∧ l + offset < r := by
  omega

omit [Inhabited T] in
private theorem right_block_address_mem_interval
    (l r blockL blockR offset : ℕ)
    (hblocks : blockL + blockR ≤ r - l)
    (hoffset : offset < blockR) :
    l ≤ r - offset - 1 ∧ r - offset - 1 < r := by
  omega

private theorem refreshOffsets_bounds
    (block startIdx endIdx : ℕ) (offsets : Array ℕ)
    (keep : ℕ → Bool)
    (hblock : block ≤ offsets.size)
    (hstart : startIdx ≤ endIdx)
    (hend : startIdx ≠ endIdx → endIdx ≤ block)
    (hactive : startIdx ≠ endIdx →
      ∀ j, j < endIdx → offsets[j]! < block) :
    let result := refreshOffsets block startIdx endIdx offsets keep
    result.1 ≤ result.2.1 ∧
      result.2.1 ≤ block ∧
      result.2.2.size = offsets.size ∧
      ∀ j, j < result.2.1 → result.2.2[j]! < block := by
  by_cases heq : startIdx = endIdx
  · simp only [refreshOffsets, if_pos heq]
    have hout := scan_offsets_bounds block offsets keep hblock
    exact ⟨Nat.zero_le _, hout.1, hout.2.1, hout.2.2⟩
  · simp only [refreshOffsets, if_neg heq]
    exact ⟨hstart, hend heq, trivial, hactive heq⟩

private def blockMutateArray
    (a : Array T) (pivot : T) (isLess : T → T → Bool)
    (l r blockL blockR : ℕ)
    (offsetsL offsetsR : Array ℕ)
    (startL endL startR endR : ℕ) : Array T :=
  let leftData := refreshOffsets blockL startL endL offsetsL
    (fun i => !isLess a[l + i]! pivot)
  let rightData := refreshOffsets blockR startR endR offsetsR
    (fun i => isLess a[r - 1 - i]! pivot)
  let count := min (leftData.2.1 - leftData.1)
    (rightData.2.1 - rightData.1)
  if 0 < count then
    blockCycleOutput a l r leftData.2.2 rightData.2.2
      leftData.1 rightData.1 count
  else
    a

private theorem blockMutateArray_size
    (a : Array T) (pivot : T) (isLess : T → T → Bool)
    (l r blockL blockR : ℕ)
    (offsetsL offsetsR : Array ℕ)
    (startL endL startR endR : ℕ) :
    (blockMutateArray a pivot isLess l r blockL blockR
      offsetsL offsetsR startL endL startR endR).size = a.size := by
  rw [blockMutateArray]
  split
  · exact blockCycleOutput_size a l r _ _ _ _ _
  · rfl

private theorem blockMutateArray_eq_blockCycleOutput_of_pos
    (a : Array T) (pivot : T) (isLess : T → T → Bool)
    (l r blockL blockR : ℕ)
    (offsetsL offsetsR : Array ℕ)
    (startL endL startR endR : ℕ) :
    let leftData := refreshOffsets blockL startL endL offsetsL
      (fun index => !isLess a[l + index]! pivot)
    let rightData := refreshOffsets blockR startR endR offsetsR
      (fun index => isLess a[r - 1 - index]! pivot)
    let count := min (leftData.2.1 - leftData.1)
      (rightData.2.1 - rightData.1)
    0 < count →
      blockMutateArray a pivot isLess l r blockL blockR
          offsetsL offsetsR startL endL startR endR =
        blockCycleOutput a l r leftData.2.2 rightData.2.2
          leftData.1 rightData.1 count := by
  simp only
  intro hcount
  rw [blockMutateArray, if_pos hcount]

private theorem blockMutateArray_eq_self_of_no_count
    (a : Array T) (pivot : T) (isLess : T → T → Bool)
    (l r blockL blockR : ℕ)
    (offsetsL offsetsR : Array ℕ)
    (startL endL startR endR : ℕ) :
    let leftData := refreshOffsets blockL startL endL offsetsL
      (fun index => !isLess a[l + index]! pivot)
    let rightData := refreshOffsets blockR startR endR offsetsR
      (fun index => isLess a[r - 1 - index]! pivot)
    let count := min (leftData.2.1 - leftData.1)
      (rightData.2.1 - rightData.1)
    ¬0 < count →
      blockMutateArray a pivot isLess l r blockL blockR
        offsetsL offsetsR startL endL startR endR = a := by
  simp only
  intro hcount
  rw [blockMutateArray, if_neg hcount]

private theorem blockMutateArray_perm
    (a : Array T) (pivot : T) (isLess : T → T → Bool)
    (l r blockL blockR : ℕ)
    (offsetsL offsetsR : Array ℕ)
    (startL endL startR endR : ℕ)
    (hlr : l ≤ r) (hrsize : r ≤ a.size)
    (hblockLgap : blockL ≤ r - l)
    (hblockRgap : blockR ≤ r - l)
    (hsizeL : offsetsL.size = 128)
    (hsizeR : offsetsR.size = 128)
    (hblockL : blockL ≤ 128)
    (hblockR : blockR ≤ 128)
    (hstartL : startL ≤ endL)
    (hendL : startL ≠ endL → endL ≤ blockL)
    (hstartR : startR ≤ endR)
    (hendR : startR ≠ endR → endR ≤ blockR)
    (hactiveL : startL ≠ endL →
      ∀ j, j < endL → offsetsL[j]! < blockL)
    (hactiveR : startR ≠ endR →
      ∀ j, j < endR → offsetsR[j]! < blockR) :
    List.Perm
      (blockMutateArray a pivot isLess l r blockL blockR
        offsetsL offsetsR startL endL startR endR).toList
      a.toList := by
  let leftData := refreshOffsets blockL startL endL offsetsL
    (fun i => !isLess a[l + i]! pivot)
  let rightData := refreshOffsets blockR startR endR offsetsR
    (fun i => isLess a[r - 1 - i]! pivot)
  have hleft := refreshOffsets_bounds blockL startL endL offsetsL
    (fun i => !isLess a[l + i]! pivot)
    (by omega) hstartL hendL hactiveL
  have hright := refreshOffsets_bounds blockR startR endR offsetsR
    (fun i => isLess a[r - 1 - i]! pivot)
    (by omega) hstartR hendR hactiveR
  let count := min (leftData.2.1 - leftData.1)
    (rightData.2.1 - rightData.1)
  dsimp only [blockMutateArray]
  split
  next hcount =>
    apply scanned_block_cycle_perm a l r blockL blockR
      leftData.2.2 rightData.2.2 leftData.1 leftData.2.1
      rightData.1 rightData.2.1 count
      hlr hrsize hblockLgap hblockRgap hleft.1 hright.1
      hcount
    · exact min_le_left _ _
    · exact min_le_right _ _
    · exact hleft.2.2.2
    · exact hright.2.2.2
  next _ => exact .refl _

private theorem blockMutateArray_offsets_exact
    (a : Array T) (pivot : T) (isLess : T → T → Bool)
    (l r blockL blockR : ℕ)
    (offsetsL offsetsR : Array ℕ)
    (startL endL startR endR : ℕ)
    (hlr : l ≤ r) (hrsize : r ≤ a.size)
    (hblocks : blockL + blockR ≤ r - l)
    (hblockL : blockL ≤ offsetsL.size)
    (hblockR : blockR ≤ offsetsR.size)
    (hstartL : startL ≤ endL)
    (hendL : startL ≠ endL → endL ≤ blockL)
    (hstartR : startR ≤ endR)
    (hendR : startR ≠ endR → endR ≤ blockR)
    (hactiveL : startL ≠ endL →
      ∀ j, j < endL → offsetsL[j]! < blockL)
    (hactiveR : startR ≠ endR →
      ∀ j, j < endR → offsetsR[j]! < blockR)
    (hexactL : startL ≠ endL →
      OffsetScanExact blockL startL endL offsetsL
        (fun index => !isLess a[l + index]! pivot))
    (hexactR : startR ≠ endR →
      OffsetScanExact blockR startR endR offsetsR
        (fun index => isLess a[r - 1 - index]! pivot)) :
    let leftData := refreshOffsets blockL startL endL offsetsL
      (fun index => !isLess a[l + index]! pivot)
    let rightData := refreshOffsets blockR startR endR offsetsR
      (fun index => isLess a[r - 1 - index]! pivot)
    let count := min (leftData.2.1 - leftData.1)
      (rightData.2.1 - rightData.1)
    let output := blockMutateArray a pivot isLess l r blockL blockR
      offsetsL offsetsR startL endL startR endR
    OffsetScanExact blockL (leftData.1 + count) leftData.2.1
        leftData.2.2 (fun index => !isLess output[l + index]! pivot) ∧
      OffsetScanExact blockR (rightData.1 + count) rightData.2.1
        rightData.2.2
          (fun index => isLess output[r - 1 - index]! pivot) ∧
      ∀ position, position < l ∨ r ≤ position →
        output[position]! = a[position]! := by
  let leftData := refreshOffsets blockL startL endL offsetsL
    (fun index => !isLess a[l + index]! pivot)
  let rightData := refreshOffsets blockR startR endR offsetsR
    (fun index => isLess a[r - 1 - index]! pivot)
  have hleftExact : OffsetScanExact blockL leftData.1 leftData.2.1
      leftData.2.2 (fun index => !isLess a[l + index]! pivot) := by
    simpa only [leftData] using refreshOffsets_exact blockL startL endL
      offsetsL (fun index => !isLess a[l + index]! pivot)
      hblockL hexactL
  have hrightExact : OffsetScanExact blockR rightData.1 rightData.2.1
      rightData.2.2 (fun index => isLess a[r - 1 - index]! pivot) := by
    simpa only [rightData] using refreshOffsets_exact blockR startR endR
      offsetsR (fun index => isLess a[r - 1 - index]! pivot)
      hblockR hexactR
  have hleft : leftData.1 ≤ leftData.2.1 ∧
      leftData.2.1 ≤ blockL ∧
      leftData.2.2.size = offsetsL.size ∧
      ∀ j, j < leftData.2.1 → leftData.2.2[j]! < blockL := by
    simpa only [leftData] using refreshOffsets_bounds blockL startL endL
      offsetsL (fun index => !isLess a[l + index]! pivot)
      hblockL hstartL hendL hactiveL
  have hright : rightData.1 ≤ rightData.2.1 ∧
      rightData.2.1 ≤ blockR ∧
      rightData.2.2.size = offsetsR.size ∧
      ∀ j, j < rightData.2.1 → rightData.2.2[j]! < blockR := by
    simpa only [rightData] using refreshOffsets_bounds blockR startR endR
      offsetsR (fun index => isLess a[r - 1 - index]! pivot)
      hblockR hstartR hendR hactiveR
  have hleftEndSize : leftData.2.1 ≤ leftData.2.2.size := by
    exact hleft.2.1.trans (hblockL.trans_eq hleft.2.2.1.symm)
  have hrightEndSize : rightData.2.1 ≤ rightData.2.2.size := by
    exact hright.2.1.trans (hblockR.trans_eq hright.2.2.1.symm)
  let count := min (leftData.2.1 - leftData.1)
    (rightData.2.1 - rightData.1)
  have hcountL : count ≤ leftData.2.1 - leftData.1 :=
    min_le_left _ _
  have hcountR : count ≤ rightData.2.1 - rightData.1 :=
    min_le_right _ _
  let output := blockMutateArray a pivot isLess l r blockL blockR
    offsetsL offsetsR startL endL startR endR
  by_cases hcount : 0 < count
  · have houtput : output = blockCycleOutput a l r leftData.2.2
        rightData.2.2 leftData.1 rightData.1 count := by
      have hresult := blockMutateArray_eq_blockCycleOutput_of_pos
        a pivot isLess l r blockL blockR offsetsL offsetsR
        startL endL startR endR
      simpa only [output, leftData, rightData, count] using hresult hcount
    have houtputRaw :
        blockMutateArray a pivot isLess l r blockL blockR
            offsetsL offsetsR startL endL startR endR =
          blockCycleOutput a l r leftData.2.2 rightData.2.2
            leftData.1 rightData.1 count := by
      simpa only [output] using houtput
    have hclassified := scanned_block_cycle_classifies a pivot isLess
      l r blockL blockR leftData.2.2 rightData.2.2
      leftData.1 leftData.2.1 rightData.1 rightData.2.1 count
      hlr hrsize hblocks hleft.1 hright.1 hleftEndSize hrightEndSize
      hcount hcountL hcountR hleftExact hrightExact
    have hclassifiedOutput :
        (∀ index, index < count →
          isLess output[l + leftData.2.2[leftData.1 + index]!]!
            pivot = true) ∧
        (∀ index, index < count →
          isLess output[r - rightData.2.2[rightData.1 + index]! - 1]!
            pivot = false) := by
      simpa only [houtput] using hclassified
    refine ⟨?_, ?_, ?_⟩
    · apply OffsetScanExact.consume blockL leftData.1 leftData.2.1
        count leftData.2.2
        (fun index => !isLess a[l + index]! pivot)
        (fun index => !isLess output[l + index]! pivot)
        hleftExact hleft.1 hleftEndSize hcountL
      · intro index hindex
        simpa using hclassifiedOutput.1 index hindex
      · intro offset hoffset hnotConsumed
        have hout := scanned_block_cycle_outside a pivot isLess
          l r blockL blockR leftData.2.2 rightData.2.2
          leftData.1 leftData.2.1 rightData.1 rightData.2.1
          count (l + offset) hlr hrsize hblocks hleft.1 hright.1
          hleftEndSize hrightEndSize hcount hcountL hcountR
          hleftExact hrightExact
          (by
            intro index hindex heq
            exact hnotConsumed index hindex
              (Nat.add_left_cancel heq))
          (by
            intro index hindex heq
            have hactive := OffsetScanExact.active blockR rightData.1
              rightData.2.1 rightData.2.2 _ hrightExact
              hrightEndSize (rightData.1 + index) (by omega) (by omega)
            exact (left_block_address_lt_right_block_address
              l r blockL blockR offset
              rightData.2.2[rightData.1 + index]!
              hblocks hoffset hactive.1).ne heq)
        simpa only [houtput] using congrArg
          (fun value => !isLess value pivot) hout
    · apply OffsetScanExact.consume blockR rightData.1 rightData.2.1
        count rightData.2.2
        (fun index => isLess a[r - 1 - index]! pivot)
        (fun index => isLess output[r - 1 - index]! pivot)
        hrightExact hright.1 hrightEndSize hcountR
      · intro index hindex
        have haddress :
            r - 1 - rightData.2.2[rightData.1 + index]! =
              r - rightData.2.2[rightData.1 + index]! - 1 := by
          have hactive := OffsetScanExact.active blockR rightData.1
            rightData.2.1 rightData.2.2 _ hrightExact hrightEndSize
            (rightData.1 + index) (by omega) (by omega)
          exact right_block_address_eq r blockR
            rightData.2.2[rightData.1 + index]!
            (right_block_le l r blockL blockR hblocks) hactive.1
        rw [haddress]
        exact hclassifiedOutput.2 index hindex
      · intro offset hoffset hnotConsumed
        have hposition : r - 1 - offset = r - offset - 1 :=
          right_block_address_eq r blockR offset
            (right_block_le l r blockL blockR hblocks) hoffset
        have hout := scanned_block_cycle_outside a pivot isLess
          l r blockL blockR leftData.2.2 rightData.2.2
          leftData.1 leftData.2.1 rightData.1 rightData.2.1
          count (r - 1 - offset) hlr hrsize hblocks hleft.1 hright.1
          hleftEndSize hrightEndSize hcount hcountL hcountR
          hleftExact hrightExact
          (by
            intro index hindex
            have hactive := OffsetScanExact.active blockL leftData.1
              leftData.2.1 leftData.2.2 _ hleftExact hleftEndSize
              (leftData.1 + index) (by omega) (by omega)
            rw [hposition]
            exact (left_block_address_lt_right_block_address
              l r blockL blockR leftData.2.2[leftData.1 + index]!
              offset hblocks hactive.1 hoffset).ne')
          (by
            intro index hindex
            rw [hposition]
            intro heq
            apply hnotConsumed index hindex
            have hactive := OffsetScanExact.active blockR rightData.1
              rightData.2.1 rightData.2.2 _ hrightExact
              hrightEndSize (rightData.1 + index) (by omega) (by omega)
            have hblockRr := right_block_le l r blockL blockR hblocks
            exact right_block_address_injective r offset
              rightData.2.2[rightData.1 + index]!
              (hoffset.trans_le hblockRr) (hactive.1.trans_le hblockRr) heq)
        simpa only [houtput] using congrArg
          (fun value => isLess value pivot) hout
    · intro position hposition
      rw [houtputRaw]
      apply scanned_block_cycle_outside a pivot isLess
        l r blockL blockR leftData.2.2 rightData.2.2
        leftData.1 leftData.2.1 rightData.1 rightData.2.1
        count position hlr hrsize hblocks hleft.1 hright.1
        hleftEndSize hrightEndSize hcount hcountL hcountR
        hleftExact hrightExact
      · intro index hindex
        have hactive := OffsetScanExact.active blockL leftData.1
          leftData.2.1 leftData.2.2 _ hleftExact hleftEndSize
          (leftData.1 + index) (by omega) (by omega)
        have hmem := left_block_address_mem_interval l r blockL blockR
          leftData.2.2[leftData.1 + index]! hblocks hactive.1
        rcases hposition with hbefore | hafter <;> omega
      · intro index hindex
        have hactive := OffsetScanExact.active blockR rightData.1
          rightData.2.1 rightData.2.2 _ hrightExact hrightEndSize
          (rightData.1 + index) (by omega) (by omega)
        have hmem := right_block_address_mem_interval l r blockL blockR
          rightData.2.2[rightData.1 + index]! hblocks hactive.1
        rcases hposition with hbefore | hafter <;> omega
  · have hzero : count = 0 := by omega
    have houtput : output = a := by
      have hresult := blockMutateArray_eq_self_of_no_count
        a pivot isLess l r blockL blockR offsetsL offsetsR
        startL endL startR endR
      simpa only [output, leftData, rightData, count] using hresult hcount
    have houtputRaw :
        blockMutateArray a pivot isLess l r blockL blockR
          offsetsL offsetsR startL endL startR endR = a := by
      simpa only [output] using houtput
    have hleftResult : OffsetScanExact blockL
        (leftData.1 + count) leftData.2.1 leftData.2.2
        (fun index => !isLess output[l + index]! pivot) := by
      simpa only [hzero, Nat.add_zero, houtput] using hleftExact
    have hrightResult : OffsetScanExact blockR
        (rightData.1 + count) rightData.2.1 rightData.2.2
        (fun index => isLess output[r - 1 - index]! pivot) := by
      simpa only [hzero, Nat.add_zero, houtput] using hrightExact
    exact ⟨hleftResult, hrightResult, fun position _ =>
      congrArg (fun array => array[position]!) houtputRaw⟩

private theorem cleanupLeftStep_order
    (array : Array T) (pivot : T) (isLess : T → T → Bool)
    (start endIdx left right : ℕ) (offsets : Array ℕ)
    (hstart : start < endIdx) (hlr : left ≤ right)
    (hright : right ≤ array.size) (hend : endIdx ≤ offsets.size)
    (hprefix : RangeAll array 0 left
      (fun item => isLess item pivot = true))
    (hsuffix : RangeAll array right array.size
      (fun item => isLess item pivot = false))
    (hexact : OffsetScanExact (right - left) start endIdx offsets
      (fun offset => !isLess array[left + offset]! pivot)) :
    let next := swp array (left + offsets[endIdx - 1]!) (right - 1)
    RangeAll next 0 left (fun item => isLess item pivot = true) ∧
      RangeAll next (right - 1) next.size
        (fun item => isLess item pivot = false) ∧
      OffsetScanExact (right - 1 - left) start (endIdx - 1) offsets
        (fun offset => !isLess next[left + offset]! pivot) := by
  let block := right - left
  let last := offsets[endIdx - 1]!
  let hole := left + last
  let edge := right - 1
  let next := swp array hole edge
  have hlast := OffsetScanExact.active block start endIdx offsets
    (fun offset => !isLess array[left + offset]! pivot)
    (by simpa only [block] using hexact) hend (endIdx - 1)
    (by omega) (by omega)
  have hrightPositive : 0 < right := by
    simp only [block] at hlast
    omega
  have hhole : hole < array.size := by
    simp only [hole, block] at *
    omega
  have hedge : edge < array.size := by
    simp only [edge]
    omega
  have hnextSize : next.size = array.size := by
    simp [next, swp_size]
  have hnextPrefix : RangeAll next 0 left
      (fun item => isLess item pivot = true) := by
    apply RangeAll.swp array hole edge 0 left _ hhole hedge hprefix
    · intro _ hstop
      simp only [hole] at hstop
      omega
    · intro _ hstop
      simp only [edge] at hstop
      omega
  have hholeBad : isLess array[hole]! pivot = false := by
    have hbad := hlast.2
    simpa only [hole, last, Bool.not_eq_true'] using hbad
  have hnextEdge : isLess next[edge]! pivot = false := by
    show isLess (swp array hole edge)[edge]! pivot = false
    by_cases heq : edge = hole
    · rw [swp_get! array hole edge edge hhole hedge, if_pos heq]
      simpa only [heq] using hholeBad
    · rw [swp_get! array hole edge edge hhole hedge,
        if_neg heq, if_pos rfl]
      exact hholeBad
  have hnextSuffixBase : RangeAll next right next.size
      (fun item => isLess item pivot = false) := by
    rw [hnextSize]
    apply RangeAll.swp array hole edge right array.size _ hhole hedge hsuffix
    · intro hposition _
      simp only [hole, block] at hposition hlast
      omega
    · intro hposition _
      simp only [edge] at hposition
      omega
  have hnextSuffixPoint : RangeAll next edge right
      (fun item => isLess item pivot = false) := by
    intro position hposition hstop
    have hpositionEq : position = edge := by
      simp only [edge] at *
      omega
    simpa only [hpositionEq] using hnextEdge
  have hnextSuffix : RangeAll next edge next.size
      (fun item => isLess item pivot = false) := by
    apply RangeAll.append hnextSuffixPoint hnextSuffixBase
  have hnextExact : OffsetScanExact (block - 1) start
      (endIdx - 1) offsets
      (fun offset => !isLess next[left + offset]! pivot) := by
    apply OffsetScanExact.shrinkLast block start endIdx offsets
      (fun offset => !isLess array[left + offset]! pivot)
      (fun offset => !isLess next[left + offset]! pivot)
      (by simpa only [block] using hexact) hstart hend
    · intro hlastBeforeEdge
      have hedgeGood := OffsetScanExact.gt_last_false block start endIdx
        offsets (fun offset => !isLess array[left + offset]! pivot)
        (by simpa only [block] using hexact) hstart hend
        (block - 1) (by omega) (by simpa only [last] using hlastBeforeEdge)
      have haddress : left + (block - 1) = edge := by
        simp only [block, edge]
        omega
      have hedgeGood' :
          (!isLess array[left + (block - 1)]! pivot) = false := by
        simpa only using hedgeGood
      rw [swp_get! array hole edge (left + last) hhole hedge,
        if_pos rfl]
      rw [haddress] at hedgeGood'
      exact hedgeGood'
    · intro offset hoffset hne
      have hpositionNeHole : left + offset ≠ hole := by
        simp only [hole, last]
        intro heq
        exact hne (Nat.add_left_cancel heq)
      have hpositionNeEdge : left + offset ≠ edge := by
        simp only [block, edge] at hoffset ⊢
        omega
      rw [swp_get! array hole edge (left + offset) hhole hedge,
        if_neg hpositionNeHole, if_neg hpositionNeEdge]
  have hblockEq : block - 1 = right - 1 - left := by
    simp only [block] at *
    omega
  simpa only [next, hole, last, edge, hblockEq] using
    And.intro hnextPrefix (And.intro hnextSuffix hnextExact)

private theorem cleanupLeft_order
    (indices : List ℕ) (pivot : T) (isLess : T → T → Bool)
    (start left : ℕ) (offsets : Array ℕ) :
    ∀ (endIdx right : ℕ) (array : Array T),
      start ≤ endIdx → endIdx - start < indices.length →
      left ≤ right → right ≤ array.size → endIdx ≤ offsets.size →
      RangeAll array 0 left (fun item => isLess item pivot = true) →
      RangeAll array right array.size
        (fun item => isLess item pivot = false) →
      OffsetScanExact (right - left) start endIdx offsets
        (fun offset => !isLess array[left + offset]! pivot) →
      let result := cleanupLeft indices start left offsets
        ⟨endIdx, right, array⟩
      RangeAll result.2.2 0 result.2.1
          (fun item => isLess item pivot = true) ∧
        RangeAll result.2.2 result.2.1 result.2.2.size
          (fun item => isLess item pivot = false) := by
  induction indices with
  | nil =>
      intro endIdx right array hstart hfuel
      simp at hfuel
  | cons index indices inductionHypothesis =>
      intro endIdx right array hstart hfuel hlr hright hend
        hprefix hsuffix hexact
      rw [cleanupLeft_cons]
      by_cases hactive : start < endIdx
      · rw [if_pos hactive]
        have hstep := cleanupLeftStep_order array pivot isLess
          start endIdx left right offsets hactive hlr hright hend
          hprefix hsuffix hexact
        have hlast := OffsetScanExact.active (right - left) start endIdx
          offsets (fun offset => !isLess array[left + offset]! pivot)
          hexact hend (endIdx - 1) (by omega) (by omega)
        have hleftLtRight : left < right := by omega
        let next := swp array (left + offsets[endIdx - 1]!) (right - 1)
        have hnextSize : next.size = array.size := by simp [next, swp_size]
        apply inductionHypothesis (endIdx - 1) (right - 1) next
        · omega
        · simp only [List.length_cons] at hfuel
          omega
        · omega
        · rw [hnextSize]
          omega
        · omega
        · simpa only [next] using hstep.1
        · simpa only [next] using hstep.2.1
        · simpa only [next] using hstep.2.2
      · rw [if_neg hactive]
        have hdone : start = endIdx := by omega
        have hmiddle : RangeAll array left right
            (fun item => isLess item pivot = true) := by
          have hexhausted := exhausted_left_block_rangeAll array pivot
            isLess left (right - left) endIdx offsets (by
              simpa only [hdone] using hexact)
          simpa only [Nat.add_sub_of_le hlr] using hexhausted
        exact ⟨RangeAll.append hprefix hmiddle, hsuffix⟩

private theorem cleanupRightStep_order
    (array : Array T) (pivot : T) (isLess : T → T → Bool)
    (start endIdx left right : ℕ) (offsets : Array ℕ)
    (hstart : start < endIdx) (hlr : left ≤ right)
    (hright : right ≤ array.size) (hend : endIdx ≤ offsets.size)
    (hprefix : RangeAll array 0 left
      (fun item => isLess item pivot = true))
    (hsuffix : RangeAll array right array.size
      (fun item => isLess item pivot = false))
    (hexact : OffsetScanExact (right - left) start endIdx offsets
      (fun offset => isLess array[right - 1 - offset]! pivot)) :
    let next := swp array left (right - offsets[endIdx - 1]! - 1)
    RangeAll next 0 (left + 1) (fun item => isLess item pivot = true) ∧
      RangeAll next right next.size
        (fun item => isLess item pivot = false) ∧
      OffsetScanExact (right - (left + 1)) start (endIdx - 1) offsets
        (fun offset => isLess next[right - 1 - offset]! pivot) := by
  let block := right - left
  let last := offsets[endIdx - 1]!
  let hole := right - last - 1
  let edge := left
  let next := swp array edge hole
  have hlast := OffsetScanExact.active block start endIdx offsets
    (fun offset => isLess array[right - 1 - offset]! pivot)
    (by simpa only [block] using hexact) hend (endIdx - 1)
    (by omega) (by omega)
  have hleftLtRight : left < right := by
    simp only [block] at hlast
    omega
  have hedge : edge < array.size := by simp only [edge]; omega
  have hhole : hole < array.size := by simp only [hole, block] at *; omega
  have hnextSize : next.size = array.size := by simp [next, swp_size]
  have hholeGood : isLess array[hole]! pivot = true := by
    have haddress : right - 1 - last = hole := by
      simp only [hole]
      omega
    rw [← haddress]
    simpa only [last] using hlast.2
  have hnextEdge : isLess next[edge]! pivot = true := by
    show isLess (swp array edge hole)[edge]! pivot = true
    rw [swp_get! array edge hole edge hedge hhole, if_pos rfl]
    exact hholeGood
  have hnextPrefixBase : RangeAll next 0 left
      (fun item => isLess item pivot = true) := by
    apply RangeAll.swp array edge hole 0 left _ hedge hhole hprefix
    · intro _ hstop
      simp only [edge] at hstop
      omega
    · intro _ hstop
      simp only [hole, block] at hstop hlast
      omega
  have hnextPrefixPoint : RangeAll next left (left + 1)
      (fun item => isLess item pivot = true) := by
    intro position hposition hstop
    have hpositionEq : position = edge := by simp only [edge]; omega
    simpa only [hpositionEq] using hnextEdge
  have hnextPrefix : RangeAll next 0 (left + 1)
      (fun item => isLess item pivot = true) :=
    RangeAll.append hnextPrefixBase hnextPrefixPoint
  have hnextSuffix : RangeAll next right next.size
      (fun item => isLess item pivot = false) := by
    rw [hnextSize]
    apply RangeAll.swp array edge hole right array.size _ hedge hhole hsuffix
    · intro hposition _
      simp only [edge] at hposition
      omega
    · intro hposition _
      simp only [hole, block] at hposition hlast
      omega
  have hnextExact : OffsetScanExact (block - 1) start
      (endIdx - 1) offsets
      (fun offset => isLess next[right - 1 - offset]! pivot) := by
    apply OffsetScanExact.shrinkLast block start endIdx offsets
      (fun offset => isLess array[right - 1 - offset]! pivot)
      (fun offset => isLess next[right - 1 - offset]! pivot)
      (by simpa only [block] using hexact) hstart hend
    · intro hlastBeforeEdge
      have hedgeGood := OffsetScanExact.gt_last_false block start endIdx
        offsets (fun offset => isLess array[right - 1 - offset]! pivot)
        (by simpa only [block] using hexact) hstart hend
        (block - 1) (by omega) (by simpa only [last] using hlastBeforeEdge)
      have haddress : right - 1 - (block - 1) = edge := by
        simp only [block, edge]
        omega
      have hedgeGood' :
          isLess array[right - 1 - (block - 1)]! pivot = false := by
        simpa only using hedgeGood
      rw [swp_get! array edge hole (right - 1 - last) hedge hhole]
      have htarget : right - 1 - last = hole := by simp [hole]; omega
      rw [if_neg (by omega), if_pos htarget]
      rw [haddress] at hedgeGood'
      exact hedgeGood'
    · intro offset hoffset hne
      have hpositionNeHole : right - 1 - offset ≠ hole := by
        simp only [hole, last]
        intro heq
        exact hne (right_block_address_injective right offset last
          (by simp only [block] at *; omega)
          (by simp only [block] at hlast; omega) (by omega))
      have hpositionNeEdge : right - 1 - offset ≠ edge := by
        simp only [block, edge] at hoffset ⊢
        omega
      rw [swp_get! array edge hole (right - 1 - offset) hedge hhole,
        if_neg hpositionNeEdge, if_neg hpositionNeHole]
  have hblockEq : block - 1 = right - (left + 1) := by
    simp only [block] at *
    omega
  simpa only [next, edge, hole, last, hblockEq] using
    And.intro hnextPrefix (And.intro hnextSuffix hnextExact)

private theorem cleanupRight_order
    (indices : List ℕ) (pivot : T) (isLess : T → T → Bool)
    (start right : ℕ) (offsets : Array ℕ) :
    ∀ (endIdx left : ℕ) (array : Array T),
      start ≤ endIdx → endIdx - start < indices.length →
      left ≤ right → right ≤ array.size → endIdx ≤ offsets.size →
      RangeAll array 0 left (fun item => isLess item pivot = true) →
      RangeAll array right array.size
        (fun item => isLess item pivot = false) →
      OffsetScanExact (right - left) start endIdx offsets
        (fun offset => isLess array[right - 1 - offset]! pivot) →
      let result := cleanupRight indices start right offsets
        ⟨endIdx, left, array⟩
      RangeAll result.2.2 0 result.2.1
          (fun item => isLess item pivot = true) ∧
        RangeAll result.2.2 result.2.1 result.2.2.size
          (fun item => isLess item pivot = false) := by
  induction indices with
  | nil =>
      intro endIdx left array hstart hfuel
      simp at hfuel
  | cons index indices inductionHypothesis =>
      intro endIdx left array hstart hfuel hlr hright hend
        hprefix hsuffix hexact
      rw [cleanupRight_cons]
      by_cases hactive : start < endIdx
      · rw [if_pos hactive]
        have hstep := cleanupRightStep_order array pivot isLess
          start endIdx left right offsets hactive hlr hright hend
          hprefix hsuffix hexact
        have hlast := OffsetScanExact.active (right - left) start endIdx
          offsets (fun offset => isLess array[right - 1 - offset]! pivot)
          hexact hend (endIdx - 1) (by omega) (by omega)
        have hleftLtRight : left < right := by omega
        let next := swp array left (right - offsets[endIdx - 1]! - 1)
        have hnextSize : next.size = array.size := by simp [next, swp_size]
        apply inductionHypothesis (endIdx - 1) (left + 1) next
        · omega
        · simp only [List.length_cons] at hfuel
          omega
        · omega
        · rw [hnextSize]
          omega
        · omega
        · simpa only [next] using hstep.1
        · simpa only [next] using hstep.2.1
        · simpa only [next] using hstep.2.2
      · rw [if_neg hactive]
        have hdone : start = endIdx := by omega
        have hmiddle : RangeAll array left right
            (fun item => isLess item pivot = false) := by
          have hexhausted := exhausted_right_block_rangeAll array pivot
            isLess right (right - left) endIdx offsets (by omega) (by
              simpa only [hdone] using hexact)
          simpa only [Nat.sub_sub_self hlr] using hexhausted
        exact ⟨hprefix, RangeAll.append hmiddle hsuffix⟩

omit [Inhabited T] in
private theorem min_remaining_exhausts
    (startL endL startR endR : ℕ)
    (hleft : startL ≤ endL) (hright : startR ≤ endR) :
    let count := min (endL - startL) (endR - startR)
    startL + count = endL ∨ startR + count = endR := by
  simp only
  rcases le_total (endL - startL) (endR - startR) with h | h
  · left
    rw [min_eq_left h]
    omega
  · right
    rw [min_eq_right h]
    omega

omit [Inhabited T] in
private theorem advance_block_bounds
    (n l r blockL blockR : ℕ)
    (advanceL advanceR : Bool)
    (hlr : l ≤ r) (hrn : r ≤ n)
    (hblocks : blockL + blockR ≤ r - l) :
    let l' := if advanceL = true then l + blockL else l
    let r' := if advanceR = true then r - blockR else r
    l' ≤ r' ∧ r' ≤ n := by
  by_cases hL : advanceL = true
  · by_cases hR : advanceR = true
    · simp only [if_pos hL, if_pos hR]
      omega
    · simp only [if_pos hL, if_neg hR]
      omega
  · by_cases hR : advanceR = true
    · simp only [if_neg hL, if_pos hR]
      omega
    · simp only [if_neg hL, if_neg hR]
      omega

omit [Inhabited T] in
private theorem forIn_step_invariant
    {ι S : Type} (P : S → Prop) (step : ι → S → ForInStep S)
    (hstep : ∀ i s, P s →
      match step i s with
      | .done s' => P s'
      | .yield s' => P s') :
    ∀ (indices : List ι) (initial : S),
      P initial →
      P (Id.run <|
        forIn indices initial fun i s => pure (step i s)) := by
  intro indices
  induction indices with
  | nil =>
      intro initial hinitial
      simpa using hinitial
  | cons i indices ih =>
      intro initial hinitial
      simp only [List.forIn_cons]
      cases hresult : step i initial with
      | done result =>
          simpa [hresult] using hstep i initial hinitial
      | yield result =>
          simpa [hresult] using
            ih result (by
              simpa [hresult] using hstep i initial hinitial)

omit [Inhabited T] in
private theorem forIn_step_post
    {ι S : Type} (P Q : S → Prop)
    (step : ι → S → ForInStep S)
    (hyield : ∀ i s s', P s →
      step i s = .yield s' → P s')
    (hdone : ∀ i s s', P s →
      step i s = .done s' → Q s')
    (hexhausted : ∀ s, P s → Q s) :
    ∀ (indices : List ι) (initial : S),
      P initial →
      Q (Id.run <|
        forIn indices initial fun i s => pure (step i s)) := by
  intro indices
  induction indices with
  | nil =>
      intro initial hinitial
      exact hexhausted initial hinitial
  | cons i indices ih =>
      intro initial hinitial
      simp only [List.forIn_cons]
      cases hresult : step i initial with
      | done result =>
          simpa [hresult] using
            hdone i initial result hinitial hresult
      | yield result =>
          simpa [hresult] using
            ih result (hyield i initial result hinitial hresult)

omit [Inhabited T] in
private theorem forIn_step_decreasing_post
    {ι S : Type} (P Q : S → Prop) (measure : S → ℕ)
    (step : ι → S → ForInStep S)
    (hyield : ∀ i s s', P s → step i s = .yield s' →
      P s' ∧ measure s' < measure s)
    (hdone : ∀ i s s', P s → step i s = .done s' → Q s') :
    ∀ (indices : List ι) (initial : S),
      P initial → measure initial < indices.length →
      Q (Id.run <|
        forIn indices initial fun i s => pure (step i s)) := by
  intro indices
  induction indices with
  | nil =>
      intro initial hinitial hfuel
      simp at hfuel
  | cons index indices inductionHypothesis =>
      intro initial hinitial hfuel
      simp only [List.forIn_cons]
      cases hresult : step index initial with
      | done result =>
          simpa [hresult] using hdone index initial result hinitial hresult
      | yield result =>
          have hnext := hyield index initial result hinitial hresult
          simpa [hresult] using inductionHypothesis result hnext.1 (by
            simp only [List.length_cons] at hfuel
            omega)

private structure BlockCoreResult (T : Type) where
  v : Array T
  l : ℕ
  r : ℕ
  startL : ℕ
  endL : ℕ
  offsetsL : Array ℕ
  startR : ℕ
  endR : ℕ
  offsetsR : Array ℕ

private def blockCore
    (a : Array T) (pivot : T) (isLess : T → T → Bool)
    (l r blockL blockR : ℕ)
    (offsetsL offsetsR : Array ℕ)
    (startL endL startR endR : ℕ) : BlockCoreResult T :=
  let leftData := refreshOffsets blockL startL endL offsetsL
    (fun i => !isLess a[l + i]! pivot)
  let rightData := refreshOffsets blockR startR endR offsetsR
    (fun i => isLess a[r - 1 - i]! pivot)
  let count := min (leftData.2.1 - leftData.1)
    (rightData.2.1 - rightData.1)
  let newStartL := leftData.1 + count
  let newStartR := rightData.1 + count
  let advanceL := decide (newStartL = leftData.2.1)
  let advanceR := decide (newStartR = rightData.2.1)
  {
    v := blockMutateArray a pivot isLess l r blockL blockR
      offsetsL offsetsR startL endL startR endR
    l := if advanceL = true then l + blockL else l
    r := if advanceR = true then r - blockR else r
    startL := newStartL
    endL := leftData.2.1
    offsetsL := leftData.2.2
    startR := newStartR
    endR := rightData.2.1
    offsetsR := rightData.2.2
  }

private theorem blockCore_offsets_exact
    (a : Array T) (pivot : T) (isLess : T → T → Bool)
    (l r blockL blockR : ℕ)
    (offsetsL offsetsR : Array ℕ)
    (startL endL startR endR : ℕ)
    (hlr : l ≤ r) (hrsize : r ≤ a.size)
    (hblocks : blockL + blockR ≤ r - l)
    (hblockL : blockL ≤ offsetsL.size)
    (hblockR : blockR ≤ offsetsR.size)
    (hstartL : startL ≤ endL)
    (hendL : startL ≠ endL → endL ≤ blockL)
    (hstartR : startR ≤ endR)
    (hendR : startR ≠ endR → endR ≤ blockR)
    (hactiveL : startL ≠ endL →
      ∀ j, j < endL → offsetsL[j]! < blockL)
    (hactiveR : startR ≠ endR →
      ∀ j, j < endR → offsetsR[j]! < blockR)
    (hexactL : startL ≠ endL →
      OffsetScanExact blockL startL endL offsetsL
        (fun index => !isLess a[l + index]! pivot))
    (hexactR : startR ≠ endR →
      OffsetScanExact blockR startR endR offsetsR
        (fun index => isLess a[r - 1 - index]! pivot)) :
    let core := blockCore a pivot isLess l r blockL blockR
      offsetsL offsetsR startL endL startR endR
    OffsetScanExact blockL core.startL core.endL core.offsetsL
        (fun index => !isLess core.v[l + index]! pivot) ∧
      OffsetScanExact blockR core.startR core.endR core.offsetsR
        (fun index => isLess core.v[r - 1 - index]! pivot) ∧
      ∀ position, position < l ∨ r ≤ position →
        core.v[position]! = a[position]! := by
  simpa only [blockCore] using blockMutateArray_offsets_exact
    a pivot isLess l r blockL blockR offsetsL offsetsR
    startL endL startR endR hlr hrsize hblocks hblockL hblockR
    hstartL hendL hstartR hendR hactiveL hactiveR hexactL hexactR

private theorem blockCore_perm
    (a : Array T) (pivot : T) (isLess : T → T → Bool)
    (l r blockL blockR : ℕ)
    (offsetsL offsetsR : Array ℕ)
    (startL endL startR endR : ℕ)
    (hlr : l ≤ r) (hrsize : r ≤ a.size)
    (hblockLgap : blockL ≤ r - l)
    (hblockRgap : blockR ≤ r - l)
    (hsizeL : offsetsL.size = 128)
    (hsizeR : offsetsR.size = 128)
    (hblockL : blockL ≤ 128)
    (hblockR : blockR ≤ 128)
    (hstartL : startL ≤ endL)
    (hendL : startL ≠ endL → endL ≤ blockL)
    (hstartR : startR ≤ endR)
    (hendR : startR ≠ endR → endR ≤ blockR)
    (hactiveL : startL ≠ endL →
      ∀ j, j < endL → offsetsL[j]! < blockL)
    (hactiveR : startR ≠ endR →
      ∀ j, j < endR → offsetsR[j]! < blockR) :
    List.Perm
      (blockCore a pivot isLess l r blockL blockR offsetsL offsetsR
        startL endL startR endR).v.toList
      a.toList := by
  apply blockMutateArray_perm a pivot isLess l r blockL blockR
    offsetsL offsetsR startL endL startR endR
    hlr hrsize hblockLgap hblockRgap hsizeL hsizeR
    hblockL hblockR hstartL hendL hstartR hendR
    hactiveL hactiveR

private theorem blockCore_cursor_bounds
    (a : Array T) (pivot : T) (isLess : T → T → Bool)
    (l r blockL blockR : ℕ)
    (offsetsL offsetsR : Array ℕ)
    (startL endL startR endR : ℕ)
    (n : ℕ)
    (hlr : l ≤ r) (hrn : r ≤ n)
    (hblocks : blockL + blockR ≤ r - l) :
    let result := blockCore a pivot isLess l r blockL blockR
      offsetsL offsetsR startL endL startR endR
    result.l ≤ result.r ∧ result.r ≤ n := by
  apply advance_block_bounds n l r blockL blockR
  · exact hlr
  · exact hrn
  · exact hblocks

private theorem blockCore_offset_bounds
    (a : Array T) (pivot : T) (isLess : T → T → Bool)
    (l r blockL blockR : ℕ)
    (offsetsL offsetsR : Array ℕ)
    (startL endL startR endR : ℕ)
    (hsizeL : offsetsL.size = 128)
    (hsizeR : offsetsR.size = 128)
    (hblockL : blockL ≤ 128)
    (hblockR : blockR ≤ 128)
    (hstartL : startL ≤ endL)
    (hendL : startL ≠ endL → endL ≤ blockL)
    (hstartR : startR ≤ endR)
    (hendR : startR ≠ endR → endR ≤ blockR)
    (hactiveL : startL ≠ endL →
      ∀ j, j < endL → offsetsL[j]! < blockL)
    (hactiveR : startR ≠ endR →
      ∀ j, j < endR → offsetsR[j]! < blockR) :
    let result := blockCore a pivot isLess l r blockL blockR
      offsetsL offsetsR startL endL startR endR
    result.startL ≤ result.endL ∧
      result.endL ≤ blockL ∧
      result.offsetsL.size = 128 ∧
      (∀ j, j < result.endL →
        result.offsetsL[j]! < blockL) ∧
      result.startR ≤ result.endR ∧
      result.endR ≤ blockR ∧
      result.offsetsR.size = 128 ∧
      (∀ j, j < result.endR →
        result.offsetsR[j]! < blockR) ∧
      (result.startL = result.endL ∨
        result.startR = result.endR) := by
  let leftData := refreshOffsets blockL startL endL offsetsL
    (fun i => !isLess a[l + i]! pivot)
  let rightData := refreshOffsets blockR startR endR offsetsR
    (fun i => isLess a[r - 1 - i]! pivot)
  have hleft := refreshOffsets_bounds blockL startL endL offsetsL
    (fun i => !isLess a[l + i]! pivot)
    (by omega) hstartL hendL hactiveL
  have hright := refreshOffsets_bounds blockR startR endR offsetsR
    (fun i => isLess a[r - 1 - i]! pivot)
    (by omega) hstartR hendR hactiveR
  let count := min (leftData.2.1 - leftData.1)
    (rightData.2.1 - rightData.1)
  have hcountL : count ≤ leftData.2.1 - leftData.1 :=
    min_le_left _ _
  have hcountR : count ≤ rightData.2.1 - rightData.1 :=
    min_le_right _ _
  have hexhaust := min_remaining_exhausts
    leftData.1 leftData.2.1 rightData.1 rightData.2.1
    hleft.1 hright.1
  dsimp only [blockCore]
  exact ⟨by omega, hleft.2.1, by omega, hleft.2.2.2,
    by omega, hright.2.1, by omega, hright.2.2.2,
    by simpa only [count] using hexhaust⟩

private structure BlockLoopState (T : Type) where
  v : Array T
  l : ℕ
  r : ℕ
  blockL : ℕ
  blockR : ℕ
  startL : ℕ
  endL : ℕ
  offsetsL : Array ℕ
  startR : ℕ
  endR : ℕ
  offsetsR : Array ℕ

private def blockCoreState
    (blockL blockR : ℕ) (core : BlockCoreResult T) :
    BlockLoopState T := {
  v := core.v
  l := core.l
  r := core.r
  blockL := blockL
  blockR := blockR
  startL := core.startL
  endL := core.endL
  offsetsL := core.offsetsL
  startR := core.startR
  endR := core.endR
  offsetsR := core.offsetsR
}

private def blockLoopStep
    (pivot : T) (isLess : T → T → Bool)
    (state : BlockLoopState T) : ForInStep (BlockLoopState T) :=
  let gap := state.r - state.l
  let isDone := decide (gap ≤ 2 * 128)
  let pendingL := decide (state.startL < state.endL)
  let pendingR := decide (state.startR < state.endR)
  let adjusted := adjustBlockSizes gap state.blockL state.blockR
    pendingL pendingR
  let core := blockCore state.v pivot isLess state.l state.r
    adjusted.1 adjusted.2 state.offsetsL state.offsetsR
    state.startL state.endL state.startR state.endR
  let result := blockCoreState adjusted.1 adjusted.2 core
  if isDone = true then .done result else .yield result

private def BlockPreInv
    (original : Array T) (state : BlockLoopState T) : Prop :=
  List.Perm state.v.toList original.toList ∧
  state.v.size = original.size ∧
  state.l ≤ state.r ∧ state.r ≤ state.v.size ∧
  state.blockL = 128 ∧ state.blockR = 128 ∧
  state.offsetsL.size = 128 ∧ state.offsetsR.size = 128 ∧
  state.startL ≤ state.endL ∧ state.endL ≤ 128 ∧
  state.startR ≤ state.endR ∧ state.endR ≤ 128 ∧
  (∀ j, j < state.endL → state.offsetsL[j]! < 128) ∧
  (∀ j, j < state.endR → state.offsetsR[j]! < 128) ∧
  ¬(state.startL < state.endL ∧
    state.startR < state.endR) ∧
  (state.startL < state.endL → 128 ≤ state.r - state.l) ∧
  (state.startR < state.endR → 128 ≤ state.r - state.l)

private def BlockCleanupInv
    (original : Array T) (state : BlockLoopState T) : Prop :=
  List.Perm state.v.toList original.toList ∧
  state.l ≤ state.r ∧ state.r ≤ state.v.size ∧
  state.v.size = original.size ∧
  state.startL ≤ state.endL ∧
  state.startR ≤ state.endR ∧
  ¬(state.startL < state.endL ∧
    state.startR < state.endR) ∧
  (state.startL < state.endL →
    state.endL - state.startL ≤ state.r ∧
    ∀ j, j < state.endL →
      state.l + state.offsetsL[j]! < state.v.size) ∧
  (state.startR < state.endR →
    state.endR - state.startR ≤ state.r - state.l ∧
    ∀ j, j < state.endR →
      state.offsetsR[j]! < state.r)

private def BlockOrderInv
    (pivot : T) (isLess : T → T → Bool)
    (state : BlockLoopState T) : Prop :=
  RangeAll state.v 0 state.l
      (fun item => isLess item pivot = true) ∧
    RangeAll state.v state.r state.v.size
      (fun item => isLess item pivot = false) ∧
    (state.startL ≠ state.endL →
      OffsetScanExact state.blockL state.startL state.endL
        state.offsetsL
        (fun offset => !isLess state.v[state.l + offset]! pivot)) ∧
    (state.startR ≠ state.endR →
      OffsetScanExact state.blockR state.startR state.endR
        state.offsetsR
        (fun offset => isLess state.v[state.r - 1 - offset]! pivot))

private def BlockDoneShape (state : BlockLoopState T) : Prop :=
  state.offsetsL.size = 128 ∧ state.offsetsR.size = 128 ∧
    state.endL ≤ 128 ∧ state.endR ≤ 128 ∧
    (state.startL < state.endL →
      state.l + state.blockL = state.r) ∧
    (state.startR < state.endR →
      state.l + state.blockR = state.r) ∧
    (state.startL = state.endL → state.startR = state.endR →
      state.l = state.r)

omit [Inhabited T] in
private theorem blockPreInv_cleanup
    (original : Array T) (state : BlockLoopState T)
    (hinv : BlockPreInv original state) :
    BlockCleanupInv original state := by
  rcases hinv with
    ⟨hperm, hsize, hlr, hrsize, hblockL, hblockR,
      hsizeL, hsizeR, hstartL, hendL, hstartR, hendR,
      hactiveL, hactiveR, hatMostOne, hpendingL,
      hpendingR⟩
  refine ⟨hperm, hlr, hrsize, hsize, hstartL, hstartR,
    hatMostOne, ?_, ?_⟩
  · intro hpending
    constructor
    · have hgap := hpendingL hpending
      omega
    · intro j hj
      have hoff := hactiveL j hj
      have hgap := hpendingL hpending
      omega
  · intro hpending
    constructor
    · have hgap := hpendingR hpending
      omega
    · intro j hj
      have hoff := hactiveR j hj
      have hgap := hpendingR hpending
      omega

private theorem blockCore_cursor_eq
    (a : Array T) (pivot : T) (isLess : T → T → Bool)
    (l r blockL blockR : ℕ)
    (offsetsL offsetsR : Array ℕ)
    (startL endL startR endR : ℕ) :
    let result := blockCore a pivot isLess l r blockL blockR
      offsetsL offsetsR startL endL startR endR
    result.l =
        (if result.startL = result.endL then l + blockL else l) ∧
      result.r =
        (if result.startR = result.endR then r - blockR else r) := by
  simp [blockCore]

private theorem blockCore_orderInv
    (a : Array T) (pivot : T) (isLess : T → T → Bool)
    (l r blockL blockR : ℕ)
    (offsetsL offsetsR : Array ℕ)
    (startL endL startR endR : ℕ)
    (hlr : l ≤ r) (hrsize : r ≤ a.size)
    (hblocks : blockL + blockR ≤ r - l)
    (hblockL : blockL ≤ offsetsL.size)
    (hblockR : blockR ≤ offsetsR.size)
    (hstartL : startL ≤ endL)
    (hendL : startL ≠ endL → endL ≤ blockL)
    (hstartR : startR ≤ endR)
    (hendR : startR ≠ endR → endR ≤ blockR)
    (hactiveL : startL ≠ endL →
      ∀ j, j < endL → offsetsL[j]! < blockL)
    (hactiveR : startR ≠ endR →
      ∀ j, j < endR → offsetsR[j]! < blockR)
    (hprefix : RangeAll a 0 l
      (fun item => isLess item pivot = true))
    (hsuffix : RangeAll a r a.size
      (fun item => isLess item pivot = false))
    (hexactL : startL ≠ endL →
      OffsetScanExact blockL startL endL offsetsL
        (fun offset => !isLess a[l + offset]! pivot))
    (hexactR : startR ≠ endR →
      OffsetScanExact blockR startR endR offsetsR
        (fun offset => isLess a[r - 1 - offset]! pivot)) :
    let core := blockCore a pivot isLess l r blockL blockR
      offsetsL offsetsR startL endL startR endR
    BlockOrderInv pivot isLess (blockCoreState blockL blockR core) := by
  let core := blockCore a pivot isLess l r blockL blockR
    offsetsL offsetsR startL endL startR endR
  have hcoreExact :
      OffsetScanExact blockL core.startL core.endL core.offsetsL
          (fun offset => !isLess core.v[l + offset]! pivot) ∧
        OffsetScanExact blockR core.startR core.endR core.offsetsR
          (fun offset => isLess core.v[r - 1 - offset]! pivot) ∧
        ∀ position, position < l ∨ r ≤ position →
          core.v[position]! = a[position]! := by
    simpa only [core] using blockCore_offsets_exact a pivot isLess
      l r blockL blockR offsetsL offsetsR startL endL startR endR
      hlr hrsize hblocks hblockL hblockR hstartL hendL
      hstartR hendR hactiveL hactiveR hexactL hexactR
  have hcursor :
      core.l =
          (if core.startL = core.endL then l + blockL else l) ∧
        core.r =
          (if core.startR = core.endR then r - blockR else r) := by
    simpa only [core] using blockCore_cursor_eq a pivot isLess
      l r blockL blockR offsetsL offsetsR startL endL startR endR
  have hprefixTransfer : RangeAll core.v 0 l
      (fun item => isLess item pivot = true) :=
    RangeAll.transfer hprefix (by
      intro position _ hposition
      exact hcoreExact.2.2 position (Or.inl hposition))
  have hsuffixTransfer : RangeAll core.v r core.v.size
      (fun item => isLess item pivot = false) := by
    have hcoreSize : core.v.size = a.size := by
      simpa only [core, blockCore] using blockMutateArray_size
        a pivot isLess l r blockL blockR offsetsL offsetsR
        startL endL startR endR
    rw [hcoreSize]
    apply RangeAll.transfer hsuffix
    intro position hposition hsize
    exact hcoreExact.2.2 position (Or.inr hposition)
  unfold BlockOrderInv
  simp only [blockCoreState]
  constructor
  · by_cases hdone : core.startL = core.endL
    · rw [hcursor.1, if_pos hdone]
      apply RangeAll.append hprefixTransfer
      exact exhausted_left_block_rangeAll core.v pivot isLess
        l blockL core.endL core.offsetsL (by simpa [hdone] using hcoreExact.1)
    · rw [hcursor.1, if_neg hdone]
      exact hprefixTransfer
  constructor
  · by_cases hdone : core.startR = core.endR
    · rw [hcursor.2, if_pos hdone]
      apply RangeAll.append
      · exact exhausted_right_block_rangeAll core.v pivot isLess
          r blockR core.endR core.offsetsR
          (right_block_le l r blockL blockR hblocks)
          (by simpa [hdone] using hcoreExact.2.1)
      · exact hsuffixTransfer
    · rw [hcursor.2, if_neg hdone]
      exact hsuffixTransfer
  constructor
  · intro hpending
    rw [hcursor.1, if_neg hpending]
    exact hcoreExact.1
  · intro hpending
    rw [hcursor.2, if_neg hpending]
    exact hcoreExact.2.1

omit [Inhabited T] in
private theorem blockCleanupInv_coreState
    (original : Array T) (blockL blockR : ℕ)
    (core : BlockCoreResult T)
    (hperm : List.Perm core.v.toList original.toList)
    (hlr : core.l ≤ core.r) (hrsize : core.r ≤ core.v.size)
    (hsize : core.v.size = original.size)
    (hstartL : core.startL ≤ core.endL)
    (hstartR : core.startR ≤ core.endR)
    (hatMostOne :
      ¬(core.startL < core.endL ∧
        core.startR < core.endR))
    (hleft : core.startL < core.endL →
      core.endL - core.startL ≤ core.r ∧
      ∀ j, j < core.endL →
        core.l + core.offsetsL[j]! < core.v.size)
    (hright : core.startR < core.endR →
      core.endR - core.startR ≤ core.r - core.l ∧
      ∀ j, j < core.endR →
        core.offsetsR[j]! < core.r) :
    BlockCleanupInv original
      (blockCoreState blockL blockR core) := by
  exact ⟨hperm, hlr, hrsize, hsize, hstartL, hstartR,
    hatMostOne, hleft, hright⟩

omit [Inhabited T] in
private theorem core_pending_left_cleanup
    (core : BlockCoreResult T)
    (aSize l r blockL blockR : ℕ)
    (hblocks : blockL + blockR ≤ r - l)
    (hcoreSize : core.v.size = aSize)
    (hend : core.endL ≤ blockL)
    (hactive : ∀ j, j < core.endL →
      core.offsetsL[j]! < blockL)
    (hexhaust :
      core.startL = core.endL ∨
        core.startR = core.endR)
    (hcursorL :
      core.l =
        if core.startL = core.endL then l + blockL else l)
    (hcursorR :
      core.r =
        if core.startR = core.endR then r - blockR else r)
    (hrsize : r ≤ aSize) :
    core.startL < core.endL →
      core.endL - core.startL ≤ core.r ∧
      ∀ j, j < core.endL →
        core.l + core.offsetsL[j]! < core.v.size := by
  intro hpending
  have hdoneR : core.startR = core.endR := by
    rcases hexhaust with hdoneL | hdoneR
    · omega
    · exact hdoneR
  have hlEq : core.l = l := by
    rw [hcursorL, if_neg (ne_of_lt hpending)]
  have hrEq : core.r = r - blockR := by
    rw [hcursorR, if_pos hdoneR]
  constructor
  · rw [hrEq]
    omega
  · intro j hj
    have hoff := hactive j hj
    rw [hlEq, hcoreSize]
    omega

omit [Inhabited T] in
private theorem core_pending_right_cleanup
    (core : BlockCoreResult T)
    (l r blockL blockR : ℕ)
    (hblocks : blockL + blockR ≤ r - l)
    (hend : core.endR ≤ blockR)
    (hactive : ∀ j, j < core.endR →
      core.offsetsR[j]! < blockR)
    (hexhaust :
      core.startL = core.endL ∨
        core.startR = core.endR)
    (hcursorL :
      core.l =
        if core.startL = core.endL then l + blockL else l)
    (hcursorR :
      core.r =
        if core.startR = core.endR then r - blockR else r) :
    core.startR < core.endR →
      core.endR - core.startR ≤ core.r - core.l ∧
      ∀ j, j < core.endR →
        core.offsetsR[j]! < core.r := by
  intro hpending
  have hdoneL : core.startL = core.endL := by
    rcases hexhaust with hdoneL | hdoneR
    · exact hdoneL
    · omega
  have hlEq : core.l = l + blockL := by
    rw [hcursorL, if_pos hdoneL]
  have hrEq : core.r = r := by
    rw [hcursorR, if_neg (ne_of_lt hpending)]
  constructor
  · rw [hlEq, hrEq]
    omega
  · intro j hj
    have hoff := hactive j hj
    rw [hrEq]
    have hblockRr : blockR ≤ r := by omega
    exact hoff.trans_le hblockRr

omit [Inhabited T] in
private theorem blockPreInv_coreState
    (original : Array T) (core : BlockCoreResult T)
    (hperm : List.Perm core.v.toList original.toList)
    (hsize : core.v.size = original.size)
    (hlr : core.l ≤ core.r) (hrsize : core.r ≤ core.v.size)
    (hsizeL : core.offsetsL.size = 128)
    (hsizeR : core.offsetsR.size = 128)
    (hstartL : core.startL ≤ core.endL)
    (hendL : core.endL ≤ 128)
    (hstartR : core.startR ≤ core.endR)
    (hendR : core.endR ≤ 128)
    (hactiveL : ∀ j, j < core.endL →
      core.offsetsL[j]! < 128)
    (hactiveR : ∀ j, j < core.endR →
      core.offsetsR[j]! < 128)
    (hatMostOne :
      ¬(core.startL < core.endL ∧
        core.startR < core.endR))
    (hpendingL :
      core.startL < core.endL →
        128 ≤ core.r - core.l)
    (hpendingR :
      core.startR < core.endR →
        128 ≤ core.r - core.l) :
    BlockPreInv original (blockCoreState 128 128 core) := by
  exact ⟨hperm, hsize, hlr, hrsize, rfl, rfl,
    hsizeL, hsizeR, hstartL, hendL, hstartR, hendR,
    hactiveL, hactiveR, hatMostOne, hpendingL, hpendingR⟩

omit [Inhabited T] in
private theorem yielded_core_pending_gap
    (core : BlockCoreResult T) (l r : ℕ)
    (hgap : 2 * 128 < r - l)
    (hexhaust :
      core.startL = core.endL ∨
        core.startR = core.endR)
    (hcursorL :
      core.l =
        if core.startL = core.endL then l + 128 else l)
    (hcursorR :
      core.r =
        if core.startR = core.endR then r - 128 else r) :
    (core.startL < core.endL →
      128 ≤ core.r - core.l) ∧
    (core.startR < core.endR →
      128 ≤ core.r - core.l) := by
  constructor
  · intro hpendingL
    have hdoneR : core.startR = core.endR := by
      rcases hexhaust with hdoneL | hdoneR
      · omega
      · exact hdoneR
    rw [hcursorL, if_neg (ne_of_lt hpendingL),
      hcursorR, if_pos hdoneR]
    omega
  · intro hpendingR
    have hdoneL : core.startL = core.endL := by
      rcases hexhaust with hdoneL | hdoneR
      · exact hdoneL
      · omega
    rw [hcursorL, if_pos hdoneL,
      hcursorR, if_neg (ne_of_lt hpendingR)]
    omega

private theorem blockCoreState_cleanup
    (original a : Array T) (pivot : T)
    (isLess : T → T → Bool)
    (l r blockL blockR : ℕ)
    (offsetsL offsetsR : Array ℕ)
    (startL endL startR endR : ℕ)
    (hperm : List.Perm a.toList original.toList)
    (hlr : l ≤ r) (hrsize : r ≤ a.size)
    (hblocks : blockL + blockR ≤ r - l)
    (hsizeL : offsetsL.size = 128)
    (hsizeR : offsetsR.size = 128)
    (hblockL : blockL ≤ 128)
    (hblockR : blockR ≤ 128)
    (hstartL : startL ≤ endL)
    (hendL : startL ≠ endL → endL ≤ blockL)
    (hstartR : startR ≤ endR)
    (hendR : startR ≠ endR → endR ≤ blockR)
    (hactiveL : startL ≠ endL →
      ∀ j, j < endL → offsetsL[j]! < blockL)
    (hactiveR : startR ≠ endR →
      ∀ j, j < endR → offsetsR[j]! < blockR) :
    let core := blockCore a pivot isLess l r blockL blockR
      offsetsL offsetsR startL endL startR endR
    BlockCleanupInv original
      (blockCoreState blockL blockR core) := by
  let core := blockCore a pivot isLess l r blockL blockR
    offsetsL offsetsR startL endL startR endR
  have hcorePerm : List.Perm core.v.toList original.toList :=
    (blockCore_perm a pivot isLess l r blockL blockR
      offsetsL offsetsR startL endL startR endR
      hlr hrsize
      (by omega) (by omega)
      hsizeL hsizeR hblockL hblockR
      hstartL hendL hstartR hendR hactiveL hactiveR).trans
      hperm
  have hcursorRaw := blockCore_cursor_bounds a pivot isLess
    l r blockL blockR offsetsL offsetsR
    startL endL startR endR a.size hlr hrsize hblocks
  change core.l ≤ core.r ∧ core.r ≤ a.size at hcursorRaw
  have hcursor := hcursorRaw
  have hoffsetsRaw := blockCore_offset_bounds a pivot isLess
    l r blockL blockR offsetsL offsetsR
    startL endL startR endR hsizeL hsizeR
    hblockL hblockR hstartL hendL hstartR hendR
    hactiveL hactiveR
  change
      core.startL ≤ core.endL ∧
      core.endL ≤ blockL ∧
      core.offsetsL.size = 128 ∧
      (∀ j, j < core.endL → core.offsetsL[j]! < blockL) ∧
      core.startR ≤ core.endR ∧
      core.endR ≤ blockR ∧
      core.offsetsR.size = 128 ∧
      (∀ j, j < core.endR → core.offsetsR[j]! < blockR) ∧
      (core.startL = core.endL ∨
        core.startR = core.endR) at hoffsetsRaw
  have hoffsets := hoffsetsRaw
  rcases hoffsets with
    ⟨hcStartL, hcEndL, hcSizeL, hcActiveL,
      hcStartR, hcEndR, hcSizeR, hcActiveR, hcExhaust⟩
  have hcursorEqRaw := blockCore_cursor_eq a pivot isLess
    l r blockL blockR offsetsL offsetsR
    startL endL startR endR
  change
      core.l =
          (if core.startL = core.endL then l + blockL else l) ∧
        core.r =
          (if core.startR = core.endR then r - blockR else r)
    at hcursorEqRaw
  have hcursorEq := hcursorEqRaw
  have hcoreSize : core.v.size = original.size := by
    simpa using hcorePerm.length_eq
  have hcoreASize : core.v.size = a.size := by
    have haSize : a.size = original.size := by
      simpa using hperm.length_eq
    omega
  have hatMostOne :
      ¬(core.startL < core.endL ∧
        core.startR < core.endR) := by
    intro hpending
    rcases hcExhaust with hdoneL | hdoneR
    · omega
    · omega
  apply blockCleanupInv_coreState original blockL blockR core
    hcorePerm hcursor.1
    (hcursor.2.trans_eq hcoreASize.symm)
    hcoreSize hcStartL hcStartR hatMostOne
  · exact core_pending_left_cleanup core a.size l r
      blockL blockR hblocks hcoreASize hcEndL hcActiveL
      hcExhaust hcursorEq.1 hcursorEq.2 hrsize
  · exact core_pending_right_cleanup core l r blockL blockR
      hblocks hcEndR hcActiveR hcExhaust
      hcursorEq.1 hcursorEq.2

private theorem blockLoopStep_cleanup
    (original : Array T) (pivot : T)
    (isLess : T → T → Bool) (state : BlockLoopState T)
    (hinv : BlockPreInv original state) :
    match blockLoopStep pivot isLess state with
    | .done result => BlockCleanupInv original result
    | .yield result => BlockCleanupInv original result := by
  rcases state with
    ⟨a, l, r, blockL, blockR, startL, endL, offsetsL,
      startR, endR, offsetsR⟩
  simp only [BlockPreInv] at hinv
  rcases hinv with
    ⟨hperm, hsize, hlr, hrsize, hblockLEq, hblockREq,
      hsizeL, hsizeR, hstartL, hendL, hstartR, hendR,
      hactiveL, hactiveR, hatMostOne, hpendingL,
      hpendingR⟩
  let gap := r - l
  let pendingL := decide (startL < endL)
  let pendingR := decide (startR < endR)
  let adjusted := adjustBlockSizes gap blockL blockR
    pendingL pendingR
  have hadjust := adjustBlockSizes_bounds gap blockL blockR
    pendingL pendingR
    (by
      intro hlarge
      exact ⟨by omega, by omega, by omega⟩)
    (by
      intro hdone hpending
      have hp : startL < endL := by
        simpa [pendingL] using hpending
      exact ⟨hblockLEq, hpendingL hp⟩)
    (by
      intro hdone hpending
      have hp : startR < endR := by
        simpa [pendingR] using hpending
      exact ⟨hblockREq, hpendingR hp⟩)
  have hleftEnd :
      startL ≠ endL → endL ≤ adjusted.1 := by
    intro hne
    have hp : startL < endL := by omega
    have hadjustLeft : adjusted.1 = blockL := by
      simp only [adjusted, adjustBlockSizes]
      by_cases hdone : gap ≤ 2 * 128 <;>
        simp [hdone, pendingL, hp]
    omega
  have hrightEnd :
      startR ≠ endR → endR ≤ adjusted.2 := by
    intro hne
    have hp : startR < endR := by omega
    have hpBool : pendingR = true := by simp [pendingR, hp]
    have hleftFalse : pendingL = false := by
      simp only [pendingL, decide_eq_false_iff_not]
      intro hpLeft
      exact hatMostOne ⟨hpLeft, hp⟩
    have hadjustRight : adjusted.2 = blockR := by
      simp only [adjusted, adjustBlockSizes]
      by_cases hdone : gap ≤ 2 * 128 <;>
        simp [hdone, pendingR, hp, hleftFalse]
    omega
  have hcleanup := blockCoreState_cleanup original a pivot isLess
    l r adjusted.1 adjusted.2 offsetsL offsetsR
    startL endL startR endR hperm hlr
    (by omega) hadjust.2.2 hsizeL hsizeR
    hadjust.1 hadjust.2.1 hstartL hleftEnd
    hstartR hrightEnd
    (by
      intro hne j hj
      have hp : startL < endL := by omega
      have hadjustLeft : adjusted.1 = blockL := by
        simp only [adjusted, adjustBlockSizes]
        by_cases hdone : gap ≤ 2 * 128 <;>
          simp [hdone, pendingL, hp]
      simpa [hadjustLeft, hblockLEq] using hactiveL j hj)
    (by
      intro hne j hj
      have hp : startR < endR := by omega
      have hleftFalse : pendingL = false := by
        simp only [pendingL, decide_eq_false_iff_not]
        intro hpLeft
        exact hatMostOne ⟨hpLeft, hp⟩
      have hadjustRight : adjusted.2 = blockR := by
        simp only [adjusted, adjustBlockSizes]
        by_cases hdone : gap ≤ 2 * 128 <;>
          simp [hdone, pendingR, hp, hleftFalse]
      simpa [hadjustRight, hblockREq] using hactiveR j hj)
  by_cases hdone : gap ≤ 2 * 128
  · simpa [blockLoopStep, gap, pendingL, pendingR, adjusted,
      hdone] using hcleanup
  · simpa [blockLoopStep, gap, pendingL, pendingR, adjusted,
      hdone] using hcleanup

private theorem blockLoopStep_order
    (original : Array T) (pivot : T)
    (isLess : T → T → Bool) (state : BlockLoopState T)
    (hpre : BlockPreInv original state)
    (horder : BlockOrderInv pivot isLess state) :
    match blockLoopStep pivot isLess state with
    | .done result =>
        BlockOrderInv pivot isLess result ∧ BlockDoneShape result
    | .yield result => BlockOrderInv pivot isLess result := by
  rcases state with
    ⟨a, l, r, blockL, blockR, startL, endL, offsetsL,
      startR, endR, offsetsR⟩
  simp only [BlockPreInv] at hpre
  rcases hpre with
    ⟨hperm, hsize, hlr, hrsize, hblockLEq, hblockREq,
      hsizeL, hsizeR, hstartL, hendL, hstartR, hendR,
      hactiveL, hactiveR, hatMostOne, hpendingL, hpendingR⟩
  simp only [BlockOrderInv] at horder
  rcases horder with ⟨hprefix, hsuffix, hexactL, hexactR⟩
  let gap := r - l
  let pendingL := decide (startL < endL)
  let pendingR := decide (startR < endR)
  let adjusted := adjustBlockSizes gap blockL blockR pendingL pendingR
  have hadjust := adjustBlockSizes_bounds gap blockL blockR
    pendingL pendingR
    (by
      intro hlarge
      exact ⟨by omega, by omega, by omega⟩)
    (by
      intro hdone hpending
      have hp : startL < endL := by simpa [pendingL] using hpending
      exact ⟨hblockLEq, hpendingL hp⟩)
    (by
      intro hdone hpending
      have hp : startR < endR := by simpa [pendingR] using hpending
      exact ⟨hblockREq, hpendingR hp⟩)
  have hadjustLeft : startL ≠ endL → adjusted.1 = blockL := by
    intro hne
    have hp : startL < endL := by omega
    simp only [adjusted, adjustBlockSizes]
    by_cases hdone : gap ≤ 2 * 128 <;> simp [hdone, pendingL, hp]
  have hadjustRight : startR ≠ endR → adjusted.2 = blockR := by
    intro hne
    have hp : startR < endR := by omega
    have hleftFalse : pendingL = false := by
      simp only [pendingL, decide_eq_false_iff_not]
      intro hpLeft
      exact hatMostOne ⟨hpLeft, hp⟩
    simp only [adjusted, adjustBlockSizes]
    by_cases hdone : gap ≤ 2 * 128 <;>
      simp [hdone, pendingR, hp, hleftFalse]
  let core := blockCore a pivot isLess l r adjusted.1 adjusted.2
    offsetsL offsetsR startL endL startR endR
  have hcoreOrder : BlockOrderInv pivot isLess
      (blockCoreState adjusted.1 adjusted.2 core) := by
    simpa only [core] using blockCore_orderInv a pivot isLess
      l r adjusted.1 adjusted.2 offsetsL offsetsR
      startL endL startR endR hlr (by omega) hadjust.2.2
      (hadjust.1.trans_eq hsizeL.symm)
      (hadjust.2.1.trans_eq hsizeR.symm)
      hstartL (fun hne => by
        rw [hadjustLeft hne]
        simpa only [hblockLEq] using hendL)
      hstartR (fun hne => by
        rw [hadjustRight hne]
        simpa only [hblockREq] using hendR)
      (by
        intro hne j hj
        rw [hadjustLeft hne]
        simpa only [hblockLEq] using hactiveL j hj)
      (by
        intro hne j hj
        rw [hadjustRight hne]
        simpa only [hblockREq] using hactiveR j hj)
      hprefix hsuffix
      (by
        intro hne
        rw [hadjustLeft hne]
        simpa only [hblockLEq] using hexactL hne)
      (by
        intro hne
        rw [hadjustRight hne]
        simpa only [hblockREq] using hexactR hne)
  by_cases hdone : gap ≤ 2 * 128
  · have hadjustDone : adjusted.1 + adjusted.2 = gap :=
      (adjustBlockSizes_done gap blockL blockR pendingL pendingR hdone
        (by
          intro hpending
          have hp : startL < endL := by simpa [pendingL] using hpending
          exact ⟨hblockLEq, hpendingL hp⟩)
        (by
          intro hpending
          have hp : startR < endR := by simpa [pendingR] using hpending
          exact ⟨hblockREq, hpendingR hp⟩)).2.2
    have hoffsets := blockCore_offset_bounds a pivot isLess
      l r adjusted.1 adjusted.2 offsetsL offsetsR
      startL endL startR endR hsizeL hsizeR hadjust.1 hadjust.2.1
      hstartL (fun hne => by
        rw [hadjustLeft hne]
        simpa only [hblockLEq] using hendL)
      hstartR (fun hne => by
        rw [hadjustRight hne]
        simpa only [hblockREq] using hendR)
      (by
        intro hne j hj
        rw [hadjustLeft hne]
        simpa only [hblockLEq] using hactiveL j hj)
      (by
        intro hne j hj
        rw [hadjustRight hne]
        simpa only [hblockREq] using hactiveR j hj)
    have hoffsetsCore :
        core.startL ≤ core.endL ∧ core.endL ≤ adjusted.1 ∧
        core.offsetsL.size = 128 ∧
        (∀ j, j < core.endL → core.offsetsL[j]! < adjusted.1) ∧
        core.startR ≤ core.endR ∧ core.endR ≤ adjusted.2 ∧
        core.offsetsR.size = 128 ∧
        (∀ j, j < core.endR → core.offsetsR[j]! < adjusted.2) ∧
        (core.startL = core.endL ∨ core.startR = core.endR) := by
      simpa only [core] using hoffsets
    rcases hoffsetsCore with
      ⟨_, hcoreEndL, hcoreSizeL, _, _, hcoreEndR,
        hcoreSizeR, _, hexhaust⟩
    have hcursor :
        core.l =
            (if core.startL = core.endL then l + adjusted.1 else l) ∧
          core.r =
            (if core.startR = core.endR then r - adjusted.2 else r) := by
      simpa only [core] using blockCore_cursor_eq a pivot isLess
        l r adjusted.1 adjusted.2 offsetsL offsetsR
        startL endL startR endR
    have hshape : BlockDoneShape
        (blockCoreState adjusted.1 adjusted.2 core) := by
      unfold BlockDoneShape
      simp only [blockCoreState]
      refine ⟨hcoreSizeL, hcoreSizeR,
        hcoreEndL.trans hadjust.1, hcoreEndR.trans hadjust.2.1,
        ?_, ?_, ?_⟩
      · intro hpending
        have hdoneR : core.startR = core.endR := by
          rcases hexhaust with hdoneL | hdoneR
          · omega
          · exact hdoneR
        rw [hcursor.1, if_neg (ne_of_lt hpending),
          hcursor.2, if_pos hdoneR]
        simp only [gap] at hadjustDone
        omega
      · intro hpending
        have hdoneL : core.startL = core.endL := by
          rcases hexhaust with hdoneL | hdoneR
          · exact hdoneL
          · omega
        rw [hcursor.1, if_pos hdoneL,
          hcursor.2, if_neg (ne_of_lt hpending)]
        simp only [gap] at hadjustDone
        omega
      · intro hdoneL hdoneR
        rw [hcursor.1, if_pos hdoneL, hcursor.2, if_pos hdoneR]
        simp only [gap] at hadjustDone
        omega
    simpa [blockLoopStep, gap, pendingL, pendingR, adjusted,
      core, hdone] using And.intro hcoreOrder hshape
  · simpa [blockLoopStep, gap, pendingL, pendingR, adjusted,
      core, hdone] using hcoreOrder

private theorem blockLoopStep_yield_pre
    (original : Array T) (pivot : T)
    (isLess : T → T → Bool)
    (state result : BlockLoopState T)
    (hinv : BlockPreInv original state)
    (hstep : blockLoopStep pivot isLess state = .yield result) :
    BlockPreInv original result ∧
      result.r - result.l < state.r - state.l := by
  rcases state with
    ⟨a, l, r, blockL, blockR, startL, endL, offsetsL,
      startR, endR, offsetsR⟩
  simp only [BlockPreInv] at hinv
  rcases hinv with
    ⟨hperm, hsize, hlr, hrsize, hblockLEq, hblockREq,
      hsizeL, hsizeR, hstartL, hendL, hstartR, hendR,
      hactiveL, hactiveR, hatMostOne, hpendingL,
      hpendingR⟩
  subst blockL
  subst blockR
  let core := blockCore a pivot isLess l r 128 128
    offsetsL offsetsR startL endL startR endR
  have hnotDone : ¬r - l ≤ 2 * 128 := by
    intro hdone
    simp [blockLoopStep, adjustBlockSizes, hdone] at hstep
  have hresult :
      result = blockCoreState 128 128 core := by
    simpa [blockLoopStep, adjustBlockSizes, hnotDone, core]
      using hstep.symm
  subst result
  have hgap : 2 * 128 < r - l := by omega
  have hcorePerm : List.Perm core.v.toList original.toList :=
    (blockCore_perm a pivot isLess l r 128 128
      offsetsL offsetsR startL endL startR endR
      hlr (by omega) (by omega) (by omega)
      hsizeL hsizeR (by omega) (by omega)
      hstartL (fun _ => hendL) hstartR (fun _ => hendR)
      (fun _ => hactiveL) (fun _ => hactiveR)).trans hperm
  have hcursorRaw := blockCore_cursor_bounds a pivot isLess
    l r 128 128 offsetsL offsetsR
    startL endL startR endR a.size hlr (by omega)
    (by omega)
  change core.l ≤ core.r ∧ core.r ≤ a.size at hcursorRaw
  have hoffsetsRaw := blockCore_offset_bounds a pivot isLess
    l r 128 128 offsetsL offsetsR
    startL endL startR endR hsizeL hsizeR
    (by omega) (by omega)
    hstartL (fun _ => hendL) hstartR (fun _ => hendR)
    (fun _ => hactiveL) (fun _ => hactiveR)
  change
    core.startL ≤ core.endL ∧
    core.endL ≤ 128 ∧ core.offsetsL.size = 128 ∧
    (∀ j, j < core.endL → core.offsetsL[j]! < 128) ∧
    core.startR ≤ core.endR ∧
    core.endR ≤ 128 ∧ core.offsetsR.size = 128 ∧
    (∀ j, j < core.endR → core.offsetsR[j]! < 128) ∧
    (core.startL = core.endL ∨ core.startR = core.endR)
      at hoffsetsRaw
  rcases hoffsetsRaw with
    ⟨hcStartL, hcEndL, hcSizeL, hcActiveL,
      hcStartR, hcEndR, hcSizeR, hcActiveR, hcExhaust⟩
  have hcursorEqRaw := blockCore_cursor_eq a pivot isLess
    l r 128 128 offsetsL offsetsR
    startL endL startR endR
  change
    core.l =
        (if core.startL = core.endL then l + 128 else l) ∧
      core.r =
        (if core.startR = core.endR then r - 128 else r)
    at hcursorEqRaw
  have hpendingGap := yielded_core_pending_gap core l r
    hgap hcExhaust hcursorEqRaw.1 hcursorEqRaw.2
  have hgapDecrease : core.r - core.l < r - l := by
    rcases hcExhaust with hdoneL | hdoneR
    · rw [hcursorEqRaw.1, if_pos hdoneL]
      by_cases hdoneRight : core.startR = core.endR
      · rw [hcursorEqRaw.2, if_pos hdoneRight]
        omega
      · rw [hcursorEqRaw.2, if_neg hdoneRight]
        omega
    · rw [hcursorEqRaw.2, if_pos hdoneR]
      by_cases hdoneLeft : core.startL = core.endL
      · rw [hcursorEqRaw.1, if_pos hdoneLeft]
        omega
      · rw [hcursorEqRaw.1, if_neg hdoneLeft]
        omega
  have hcoreSize : core.v.size = original.size := by
    simpa using hcorePerm.length_eq
  have hcoreASize : core.v.size = a.size := by omega
  have hatMostOneCore :
      ¬(core.startL < core.endL ∧
        core.startR < core.endR) := by
    intro hpending
    rcases hcExhaust with hdoneL | hdoneR <;> omega
  exact ⟨blockPreInv_coreState original core hcorePerm hcoreSize
      hcursorRaw.1 (hcursorRaw.2.trans_eq hcoreASize.symm)
      hcSizeL hcSizeR hcStartL hcEndL hcStartR hcEndR
      hcActiveL hcActiveR hatMostOneCore
      hpendingGap.1 hpendingGap.2,
    hgapDecrease⟩

private theorem blockLoop_contract
    (v : Array T) (pivot : T) (isLess : T → T → Bool) :
    let initial : BlockLoopState T := {
      v := v
      l := 0
      r := v.size
      blockL := 128
      blockR := 128
      startL := 0
      endL := 0
      offsetsL := Array.replicate 128 0
      startR := 0
      endR := 0
      offsetsR := Array.replicate 128 0
    }
    let result := Id.run <|
      forIn (List.range' 0 (v.size + 4)) initial
        fun _ state => pure (blockLoopStep pivot isLess state)
    BlockCleanupInv v result := by
  let initial : BlockLoopState T := {
    v := v
    l := 0
    r := v.size
    blockL := 128
    blockR := 128
    startL := 0
    endL := 0
    offsetsL := Array.replicate 128 0
    startR := 0
    endR := 0
    offsetsR := Array.replicate 128 0
  }
  apply forIn_step_post
    (BlockPreInv v) (BlockCleanupInv v)
    (fun _ state => blockLoopStep pivot isLess state)
  · intro _ state result hinv hstep
    exact blockLoopStep_yield_pre v pivot isLess
      state result hinv hstep |>.1
  · intro _ state result hinv hstep
    have hout := blockLoopStep_cleanup v pivot isLess state hinv
    rw [hstep] at hout
    exact hout
  · exact blockPreInv_cleanup v
  · show BlockPreInv v initial
    simp [BlockPreInv, initial]

private theorem blockLoop_order_contract
    (v : Array T) (pivot : T) (isLess : T → T → Bool) :
    let initial : BlockLoopState T := {
      v := v
      l := 0
      r := v.size
      blockL := 128
      blockR := 128
      startL := 0
      endL := 0
      offsetsL := Array.replicate 128 0
      startR := 0
      endR := 0
      offsetsR := Array.replicate 128 0
    }
    let result := Id.run <|
      forIn (List.range' 0 (v.size + 4)) initial
        fun _ state => pure (blockLoopStep pivot isLess state)
    BlockCleanupInv v result ∧ BlockOrderInv pivot isLess result ∧
      BlockDoneShape result := by
  let initial : BlockLoopState T := {
    v := v
    l := 0
    r := v.size
    blockL := 128
    blockR := 128
    startL := 0
    endL := 0
    offsetsL := Array.replicate 128 0
    startR := 0
    endR := 0
    offsetsR := Array.replicate 128 0
  }
  apply forIn_step_decreasing_post
    (fun state => BlockPreInv v state ∧
      BlockOrderInv pivot isLess state)
    (fun state => BlockCleanupInv v state ∧
      BlockOrderInv pivot isLess state ∧ BlockDoneShape state)
    (fun state => state.r - state.l)
    (fun _ state => blockLoopStep pivot isLess state)
  · intro _ state result hinv hstep
    have hprogress := blockLoopStep_yield_pre v pivot isLess
      state result hinv.1 hstep
    have horder := blockLoopStep_order v pivot isLess state
      hinv.1 hinv.2
    rw [hstep] at horder
    exact ⟨⟨hprogress.1, horder⟩, hprogress.2⟩
  · intro _ state result hinv hstep
    have hcleanup := blockLoopStep_cleanup v pivot isLess state hinv.1
    have horder := blockLoopStep_order v pivot isLess state
      hinv.1 hinv.2
    rw [hstep] at hcleanup horder
    exact ⟨hcleanup, horder.1, horder.2⟩
  · constructor
    · show BlockPreInv v initial
      simp [BlockPreInv, initial]
    · show BlockOrderInv pivot isLess initial
      simp [BlockOrderInv, initial, RangeAll.empty]
  · simp

private def partitionInBlocksFactored
    (v : Array T) (pivot : T)
    (isLess : T → T → Bool) : ℕ × Array T :=
  let initial : BlockLoopState T := {
    v := v
    l := 0
    r := v.size
    blockL := 128
    blockR := 128
    startL := 0
    endL := 0
    offsetsL := Array.replicate 128 0
    startR := 0
    endR := 0
    offsetsR := Array.replicate 128 0
  }
  let state := Id.run <|
    forIn (List.range' 0 (v.size + 4)) initial
      fun _ state => pure (blockLoopStep pivot isLess state)
  if state.startL < state.endL then
    let result := cleanupLeft (List.range' 0 (128 + 1))
      state.startL state.l state.offsetsL
      ⟨state.endL, state.r, state.v⟩
    (result.2.1, result.2.2)
  else if state.startR < state.endR then
    let result := cleanupRight (List.range' 0 (128 + 1))
      state.startR state.r state.offsetsR
      ⟨state.endR, state.l, state.v⟩
    (result.2.1, result.2.2)
  else
    (state.l, state.v)

private theorem partitionInBlocksFactored_eq
    (v : Array T) (pivot : T) (isLess : T → T → Bool) :
    let initial : BlockLoopState T := {
      v := v
      l := 0
      r := v.size
      blockL := 128
      blockR := 128
      startL := 0
      endL := 0
      offsetsL := Array.replicate 128 0
      startR := 0
      endR := 0
      offsetsR := Array.replicate 128 0
    }
    let state := Id.run <|
      forIn (List.range' 0 (v.size + 4)) initial
        fun _ state => pure (blockLoopStep pivot isLess state)
    partitionInBlocksFactored v pivot isLess =
      if state.startL < state.endL then
        let result := cleanupLeft (List.range' 0 (128 + 1))
          state.startL state.l state.offsetsL
          ⟨state.endL, state.r, state.v⟩
        (result.2.1, result.2.2)
      else if state.startR < state.endR then
        let result := cleanupRight (List.range' 0 (128 + 1))
          state.startR state.r state.offsetsR
          ⟨state.endR, state.l, state.v⟩
        (result.2.1, result.2.2)
      else
        (state.l, state.v) := by
  rfl

theorem partitionInBlocksFactored_contract
    (v : Array T) (pivot : T) (isLess : T → T → Bool) :
    let result := partitionInBlocksFactored v pivot isLess
    result.1 ≤ v.size ∧
      List.Perm result.2.toList v.toList := by
  let initial : BlockLoopState T := {
    v := v
    l := 0
    r := v.size
    blockL := 128
    blockR := 128
    startL := 0
    endL := 0
    offsetsL := Array.replicate 128 0
    startR := 0
    endR := 0
    offsetsR := Array.replicate 128 0
  }
  let state := Id.run <|
    forIn (List.range' 0 (v.size + 4)) initial
      fun _ state => pure (blockLoopStep pivot isLess state)
  have hinv := blockLoop_contract v pivot isLess
  change BlockCleanupInv v state at hinv
  rcases hinv with
    ⟨hperm, hlr, hrsize, hsize, hstartL, hstartR,
      hatMostOne, hleft, hright⟩
  unfold partitionInBlocksFactored
  change
    (if state.startL < state.endL then
      let result := cleanupLeft (List.range' 0 (128 + 1))
        state.startL state.l state.offsetsL
        ⟨state.endL, state.r, state.v⟩
      (result.2.1, result.2.2)
    else if state.startR < state.endR then
      let result := cleanupRight (List.range' 0 (128 + 1))
        state.startR state.r state.offsetsR
        ⟨state.endR, state.l, state.v⟩
      (result.2.1, result.2.2)
    else
      (state.l, state.v)).1 ≤ v.size ∧
    List.Perm
      (if state.startL < state.endL then
        let result := cleanupLeft (List.range' 0 (128 + 1))
          state.startL state.l state.offsetsL
          ⟨state.endL, state.r, state.v⟩
        (result.2.1, result.2.2)
      else if state.startR < state.endR then
        let result := cleanupRight (List.range' 0 (128 + 1))
          state.startR state.r state.offsetsR
          ⟨state.endR, state.l, state.v⟩
        (result.2.1, result.2.2)
      else
        (state.l, state.v)).2.toList
      v.toList
  by_cases hpendingL : state.startL < state.endL
  · simp only [if_pos hpendingL]
    have hfacts := hleft hpendingL
    exact cleanupLeft_contract (T := T)
      (List.range' 0 (128 + 1))
      state.startL state.l state.offsetsL
      state.endL state.r state.v v
      hstartL hfacts.1 hrsize hfacts.2 hperm
  · simp only [if_neg hpendingL]
    by_cases hpendingR : state.startR < state.endR
    · simp only [if_pos hpendingR]
      have hfacts := hright hpendingR
      exact cleanupRight_contract (T := T)
        (List.range' 0 (128 + 1))
        state.startR state.r state.offsetsR
        state.endR state.l state.v v
        hstartR hlr hfacts.1 hrsize hfacts.2 hperm
    · simp only [if_neg hpendingR]
      exact ⟨by omega, hperm⟩

theorem partitionInBlocksFactored_order
    (v : Array T) (pivot : T) (isLess : T → T → Bool) :
    let result := partitionInBlocksFactored v pivot isLess
    RangeAll result.2 0 result.1
        (fun item => isLess item pivot = true) ∧
      RangeAll result.2 result.1 result.2.size
        (fun item => isLess item pivot = false) := by
  let initial : BlockLoopState T := {
    v := v
    l := 0
    r := v.size
    blockL := 128
    blockR := 128
    startL := 0
    endL := 0
    offsetsL := Array.replicate 128 0
    startR := 0
    endR := 0
    offsetsR := Array.replicate 128 0
  }
  let state := Id.run <|
    forIn (List.range' 0 (v.size + 4)) initial
      fun _ state => pure (blockLoopStep pivot isLess state)
  have hinv := blockLoop_order_contract v pivot isLess
  have htyped : BlockCleanupInv v state ∧
      BlockOrderInv pivot isLess state ∧ BlockDoneShape state := by
    simpa only [initial, state] using hinv
  rcases htyped with ⟨hcleanup, horder, hshape⟩
  simp only [BlockCleanupInv] at hcleanup
  rcases hcleanup with
    ⟨hperm, hlr, hrsize, hsize, hstartL, hstartR,
      hatMostOne, hleft, hright⟩
  simp only [BlockOrderInv] at horder
  rcases horder with ⟨hprefix, hsuffix, hexactL, hexactR⟩
  simp only [BlockDoneShape] at hshape
  rcases hshape with
    ⟨hsizeL, hsizeR, hendL, hendR, hleftShape,
      hrightShape, hclosed⟩
  have hpartition : partitionInBlocksFactored v pivot isLess =
      (if state.startL < state.endL then
        let result := cleanupLeft (List.range' 0 (128 + 1))
          state.startL state.l state.offsetsL
          ⟨state.endL, state.r, state.v⟩
        (result.2.1, result.2.2)
      else if state.startR < state.endR then
        let result := cleanupRight (List.range' 0 (128 + 1))
          state.startR state.r state.offsetsR
          ⟨state.endR, state.l, state.v⟩
        (result.2.1, result.2.2)
      else (state.l, state.v)) := by
    simpa only [initial, state] using
      partitionInBlocksFactored_eq v pivot isLess
  rw [hpartition]
  by_cases hpendingL : state.startL < state.endL
  · simp only [if_pos hpendingL]
    have hblock : state.blockL = state.r - state.l := by
      have := hleftShape hpendingL
      omega
    have hresult := cleanupLeft_order (T := T)
      (List.range' 0 (128 + 1)) pivot isLess
      state.startL state.l state.offsetsL
      state.endL state.r state.v hstartL (by
        simp
        omega) hlr hrsize (by omega) hprefix hsuffix (by
          simpa only [hblock] using
            hexactL (ne_of_lt hpendingL))
    simpa only [initial, state] using hresult
  · simp only [if_neg hpendingL]
    by_cases hpendingR : state.startR < state.endR
    · simp only [if_pos hpendingR]
      have hblock : state.blockR = state.r - state.l := by
        have := hrightShape hpendingR
        omega
      have hresult := cleanupRight_order (T := T)
        (List.range' 0 (128 + 1)) pivot isLess
        state.startR state.r state.offsetsR
        state.endR state.l state.v hstartR (by
          simp
          omega) hlr hrsize (by omega) hprefix hsuffix (by
            simpa only [hblock] using
              hexactR (ne_of_lt hpendingR))
      simpa only [initial, state] using hresult
    · simp only [if_neg hpendingR]
      have hdoneL : state.startL = state.endL := by omega
      have hdoneR : state.startR = state.endR := by omega
      have hlrEq : state.l = state.r := hclosed hdoneL hdoneR
      exact ⟨hprefix, by simpa only [hlrEq] using hsuffix⟩

/-- `partition_in_blocks` (`sort.rs:233-465`), implemented through the
proved phase decomposition above. -/
def partitionInBlocks (v : Array T) (pivot : T)
    (isLess : T → T → Bool) : ℕ × Array T :=
  partitionInBlocksFactored v pivot isLess

/-- The block partition returns an in-bounds split and only permutes its input. -/
theorem partitionInBlocks_contract
    (v : Array T) (pivot : T) (isLess : T → T → Bool) :
    let result := partitionInBlocks v pivot isLess
    result.1 ≤ v.size ∧ List.Perm result.2.toList v.toList := by
  simpa only [partitionInBlocks] using
    partitionInBlocksFactored_contract v pivot isLess

/-- The block partition places precisely the `isLess` elements before its
split and all remaining elements after it. -/
theorem partitionInBlocks_order
    (v : Array T) (pivot : T) (isLess : T → T → Bool) :
    let result := partitionInBlocks v pivot isLess
    RangeAll result.2 0 result.1
        (fun item => isLess item pivot = true) ∧
      RangeAll result.2 result.1 result.2.size
        (fun item => isLess item pivot = false) := by
  simpa only [partitionInBlocks] using
    partitionInBlocksFactored_order v pivot isLess

/-- `partition` (`sort.rs:474-521`): partition around `v[pivotIdx]`. Returns
`((#elements < pivot, was_already_partitioned), mutated slice)`. -/
def partitionP (v0 : Array T) (pivotIdx : ℕ) (isLess : T → T → Bool) : (ℕ × Bool) × Array T := Id.run do
  let mut v := swp v0 0 pivotIdx
  let pivotVal := v[0]!
  let n := v.size
  let mut l : ℕ := 0
  let mut r : ℕ := n - 1
  for _ in [0:n] do
    if l < r && isLess (v[1+l]!) pivotVal then l := l + 1 else break
  for _ in [0:n] do
    if l < r && !isLess (v[1+(r-1)]!) pivotVal then r := r - 1 else break
  let (cnt, sub') := partitionInBlocks (v.extract (1+l) (1+r)) pivotVal isLess
  v := overwrite v (1+l) sub'
  let mid := l + cnt
  let wasP := decide (l ≥ r)
  v := swp v 0 mid
  return ((mid, wasP), v)

/-- `partition_equal` (`sort.rs:527-579`): partition `[==pivot | >pivot]` (assumes no element
`< pivot`). Returns the number equal to the pivot (incl. the pivot) and the mutated slice. -/
def partitionEqual (v0 : Array T) (pivotIdx : ℕ) (isLess : T → T → Bool) : ℕ × Array T := Id.run do
  let mut v := swp v0 0 pivotIdx
  let pivotVal := v[0]!
  let n := v.size
  let mut l : ℕ := 0
  let mut r : ℕ := n - 1
  let mut done := false
  for _ in [0:n+1] do
    if !done then
      for _ in [0:n] do
        if l < r && !isLess pivotVal (v[1+l]!) then l := l + 1 else break
      for _ in [0:n] do
        if l < r && isLess pivotVal (v[1+(r-1)]!) then r := r - 1 else break
      if l ≥ r then done := true
      else
        r := r - 1
        v := swp v (1+l) (1+r)
        l := l + 1
  return (l+1, v)

/-- Smallest power of two `≥ n` (`usize::next_power_of_two`). -/
def nextPow2 (n : ℕ) : ℕ := Id.run do
  let mut p := 1
  for _ in [0:64] do
    if p ≥ n then break
    p := p * 2
  return p

/-- `break_patterns` (`sort.rs:584-620`): pseudo-random swaps to defeat adversarial patterns.
Uses the MODIFIED (deterministic, 64-bit) Xorshift with two `gen_u32` calls per `gen_usize`
(`sort.rs:595-597`). u32 wrapping arithmetic is modelled with `UInt32`. -/
def breakPatterns (v0 : Array T) : Array T := Id.run do
  let mut v := v0
  let len := v.size
  if len ≥ 8 then
    let mut random : UInt32 := len.toUInt32
    let modulus := nextPow2 len
    let pos := len/4*2
    for i in [0:3] do
      random := random ^^^ (random <<< 13)
      random := random ^^^ (random >>> 17)
      random := random ^^^ (random <<< 5)
      let hi := random
      random := random ^^^ (random <<< 13)
      random := random ^^^ (random >>> 17)
      random := random ^^^ (random <<< 5)
      let lo := random
      let g : UInt64 := (hi.toUInt64 <<< 32) ||| lo.toUInt64
      let mut other : ℕ := g.toNat % modulus
      if other ≥ len then other := other - len
      v := swp v (pos - 1 + i) other
  return v

/-- `choose_pivot` (`sort.rs:625-686`): median-of-medians pivot selection. Returns
`((pivot index, likely-sorted), mutated slice)`. `sort2`/`sort3` reorder INDEX variables
(comparing `v` at those indices), not the slice; only the final `v.reverse()` mutates `v`. -/
def choosePivot (v0 : Array T) (isLess : T → T → Bool) : (ℕ × Bool) × Array T := Id.run do
  let mut v := v0
  let len := v.size
  let mut a := len/4*1
  let mut b := len/4*2
  let mut c := len/4*3
  let mut swaps : ℕ := 0
  -- sort2/sort3 as pure functions over index triples, threading the swap counter.
  let sort2 := fun (x y sw : ℕ) => if isLess (v[y]!) (v[x]!) then (y, x, sw+1) else (x, y, sw)
  let sort3 := fun (x y z sw : ℕ) =>
    let (x, y, sw) := sort2 x y sw
    let (y, z, sw) := sort2 y z sw
    let (x, y, sw) := sort2 x y sw
    (x, y, z, sw)
  if len ≥ 8 then
    if len ≥ 50 then
      let (_, ya, _, sw) := sort3 (a-1) a (a+1) swaps; a := ya; swaps := sw
      let (_, yb, _, sw) := sort3 (b-1) b (b+1) swaps; b := yb; swaps := sw
      let (_, yc, _, sw) := sort3 (c-1) c (c+1) swaps; c := yc; swaps := sw
    let (xa, yb, zc, sw) := sort3 a b c swaps
    a := xa; b := yb; c := zc; swaps := sw
  if swaps < 4*3 then
    return ((b, decide (swaps == 0)), v)
  else
    v := v.reverse
    return ((len - 1 - b, true), v)

/-- `partial_insertion_sort` (`sort.rs:129-172`). Returns `(sorted?, mutated slice)`. -/
def partialInsertionSort (v0 : Array T) (isLess : T → T → Bool) : Bool × Array T := Id.run do
  let MAX_STEPS := 5
  let SHORTEST_SHIFTING := 50
  let mut v := v0
  let len := v.size
  let mut i : ℕ := 1
  let mut result : Option Bool := none
  for _ in [0:MAX_STEPS] do
    if result.isNone then
      for _ in [0:len+1] do
        if i < len && !isLess (v[i]!) (v[i-1]!) then i := i + 1 else break
      if i == len then result := some true
      else if len < SHORTEST_SHIFTING then result := some false
      else
        v := swp v (i-1) i
        v := overwrite v 0 (shiftTail (v.extract 0 i) isLess)
        v := overwrite v i (shiftHead (v.extract i v.size) isLess)
  return (result.getD false, v)

/--
The ordinary pivot split, factored out of the recursive driver.  Making this
phase explicit avoids normalizing the entire `Id.run` program when proving its
local permutation law.
-/
private def recursePartition
    (rec : Array T → Option T → ℕ → Bool → Bool → Array T)
    (v : Array T) (isLess : T → T → Bool) (pred : Option T)
    (limit len : ℕ) (pivot : ℕ) : Array T :=
  let ((mid, wasP), v4) := partitionP v pivot isLess
  let newBalanced := decide (Nat.min mid (len - mid) ≥ len / 8)
  let pivotVal := v4[mid]!
  let left := v4.extract 0 mid
  let right := v4.extract (mid + 1) v4.size
  if left.size < right.size then
    let left' := rec left pred limit true true
    let right' := rec right (some pivotVal) limit newBalanced wasP
    left' ++ #[pivotVal] ++ right'
  else
    let right' := rec right (some pivotVal) limit true true
    let left' := rec left pred limit newBalanced wasP
    left' ++ #[pivotVal] ++ right'

/-- The predecessor-equal fast path, followed by the ordinary pivot split. -/
private def recursePred
    (rec : Array T → Option T → ℕ → Bool → Bool → Array T)
    (v : Array T) (isLess : T → T → Bool) (pred : Option T)
    (limit len : ℕ) (wasBalanced wasPartitioned : Bool)
    (pivot : ℕ) : Array T :=
  match pred with
  | some p =>
    if !isLess p (v[pivot]!) then
      let (mid, v3) := partitionEqual v pivot isLess
      let head := v3.extract 0 mid
      let tail := rec (v3.extract mid v3.size) pred limit
        wasBalanced wasPartitioned
      head ++ tail
    else
      recursePartition rec v isLess pred limit len pivot
  | none =>
    recursePartition rec v isLess pred limit len pivot

/-- Optional partial-insertion fast path after pivot selection. -/
private def recurseAfterPivot
    (rec : Array T → Option T → ℕ → Bool → Bool → Array T)
    (v : Array T) (isLess : T → T → Bool) (pred : Option T)
    (limit len : ℕ) (wasBalanced wasPartitioned likelySorted : Bool)
    (pivot : ℕ) : Array T :=
  if wasBalanced && wasPartitioned && likelySorted then
    let (sorted, v2) := partialInsertionSort v isLess
    if sorted then v2
    else
      recursePred rec v2 isLess pred limit len
        wasBalanced wasPartitioned pivot
  else
    recursePred rec v isLess pred limit len
      wasBalanced wasPartitioned pivot

/-- Pivot selection and the remainder of a long-array driver iteration. -/
private def recurseChoose
    (rec : Array T → Option T → ℕ → Bool → Bool → Array T)
    (v : Array T) (isLess : T → T → Bool) (pred : Option T)
    (limit len : ℕ) (wasBalanced wasPartitioned : Bool) : Array T :=
  let ((pivot, likelySorted), v1) := choosePivot v isLess
  recurseAfterPivot rec v1 isLess pred limit len
    wasBalanced wasPartitioned likelySorted pivot

/-- Pattern breaking before pivot selection. -/
private def recurseLong
    (rec : Array T → Option T → ℕ → Bool → Bool → Array T)
    (v : Array T) (isLess : T → T → Bool) (pred : Option T)
    (limit len : ℕ) (wasBalanced wasPartitioned : Bool) : Array T :=
  if !wasBalanced then
    recurseChoose rec (breakPatterns v) isLess pred (limit - 1) len
      wasBalanced wasPartitioned
  else
    recurseChoose rec v isLess pred limit len
      wasBalanced wasPartitioned

/-- One structurally recursive pdqsort driver step. -/
private def recurseStep
    (rec : Array T → Option T → ℕ → Bool → Bool → Array T)
    (v : Array T) (isLess : T → T → Bool) (pred : Option T)
    (limit : ℕ) (wasBalanced wasPartitioned : Bool) : Array T :=
  let len := v.size
  if len ≤ 20 then insertionSort v isLess
  else if limit == 0 then heapsort v isLess
  else
    recurseLong rec v isLess pred limit len
      wasBalanced wasPartitioned

/-- `recurse` (`sort.rs:694-777`), factored through one proof-facing driver step. -/
def recurse : ℕ → Array T → (T → T → Bool) → Option T → ℕ → Bool → Bool → Array T
  | 0, v, isLess, _, _, _, _ => heapsort v isLess
  | fuel + 1, v, isLess, pred, limit, wasBalanced, wasPartitioned =>
      recurseStep
        (fun v pred limit wasBalanced wasPartitioned =>
          recurse fuel v isLess pred limit wasBalanced wasPartitioned)
        v isLess pred limit wasBalanced wasPartitioned

/-- `quicksort` (`sort.rs:780-793`): `limit = usize::BITS − leading_zeros(len)` = the bit
length of `len` = `Nat.log2 len + 1` for `len ≥ 1`. Fuel `v.size + 1` bounds the
recursion depth (see `recurse`). -/
def quicksort (v : Array T) (isLess : T → T → Bool) : Array T :=
  if v.size == 0 then v
  else recurse (v.size + 1) v isLess none (Nat.log2 v.size + 1) true true

/-! ## Permutation correctness of legacy pdqsort -/

theorem overwrite_size (a : Array T) (start : ℕ) (sub : Array T) :
    (overwrite a start sub).size = a.size := by
  simp [overwrite]
  induction List.range' 0 sub.size generalizing a with
  | nil => rfl
  | cons i indices ih =>
      simp only [List.foldl_cons]
      rw [ih, Array.size_setIfInBounds]

private theorem fold_set_range_toList
    (a sub : Array T) (start n : ℕ)
    (hn : n ≤ sub.size) (hfit : start + n ≤ a.size) :
    (List.foldl
        (fun b i => b.setIfInBounds (start + i) sub[i]!)
        a (List.range n)).toList =
      a.toList.take start ++ sub.toList.take n ++
        a.toList.drop (start + n) := by
  induction n with
  | zero =>
      simp only [List.range_zero, List.foldl_nil, List.take_zero,
        List.append_nil, Nat.add_zero]
      exact (List.take_append_drop start a.toList).symm
  | succ n ih =>
      have hn' : n ≤ sub.size := by omega
      have hfit' : start + n ≤ a.size := by omega
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil,
        Array.toList_setIfInBounds]
      rw [ih hn' hfit', List.set_eq_take_cons_drop]
      ·
        have ha : a.toList.length = a.size := Array.length_toList
        have hs : sub.toList.length = sub.size := Array.length_toList
        have hstart : start ≤ a.toList.length := by omega
        have hnsize : n ≤ sub.toList.length := by omega
        have hidx : n < sub.toList.length := by omega
        have hA : (a.toList.take start).length = start := by
          rw [List.length_take, Nat.min_eq_left hstart]
        have hB : (sub.toList.take n).length = n := by
          rw [List.length_take, Nat.min_eq_left hnsize]
        have hAB :
            (a.toList.take start ++ sub.toList.take n).length =
              start + n := by simp [hA, hB]
        have htake :
            (a.toList.take start ++ sub.toList.take n ++
                a.toList.drop (start + n)).take (start + n) =
              a.toList.take start ++ sub.toList.take n := by
          rw [List.take_append_of_le_length (by omega)]
          apply List.take_of_length_le
          omega
        have hdrop :
            (a.toList.take start ++ sub.toList.take n ++
                a.toList.drop (start + n)).drop (start + n + 1) =
              a.toList.drop (start + (n + 1)) := by
          rw [List.drop_append]
          simp [hAB, List.drop_drop, Nat.add_assoc]
        rw [htake, hdrop,
          show sub[n]! = sub.toList[n] by simp [show n < sub.size by omega]]
        rw [← List.take_append_getElem hidx]
        simp only [List.append_assoc, List.singleton_append]
      ·
        have ha : a.toList.length = a.size := Array.length_toList
        have hs : sub.toList.length = sub.size := Array.length_toList
        simp [List.length_append]
        omega

theorem overwrite_toList (a : Array T) (start : ℕ) (sub : Array T)
    (hfit : start + sub.size ≤ a.size) :
    (overwrite a start sub).toList =
      a.toList.take start ++ sub.toList ++
        a.toList.drop (start + sub.size) := by
  simp [overwrite]
  have ht : sub.toList.take sub.size = sub.toList := by
    rw [← Array.length_toList, List.take_length]
  simpa [List.range'_eq_map_range, ht] using
    fold_set_range_toList a sub start sub.size (Nat.le_refl _) hfit

private theorem arrayToList_getElem!
    (array : Array T) (index : ℕ) :
    array.toList[index]! = array[index]! := by
  by_cases hindex : index < array.size
  · rw [getElem!_pos array.toList index (by simpa using hindex),
      getElem!_pos array index hindex]
    simp
  · rw [getElem!_neg array.toList index (by simpa using hindex),
      getElem!_neg array index hindex]

/-- `overwrite` replaces exactly the requested interval and leaves every
other entry unchanged. -/
theorem overwrite_get!
    (array sub : Array T) (start index : ℕ)
    (hfit : start + sub.size ≤ array.size) :
    (overwrite array start sub)[index]! =
      if start ≤ index ∧ index < start + sub.size then
        sub[index - start]!
      else
        array[index]! := by
  have heq := congrArg (fun values : List T => values[index]!)
    (overwrite_toList array start sub hfit)
  dsimp only at heq
  rw [arrayToList_getElem!] at heq
  rw [heq]
  by_cases hinside : start ≤ index ∧ index < start + sub.size
  · rw [if_pos hinside]
    simp only [List.getElem!_eq_getElem?_getD, List.getElem?_append]
    have htake : (array.toList.take start).length = start := by
      simp only [List.length_take, Array.length_toList]
      omega
    have hprefix :
        (array.toList.take start ++ sub.toList).length =
          start + sub.size := by simp [htake]
    rw [if_pos (by rw [hprefix]; omega), htake,
      if_neg (by omega)]
    rw [List.getElem?_eq_getElem (by simp; omega), Option.getD_some]
    rw [getElem!_pos sub (index - start) (by omega)]
    exact Array.getElem_toList (xs := sub) (by omega)
  · rw [if_neg hinside]
    by_cases hbefore : index < start
    · simp only [List.getElem!_eq_getElem?_getD, List.getElem?_append]
      have htake : (array.toList.take start).length = start := by
        simp only [List.length_take, Array.length_toList]
        omega
      have hprefix :
          (array.toList.take start ++ sub.toList).length =
            start + sub.size := by simp [htake]
      rw [if_pos (by rw [hprefix]; omega),
        if_pos (by rw [htake]; omega)]
      rw [List.getElem?_eq_getElem (by
        simp only [List.length_take, Array.length_toList]
        omega), Option.getD_some, List.getElem_take]
      rw [getElem!_pos array index (by omega)]
      exact Array.getElem_toList (xs := array) (by omega)
    · have hafter : start + sub.size ≤ index := by omega
      simp only [List.getElem!_eq_getElem?_getD, List.getElem?_append]
      have htake : (array.toList.take start).length = start := by
        simp only [List.length_take, Array.length_toList]
        omega
      have hprefix :
          (array.toList.take start ++ sub.toList).length =
            start + sub.size := by simp [htake]
      rw [if_neg (by rw [hprefix]; omega), hprefix]
      by_cases horiginal : index < array.size
      · rw [List.getElem?_eq_getElem (by
            simp only [List.length_drop, Array.length_toList]
            omega), Option.getD_some, List.getElem_drop]
        rw [getElem!_pos array index horiginal]
        simpa only [show start + sub.size + (index - (start + sub.size)) =
            index by omega] using
          Array.getElem_toList (xs := array) horiginal
      · rw [List.getElem?_eq_none (by
            simp only [List.length_drop, Array.length_toList]
            omega), Option.getD_none,
          getElem!_neg array index horiginal]

theorem overwrite_perm_of_extract
    (a : Array T) (start : ℕ) (sub : Array T)
    (hfit : start + sub.size ≤ a.size)
    (hsub : List.Perm sub.toList
      (a.extract start (start + sub.size)).toList) :
    List.Perm (overwrite a start sub).toList a.toList := by
  rw [overwrite_toList a start sub hfit]
  have hsegment :
      (a.extract start (start + sub.size)).toList =
        (a.toList.drop start).take sub.size := by
    simp [Array.toList_extract, List.extract_eq_take_drop]
  have hreplace :
      List.Perm
        (a.toList.take start ++ sub.toList ++
          a.toList.drop (start + sub.size))
        (a.toList.take start ++
          (a.extract start (start + sub.size)).toList ++
          a.toList.drop (start + sub.size)) :=
    by
      simpa only [List.append_assoc] using
        (List.Perm.refl (a.toList.take start)).append
          (hsub.append
            (List.Perm.refl (a.toList.drop (start + sub.size))))
  have horiginal :
      a.toList.take start ++
          (a.extract start (start + sub.size)).toList ++
          a.toList.drop (start + sub.size) =
        a.toList := by
    rw [hsegment, List.append_assoc,
      List.drop_take_append_drop, List.take_append_drop]
  rw [horiginal] at hreplace
  exact hreplace

private theorem list_shift_restore
    (tmp : T) : ∀ (l : List T) (i : ℕ) (_hi : i + 1 < l.length),
    (l.set (i + 1) l[i]!).set i tmp =
      ((l.set (i + 1) tmp).set i tmp).set (i + 1) l[i]! := by
  intro l i
  induction l generalizing i with
  | nil => simp
  | cons a l ih =>
      cases i with
      | zero =>
          intro hi
          cases l with
          | nil => simp at hi
          | cons b l => simp
      | succ i =>
          intro hi
          simpa only [List.getElem!_cons_succ, List.set_cons_succ] using
            congrArg (List.cons a) (ih i (by simpa using hi))

private theorem list_set_self :
    ∀ (l : List T) (i : ℕ), l.set i l[i]! = l := by
  intro l i
  induction l generalizing i with
  | nil => cases i <;> rfl
  | cons a l ih =>
      cases i with
      | zero => rfl
      | succ i =>
          simpa only [List.getElem!_cons_succ, List.set_cons_succ] using
            congrArg (List.cons a) (ih i)

private theorem shift_restore_eq_swp
    (a : Array T) (tmp : T) (i : ℕ) (hi : i + 1 < a.size) :
    (a.set! (i + 1) a[i]!).set! i tmp =
      swp (a.set! (i + 1) tmp) i (i + 1) := by
  apply Array.toList_inj.mp
  unfold swp
  simp only [Array.set!, Array.toList_setIfInBounds]
  rw [show a[i]! = a.toList[i]! by simp [show i < a.size by omega]]
  have hreadi :
      (a.setIfInBounds (i + 1) tmp)[i]! = a.toList[i]! := by
    simp [Array.setIfInBounds, hi,
      show i < a.size by omega]
  have hreadsucc :
      (a.setIfInBounds (i + 1) tmp)[i + 1]! = tmp := by
    simp [Array.setIfInBounds, hi]
  rw [hreadi, hreadsucc]
  exact list_shift_restore tmp a.toList i (by simpa using hi)

private theorem shiftTail_loop_perm
    (tmp : T) (isLess : T → T → Bool) :
    ∀ (n : ℕ) (a original : Array T),
      n < a.size →
      List.Perm (a.set! n tmp).toList original.toList →
      let output : Array T := Id.run do
        pure PUnit.unit
        pure PUnit.unit
        let r ← forIn (List.range n).reverse
          (⟨n, a⟩ : MProd ℕ (Array T)) fun i (r : MProd ℕ (Array T)) =>
          if !isLess tmp (r.snd[i]!) then
            pure (.done ⟨r.fst, r.snd⟩)
          else do
            pure PUnit.unit
            pure PUnit.unit
            pure (.yield ⟨i, r.snd.set! (i + 1) (r.snd[i]!)⟩)
        pure (r.snd.set! r.fst tmp)
      List.Perm output.toList original.toList := by
  intro n
  induction n with
  | zero =>
      intro a original hn hperm
      simpa using hperm
  | succ n ih =>
      intro a original hn hperm
      rw [List.range_succ, List.reverse_append]
      simp only [List.reverse_singleton, List.singleton_append]
      simp only [List.forIn_cons]
      split
      · simpa using hperm
      ·
        apply ih (a.set! (n + 1) a[n]!) original
        · simpa [Array.set!] using Nat.lt_trans (Nat.lt_succ_self n) hn
        · rw [shift_restore_eq_swp a tmp n (by simpa using hn)]
          have hin : n < (a.set! (n + 1) tmp).size := by
            simpa [Array.set!] using Nat.lt_trans (Nat.lt_succ_self n) hn
          have his : n + 1 < (a.set! (n + 1) tmp).size := by
            simpa [Array.set!] using hn
          exact (swp_perm (a.set! (n + 1) tmp) n (n + 1)
            hin his).trans hperm

theorem shiftTail_perm (v : Array T) (isLess : T → T → Bool) :
    List.Perm (shiftTail v isLess).toList v.toList := by
  simp only [shiftTail]
  split
  · simp
  split
  · simp
  ·
    have hnSucc : v.size - 2 + 1 < v.size := by omega
    have hnBase : v.size - 2 < v.size := by omega
    have hn : v.size - 2 <
        (v.set! (v.size - 1) v[v.size - 2]!).size := by
      simpa [Array.set!] using Nat.lt_trans
        (Nat.lt_succ_self (v.size - 2)) hnSucc
    have hinit :
        List.Perm
          ((v.set! (v.size - 1) v[v.size - 2]!).set!
            (v.size - 2) v[v.size - 1]!).toList
          v.toList := by
      rw [show v.size - 1 = v.size - 2 + 1 by omega]
      rw [shift_restore_eq_swp v v[v.size - 2 + 1]!
        (v.size - 2) hnSucc]
      have hp := swp_perm (v.set! (v.size - 2 + 1)
          v[v.size - 2 + 1]!) (v.size - 2) (v.size - 2 + 1)
        (by simpa [Array.set!] using hnBase)
        (by simpa [Array.set!] using hnSucc)
      have hself :
          (v.set! (v.size - 2 + 1) v[v.size - 2 + 1]!).toList =
            v.toList := by
        simp only [Array.set!, Array.toList_setIfInBounds]
        rw [show v[v.size - 2 + 1]! = v.toList[v.size - 2 + 1]! by
          simp [hnSucc]]
        exact list_set_self v.toList (v.size - 2 + 1)
      exact hp.trans (hself ▸ List.Perm.refl v.toList)
    have hloop := shiftTail_loop_perm v[v.size - 1]! isLess
        (v.size - 2) (v.set! (v.size - 1) v[v.size - 2]!) v
        hn hinit
    exact hloop

private theorem list_shiftHead_restore
    (tmp : T) : ∀ (l : List T) (i : ℕ) (_hi : i + 1 < l.length),
    (l.set i l[i + 1]!).set (i + 1) tmp =
      ((l.set i tmp).set i l[i + 1]!).set (i + 1) tmp := by
  intro l i
  induction l generalizing i with
  | nil => simp
  | cons a l ih =>
      cases i with
      | zero =>
          intro hi
          cases l with
          | nil => simp at hi
          | cons b l => simp
      | succ i =>
          intro hi
          simpa only [List.getElem!_cons_succ, List.set_cons_succ] using
            congrArg (List.cons a) (ih i (by simpa using hi))

private theorem shiftHead_restore_eq_swp
    (a : Array T) (tmp : T) (i : ℕ) (hi : i + 1 < a.size) :
    (a.set! i a[i + 1]!).set! (i + 1) tmp =
      swp (a.set! i tmp) i (i + 1) := by
  apply Array.toList_inj.mp
  unfold swp
  simp only [Array.set!, Array.toList_setIfInBounds]
  rw [show a[i + 1]! = a.toList[i + 1]! by simp [hi]]
  have hreadi :
      (a.setIfInBounds i tmp)[i]! = tmp := by
    simp [Array.setIfInBounds, show i < a.size by omega]
  have hreadsucc :
      (a.setIfInBounds i tmp)[i + 1]! = a.toList[i + 1]! := by
    have hibase : i < a.size := by omega
    rw [show a.setIfInBounds i tmp = a.set i tmp hibase by
      simp [Array.setIfInBounds, hibase]]
    simp [hi]
  rw [hreadi, hreadsucc]
  exact list_shiftHead_restore tmp a.toList i (by simpa using hi)

private theorem shiftHead_loop_perm
    (tmp : T) (isLess : T → T → Bool) :
    ∀ (start count : ℕ) (a original : Array T),
      0 < start →
      start + count ≤ a.size →
      List.Perm (a.set! (start - 1) tmp).toList original.toList →
      let output : Array T := Id.run do
        pure PUnit.unit
        pure PUnit.unit
        let r ← forIn (List.range' start count)
          (⟨start - 1, a⟩ : MProd ℕ (Array T))
          fun i (r : MProd ℕ (Array T)) =>
            if !isLess (r.snd[i]!) tmp then
              pure (.done ⟨r.fst, r.snd⟩)
            else do
              pure PUnit.unit
              pure PUnit.unit
              pure (.yield ⟨i, r.snd.set! (i - 1) (r.snd[i]!)⟩)
        pure (r.snd.set! r.fst tmp)
      List.Perm output.toList original.toList := by
  intro start count
  induction count generalizing start with
  | zero =>
      intro a original hstart hfit hperm
      simpa using hperm
  | succ count ih =>
      intro a original hstart hfit hperm
      rw [List.range'_succ]
      simp only [List.forIn_cons]
      split
      · simpa using hperm
      ·
        apply ih (start + 1)
          (a.set! (start - 1) a[start]!) original
        · omega
        · simpa [Array.set!] using (show start + 1 + count ≤ a.size by
            omega)
        ·
          simp only [Nat.add_sub_cancel]
          have hslt : start < a.size := by omega
          have hprev : start - 1 + 1 = start := by omega
          have hstep :
              (a.set! (start - 1) a[start]!).set! start tmp =
                swp (a.set! (start - 1) tmp) (start - 1) start := by
            simpa only [hprev] using
              shiftHead_restore_eq_swp a tmp (start - 1)
                (hprev ▸ hslt)
          rw [hstep]
          have hleft :
              start - 1 < (a.set! (start - 1) tmp).size := by
            simpa [Array.set!] using (show start - 1 < a.size by omega)
          have hright :
              start < (a.set! (start - 1) tmp).size := by
            simpa [Array.set!] using (show start < a.size by omega)
          exact (swp_perm (a.set! (start - 1) tmp)
            (start - 1) start hleft hright).trans hperm

theorem shiftHead_perm (v : Array T) (isLess : T → T → Bool) :
    List.Perm (shiftHead v isLess).toList v.toList := by
  simp only [shiftHead]
  split
  · simp
  split
  · simp
  ·
    have hone : 1 < v.size := by omega
    have hfit : 2 + (v.size - 2) ≤ v.size := by omega
    have hinit :
        List.Perm ((v.set! 0 v[1]!).set! 1 v[0]!).toList
          v.toList := by
      rw [shiftHead_restore_eq_swp v v[0]! 0 (by simpa using hone)]
      have hp := swp_perm (v.set! 0 v[0]!) 0 1
        (by simpa [Array.set!] using (show 0 < v.size by omega))
        (by simpa [Array.set!] using hone)
      have hself : (v.set! 0 v[0]!).toList = v.toList := by
        simp only [Array.set!, Array.toList_setIfInBounds]
        rw [show v[0]! = v.toList[0]! by simp [show 0 < v.size by omega]]
        exact list_set_self v.toList 0
      exact hp.trans (hself ▸ List.Perm.refl v.toList)
    have hloop := shiftHead_loop_perm v[0]! isLess
      2 (v.size - 2) (v.set! 0 v[1]!) v
      (by omega) (by simpa [Array.set!] using hfit) hinit
    simpa using hloop

omit [Inhabited T] in
private theorem array_size_eq_of_perm {left right : Array T}
    (hperm : List.Perm left.toList right.toList) :
    left.size = right.size := by
  simpa using hperm.length_eq

private theorem insertion_step_perm
    (v : Array T) (isLess : T → T → Bool) (i : ℕ)
    (hi : i < v.size) :
    List.Perm
      (overwrite v 0
        (shiftTail (v.extract 0 (i + 1)) isLess)).toList
      v.toList := by
  let pre := v.extract 0 (i + 1)
  let shifted := shiftTail pre isLess
  have hshift : List.Perm shifted.toList pre.toList :=
    shiftTail_perm pre isLess
  have hsize : shifted.size = pre.size :=
    array_size_eq_of_perm hshift
  have hprefix : pre.size = i + 1 := by
    simp [pre, hi]
  apply overwrite_perm_of_extract v 0 shifted
  · simp [hsize, hprefix]
    omega
  · simpa [shifted, pre, hsize, hprefix] using hshift

private theorem insertion_fold_perm
    (isLess : T → T → Bool) :
    ∀ (indices : List ℕ) (current original : Array T),
      (∀ i ∈ indices, i < original.size) →
      List.Perm current.toList original.toList →
      List.Perm
        (indices.foldl (fun a i =>
          overwrite a 0
            (shiftTail (a.extract 0 (i + 1)) isLess)) current).toList
        original.toList := by
  intro indices
  induction indices with
  | nil =>
      intro current original _ hperm
      simpa using hperm
  | cons i indices ih =>
      intro current original hindices hperm
      have hsize : current.size = original.size :=
        array_size_eq_of_perm hperm
      have hi : i < current.size := by
        rw [hsize]
        exact hindices i (by simp)
      have hstep := insertion_step_perm current isLess i hi
      simp only [List.foldl_cons]
      apply ih
      · intro j hj
        exact hindices j (by simp [hj])
      · exact hstep.trans hperm

theorem insertionSort_perm (v : Array T) (isLess : T → T → Bool) :
    List.Perm (insertionSort v isLess).toList v.toList := by
  simp [insertionSort]
  apply insertion_fold_perm isLess (List.range' 1 (v.size - 1)) v v
  · intro i hi
    simp only [List.mem_range'] at hi
    omega
  · exact List.Perm.refl _

private theorem insertion_range_sorted
    (key : T → ℕ) :
    ∀ (count start : ℕ) (current : Array T),
      start + count ≤ current.size →
      KeySorted key (current.toList.take start) →
      KeySorted key
        (((List.range' start count).foldl (fun array index =>
          overwrite array 0
            (shiftTail (array.extract 0 (index + 1)) (lessBy key)))
          current).toList.take (start + count)) := by
  intro count
  induction count with
  | zero =>
      intro start current _ hsorted
      simpa using hsorted
  | succ count inductionHypothesis =>
      intro start current hfit hsorted
      rw [List.range'_succ, List.foldl_cons]
      let prefixArray := current.extract 0 (start + 1)
      let shifted := shiftTail prefixArray (lessBy key)
      let next := overwrite current 0 shifted
      have hprefixSize : prefixArray.size = start + 1 := by
        simp [prefixArray]
        omega
      have hprefixSorted : KeySorted key
          (prefixArray.toList.take (prefixArray.size - 1)) := by
        simp only [prefixArray, Array.toList_extract,
          List.extract_eq_take_drop, List.drop_zero, hprefixSize]
        rw [show start + 1 - 1 = start by omega, List.take_take,
          Nat.min_eq_left (by omega)]
        exact hsorted
      have hshiftedSorted : KeySorted key shifted.toList :=
        shiftTail_sorted prefixArray key hprefixSorted
      have hshiftedSize : shifted.size = prefixArray.size := by
        have hperm := shiftTail_perm prefixArray (lessBy key)
        simpa using hperm.length_eq
      have hnextSize : next.size = current.size := by
        simp [next, overwrite_size]
      have hnextPrefix :
          KeySorted key (next.toList.take (start + 1)) := by
        have hoverwrite := overwrite_toList current 0 shifted (by
          simp [hshiftedSize, hprefixSize]
          omega)
        simp only [List.take_zero, List.nil_append, Nat.zero_add] at hoverwrite
        rw [hoverwrite]
        rw [List.take_append_of_le_length]
        · have hlength : shifted.toList.length = start + 1 := by
            simp [hshiftedSize, hprefixSize]
          rw [← hlength, List.take_length]
          exact hshiftedSorted
        · simp [hshiftedSize, hprefixSize]
      have hresult := inductionHypothesis (start + 1) next
        (by simp [hnextSize]; omega) hnextPrefix
      unfold next shifted prefixArray at hresult
      rw [show start + (count + 1) = start + 1 + count by omega]
      exact hresult

/-- The legacy insertion-sort implementation orders its output by the supplied key. -/
theorem insertionSort_sorted (array : Array T) (key : T → ℕ) :
    KeySorted key (insertionSort array (lessBy key)).toList := by
  by_cases hempty : array.size = 0
  · have hnil : array.toList = [] := by
      apply List.eq_nil_of_length_eq_zero
      simpa using hempty
    have hresult : insertionSort array (lessBy key) = array := by
      simp [insertionSort, hempty]
    rw [hresult, hnil]
    exact KeySorted.nil key
  · have hprefix : KeySorted key (array.toList.take 1) := by
      rw [KeySorted, List.sortedLE_iff_pairwise,
        List.pairwise_map, List.pairwise_iff_get]
      intro left right horder
      have hleft := left.isLt
      have hright := right.isLt
      simp only [List.length_take] at hleft hright
      omega
    have hsorted := insertion_range_sorted key (array.size - 1) 1 array
      (by omega) hprefix
    rw [show 1 + (array.size - 1) = array.size by omega] at hsorted
    have hlength :
        (insertionSort array (lessBy key)).toList.length = array.size := by
      have hperm := insertionSort_perm array (lessBy key)
      simpa using hperm.length_eq
    have hfold :
        (List.range' 1 (array.size - 1)).foldl (fun current index =>
          overwrite current 0
            (shiftTail (current.extract 0 (index + 1)) (lessBy key))) array =
          insertionSort array (lessBy key) := by
      simp [insertionSort]
    rw [hfold, ← hlength, List.take_length] at hsorted
    exact hsorted

private theorem siftDown_loop_perm
    (isLess : T → T → Bool) :
    ∀ (indices : List ℕ) (node : ℕ) (a original : Array T),
      node < a.size →
      List.Perm a.toList original.toList →
      let result : MProd ℕ (Array T) := Id.run <|
        forIn indices (⟨node, a⟩ : MProd ℕ (Array T))
          fun _ (r : MProd ℕ (Array T)) =>
            let left := 2 * r.fst + 1
            let right := 2 * r.fst + 2
            let greater :=
              if right < r.snd.size &&
                  isLess (r.snd[left]!) (r.snd[right]!) then
                right
              else left
            if greater ≥ r.snd.size ||
                !isLess (r.snd[r.fst]!) (r.snd[greater]!) then
              pure (.done ⟨r.fst, r.snd⟩)
            else do
              pure PUnit.unit
              pure PUnit.unit
              pure (.yield ⟨greater,
                swp r.snd r.fst greater⟩)
      result.fst < result.snd.size ∧
        List.Perm result.snd.toList original.toList := by
  intro indices
  induction indices with
  | nil =>
      intro node a original hnode hperm
      exact ⟨hnode, hperm⟩
  | cons index indices ih =>
      intro node a original hnode hperm
      simp only [List.forIn_cons]
      split
      · split
        · exact ⟨hnode, hperm⟩
        ·
          apply ih
          · simp only [Bool.and_eq_true, Bool.or_eq_true,
              decide_eq_true_eq] at *
            have hright : 2 * node + 2 < a.size := by omega
            simpa [swp, Array.set!] using hright
          ·
            have hright : 2 * node + 2 < a.size := by
              simp only [Bool.and_eq_true, Bool.or_eq_true,
                decide_eq_true_eq] at *
              omega
            exact (swp_perm a node (2 * node + 2)
              hnode hright).trans hperm
      ·
        split
        · exact ⟨hnode, hperm⟩
        ·
          apply ih
          ·
            simp only [Bool.or_eq_true, decide_eq_true_eq] at *
            have hleft : 2 * node + 1 < a.size := by omega
            simpa [swp, Array.set!] using hleft
          ·
            have hleft : 2 * node + 1 < a.size := by
              simp only [Bool.or_eq_true, decide_eq_true_eq] at *
              omega
            exact (swp_perm a node (2 * node + 1)
              hnode hleft).trans hperm

theorem siftDown_perm (v : Array T) (isLess : T → T → Bool)
    (node : ℕ) (hnode : node < v.size) :
    List.Perm (siftDown v isLess node).toList v.toList := by
  simp [siftDown]
  have hloop := siftDown_loop_perm isLess
    (List.range' 0 (v.size + 1)) node v v
    hnode (List.Perm.refl _)
  simpa using hloop.2

private theorem siftDown_fold_perm
    (isLess : T → T → Bool) :
    ∀ (indices : List ℕ) (current original : Array T),
      (∀ i ∈ indices, i < original.size) →
      List.Perm current.toList original.toList →
      List.Perm
        (indices.foldl (fun a i => siftDown a isLess i)
          current).toList
        original.toList := by
  intro indices
  induction indices with
  | nil =>
      intro current original _ hperm
      simpa using hperm
  | cons i indices ih =>
      intro current original hindices hperm
      have hsize : current.size = original.size :=
        array_size_eq_of_perm hperm
      have hi : i < current.size := by
        rw [hsize]
        exact hindices i (by simp)
      have hstep := siftDown_perm current isLess i hi
      simp only [List.foldl_cons]
      apply ih
      · intro j hj
        exact hindices j (by simp [hj])
      · exact hstep.trans hperm

private theorem heapsort_extract_step_perm
    (v : Array T) (isLess : T → T → Bool) (i : ℕ)
    (hi : i < v.size) (hone : 1 ≤ i) :
    List.Perm
      (overwrite (swp v 0 i) 0
        (siftDown ((swp v 0 i).extract 0 i) isLess 0)).toList
      v.toList := by
  have hzero : 0 < v.size := by omega
  have hswap : List.Perm (swp v 0 i).toList v.toList :=
    swp_perm v 0 i hzero hi
  let swapped := swp v 0 i
  let pre := swapped.extract 0 i
  let sifted := siftDown pre isLess 0
  have hswappedSize : swapped.size = v.size :=
    array_size_eq_of_perm hswap
  have hpreSize : pre.size = i := by
    simp [pre, swapped, swp, Array.set!, hi]
    omega
  have hsift : List.Perm sifted.toList pre.toList := by
    apply siftDown_perm pre isLess 0
    simp [hpreSize]
    omega
  have hsiftSize : sifted.size = pre.size :=
    array_size_eq_of_perm hsift
  have hover : List.Perm (overwrite swapped 0 sifted).toList
      swapped.toList := by
    apply overwrite_perm_of_extract swapped 0 sifted
    · simp [hsiftSize, hpreSize, hswappedSize]
      omega
    · simpa [sifted, pre, hsiftSize, hpreSize] using hsift
  exact hover.trans hswap

private theorem heapsort_extract_fold_perm
    (isLess : T → T → Bool) :
    ∀ (indices : List ℕ) (current original : Array T),
      (∀ i ∈ indices, i < original.size) →
      List.Perm current.toList original.toList →
      List.Perm
        (indices.foldl (fun a i =>
          if i ≥ 1 then
            overwrite (swp a 0 i) 0
              (siftDown ((swp a 0 i).extract 0 i) isLess 0)
          else a) current).toList
        original.toList := by
  intro indices
  induction indices with
  | nil =>
      intro current original _ hperm
      simpa using hperm
  | cons i indices ih =>
      intro current original hindices hperm
      have hsize : current.size = original.size :=
        array_size_eq_of_perm hperm
      simp only [List.foldl_cons]
      split
      ·
        have hi : i < current.size := by
          rw [hsize]
          exact hindices i (by simp)
        have hstep := heapsort_extract_step_perm current isLess i hi
          (by omega)
        apply ih
        · intro j hj
          exact hindices j (by simp [hj])
        · exact hstep.trans hperm
      ·
        apply ih
        · intro j hj
          exact hindices j (by simp [hj])
        · exact hperm

private theorem heapsort_extract_forIn_perm
    (isLess : T → T → Bool) :
    ∀ (indices : List ℕ) (current original : Array T),
      (∀ i ∈ indices, i < original.size) →
      List.Perm current.toList original.toList →
      List.Perm
        (Id.run (forIn indices current fun i a =>
          if i ≥ 1 then
            pure (.yield (overwrite (swp a 0 i) 0
              (siftDown ((swp a 0 i).extract 0 i) isLess 0)))
          else pure (.yield a))).toList
        original.toList := by
  intro indices
  induction indices with
  | nil =>
      intro current original _ hperm
      simpa using hperm
  | cons i indices ih =>
      intro current original hindices hperm
      have hsize : current.size = original.size :=
        array_size_eq_of_perm hperm
      simp only [List.forIn_cons]
      split
      ·
        have hi : i < current.size := by
          rw [hsize]
          exact hindices i (by simp)
        have hstep := heapsort_extract_step_perm current isLess i hi
          (by omega)
        apply ih
        · intro j hj
          exact hindices j (by simp [hj])
        · exact hstep.trans hperm
      ·
        apply ih
        · intro j hj
          exact hindices j (by simp [hj])
        · exact hperm

theorem heapsort_perm (v : Array T) (isLess : T → T → Bool) :
    List.Perm (heapsort v isLess).toList v.toList := by
  simp [heapsort]
  let heapified :=
    List.foldr (fun i a => siftDown a isLess i)
      v (List.range (v.size / 2))
  have hheap : List.Perm heapified.toList v.toList := by
    have hfold := siftDown_fold_perm isLess
      (List.range (v.size / 2)).reverse v v
      (by
        intro i hi
        simp only [List.mem_reverse, List.mem_range] at hi
        omega)
      (List.Perm.refl _)
    simpa [heapified] using hfold
  have hextract := heapsort_extract_forIn_perm isLess
    (List.range v.size).reverse heapified v
    (by
      intro i hi
      simpa only [List.mem_reverse, List.mem_range] using hi)
    hheap
  simpa [heapified] using hextract

private theorem nextPow2_loop_bounds :
    ∀ (indices : List ℕ) (n p : ℕ),
      0 < p →
      p ≤ 2 * n →
      let result : ℕ := Id.run <|
        forIn indices p fun _ p =>
          if p ≥ n then pure (.done p)
          else pure (.yield (p * 2))
      0 < result ∧ result ≤ 2 * n := by
  intro indices
  induction indices with
  | nil =>
      intro n p hp hbound
      exact ⟨hp, hbound⟩
  | cons i indices ih =>
      intro n p hp hbound
      simp only [List.forIn_cons]
      split
      · exact ⟨hp, hbound⟩
      ·
        apply ih
        · omega
        · omega

private theorem nextPow2_bounds (n : ℕ) (hn : 0 < n) :
    0 < nextPow2 n ∧ nextPow2 n ≤ 2 * n := by
  have hloop := nextPow2_loop_bounds
    (List.range' 0 64) n 1 (by omega) (by omega)
  simpa [nextPow2] using hloop

private theorem adjusted_mod_lt (x len : ℕ) (hlen : 0 < len) :
    let raw := x % nextPow2 len
    (if raw ≥ len then raw - len else raw) < len := by
  have hb := nextPow2_bounds len hlen
  have hmod : x % nextPow2 len < nextPow2 len :=
    Nat.mod_lt x hb.1
  dsimp only
  split <;> omega

/-
private theorem breakPatterns_loop_perm :
    ∀ (indices : List ℕ) (len : ℕ)
      (random : UInt32) (a original : Array T),
      8 ≤ len →
      a.size = len →
      (∀ i ∈ indices, i < 3) →
      List.Perm a.toList original.toList →
      let result : MProd UInt32 (Array T) := Id.run <|
        forIn indices (⟨random, a⟩ : MProd UInt32 (Array T))
          fun i (r : MProd UInt32 (Array T)) =>
            let random₁ := r.fst ^^^ (r.fst <<< 13)
            let random₂ := random₁ ^^^ (random₁ >>> 17)
            let random₃ := random₂ ^^^ (random₂ <<< 5)
            let hi := random₃
            let random₄ := random₃ ^^^ (random₃ <<< 13)
            let random₅ := random₄ ^^^ (random₄ >>> 17)
            let random₆ := random₅ ^^^ (random₅ <<< 5)
            let lo := random₆
            let g : UInt64 :=
              (hi.toUInt64 <<< 32) ||| lo.toUInt64
            let raw : ℕ := g.toNat % nextPow2 len
            let other := if raw ≥ len then raw - len else raw
            pure (.yield ⟨random₆,
              swp r.snd (len / 4 * 2 - 1 + i) other⟩)
      List.Perm result.snd.toList original.toList := by
  intro indices
  induction indices with
  | nil =>
      intro len random a original hlen hsize hindices hperm
      simpa using hperm
  | cons i indices ih =>
      intro len random a original hlen hsize hindices hperm
      simp only [List.forIn_cons]
      apply ih
      · exact hlen
      ·
        have hpermStep := swp_perm a (len / 4 * 2 - 1 + i)
          (if
              (((((random ^^^ (random <<< 13)) ^^^
                    ((random ^^^ (random <<< 13)) >>> 17)) ^^^
                  (((random ^^^ (random <<< 13)) ^^^
                    ((random ^^^ (random <<< 13)) >>> 17)) <<< 5)) ^^^
                ((((random ^^^ (random <<< 13)) ^^^
                      ((random ^^^ (random <<< 13)) >>> 17)) ^^^
                    (((random ^^^ (random <<< 13)) ^^^
                      ((random ^^^ (random <<< 13)) >>> 17)) <<< 5)) <<< 13) ^^^
                (((((random ^^^ (random <<< 13)) ^^^
                        ((random ^^^ (random <<< 13)) >>> 17)) ^^^
                      (((random ^^^ (random <<< 13)) ^^^
                        ((random ^^^ (random <<< 13)) >>> 17)) <<< 5)) ^^^
                    ((((random ^^^ (random <<< 13)) ^^^
                          ((random ^^^ (random <<< 13)) >>> 17)) ^^^
                        (((random ^^^ (random <<< 13)) ^^^
                          ((random ^^^ (random <<< 13)) >>> 17)) <<< 5)) <<< 13)) >>> 17) ^^^
              (((((random ^^^ (random <<< 13)) ^^^
                        ((random ^^^ (random <<< 13)) >>> 17)) ^^^
                      (((random ^^^ (random <<< 13)) ^^^
                        ((random ^^^ (random <<< 13)) >>> 17)) <<< 5)) ^^^
                    ((((random ^^^ (random <<< 13)) ^^^
                          ((random ^^^ (random <<< 13)) >>> 17)) ^^^
                        (((random ^^^ (random <<< 13)) ^^^
                          ((random ^^^ (random <<< 13)) >>> 17)) <<< 5)) <<< 13) ^^^
                    (((((random ^^^ (random <<< 13)) ^^^
                            ((random ^^^ (random <<< 13)) >>> 17)) ^^^
                          (((random ^^^ (random <<< 13)) ^^^
                            ((random ^^^ (random <<< 13)) >>> 17)) <<< 5)) ^^^
                        ((((random ^^^ (random <<< 13)) ^^^
                              ((random ^^^ (random <<< 13)) >>> 17)) ^^^
                            (((random ^^^ (random <<< 13)) ^^^
                              ((random ^^^ (random <<< 13)) >>> 17)) <<< 5)) <<< 13)) >>> 17)) <<< 5)).toUInt64.toNat %
                nextPow2 len ≥ len then
            (((((random ^^^ (random <<< 13)) ^^^
                    ((random ^^^ (random <<< 13)) >>> 17)) ^^^
                  (((random ^^^ (random <<< 13)) ^^^
                    ((random ^^^ (random <<< 13)) >>> 17)) <<< 5)).toUInt64 <<< 32 |||
              (((((random ^^^ (random <<< 13)) ^^^
                        ((random ^^^ (random <<< 13)) >>> 17)) ^^^
                      (((random ^^^ (random <<< 13)) ^^^
                        ((random ^^^ (random <<< 13)) >>> 17)) <<< 5)) ^^^
                    ((((random ^^^ (random <<< 13)) ^^^
                          ((random ^^^ (random <<< 13)) >>> 17)) ^^^
                        (((random ^^^ (random <<< 13)) ^^^
                          ((random ^^^ (random <<< 13)) >>> 17)) <<< 5)) <<< 13) ^^^
                    (((((random ^^^ (random <<< 13)) ^^^
                            ((random ^^^ (random <<< 13)) >>> 17)) ^^^
                          (((random ^^^ (random <<< 13)) ^^^
                            ((random ^^^ (random <<< 13)) >>> 17)) <<< 5)) ^^^
                        ((((random ^^^ (random <<< 13)) ^^^
                              ((random ^^^ (random <<< 13)) >>> 17)) ^^^
                            (((random ^^^ (random <<< 13)) ^^^
                              ((random ^^^ (random <<< 13)) >>> 17)) <<< 5)) <<< 13)) >>> 17)) ^^^
                  (((((random ^^^ (random <<< 13)) ^^^
                            ((random ^^^ (random <<< 13)) >>> 17)) ^^^
                          (((random ^^^ (random <<< 13)) ^^^
                            ((random ^^^ (random <<< 13)) >>> 17)) <<< 5)) ^^^
                        ((((random ^^^ (random <<< 13)) ^^^
                              ((random ^^^ (random <<< 13)) >>> 17)) ^^^
                            (((random ^^^ (random <<< 13)) ^^^
                              ((random ^^^ (random <<< 13)) >>> 17)) <<< 5)) <<< 13) ^^^
                        (((((random ^^^ (random <<< 13)) ^^^
                                ((random ^^^ (random <<< 13)) >>> 17)) ^^^
                              (((random ^^^ (random <<< 13)) ^^^
                                ((random ^^^ (random <<< 13)) >>> 17)) <<< 5)) ^^^
                            ((((random ^^^ (random <<< 13)) ^^^
                                  ((random ^^^ (random <<< 13)) >>> 17)) ^^^
                                (((random ^^^ (random <<< 13)) ^^^
                                  ((random ^^^ (random <<< 13)) >>> 17)) <<< 5)) <<< 13)) >>> 17)) <<< 5)).toUInt64).toNat %
                nextPow2 len - len
          else
            (((((random ^^^ (random <<< 13)) ^^^
                    ((random ^^^ (random <<< 13)) >>> 17)) ^^^
                  (((random ^^^ (random <<< 13)) ^^^
                    ((random ^^^ (random <<< 13)) >>> 17)) <<< 5)).toUInt64 <<< 32 |||
              (((((random ^^^ (random <<< 13)) ^^^
                        ((random ^^^ (random <<< 13)) >>> 17)) ^^^
                      (((random ^^^ (random <<< 13)) ^^^
                        ((random ^^^ (random <<< 13)) >>> 17)) <<< 5)) ^^^
                    ((((random ^^^ (random <<< 13)) ^^^
                          ((random ^^^ (random <<< 13)) >>> 17)) ^^^
                        (((random ^^^ (random <<< 13)) ^^^
                          ((random ^^^ (random <<< 13)) >>> 17)) <<< 5)) <<< 13) ^^^
                    (((((random ^^^ (random <<< 13)) ^^^
                            ((random ^^^ (random <<< 13)) >>> 17)) ^^^
                          (((random ^^^ (random <<< 13)) ^^^
                            ((random ^^^ (random <<< 13)) >>> 17)) <<< 5)) ^^^
                        ((((random ^^^ (random <<< 13)) ^^^
                              ((random ^^^ (random <<< 13)) >>> 17)) ^^^
                            (((random ^^^ (random <<< 13)) ^^^
                              ((random ^^^ (random <<< 13)) >>> 17)) <<< 5)) <<< 13)) >>> 17)) ^^^
                  (((((random ^^^ (random <<< 13)) ^^^
                            ((random ^^^ (random <<< 13)) >>> 17)) ^^^
                          (((random ^^^ (random <<< 13)) ^^^
                            ((random ^^^ (random <<< 13)) >>> 17)) <<< 5)) ^^^
                        ((((random ^^^ (random <<< 13)) ^^^
                              ((random ^^^ (random <<< 13)) >>> 17)) ^^^
                            (((random ^^^ (random <<< 13)) ^^^
                              ((random ^^^ (random <<< 13)) >>> 17)) <<< 5)) <<< 13) ^^^
                        (((((random ^^^ (random <<< 13)) ^^^
                                ((random ^^^ (random <<< 13)) >>> 17)) ^^^
                              (((random ^^^ (random <<< 13)) ^^^
                                ((random ^^^ (random <<< 13)) >>> 17)) <<< 5)) ^^^
                            ((((random ^^^ (random <<< 13)) ^^^
                                  ((random ^^^ (random <<< 13)) >>> 17)) ^^^
                                (((random ^^^ (random <<< 13)) ^^^
                                  ((random ^^^ (random <<< 13)) >>> 17)) <<< 5)) <<< 13)) >>> 17)) <<< 5)).toUInt64).toNat %
              nextPow2 len)
          (by
            rw [hsize]
            have hi := hindices i (by simp)
            omega)
          (by
            rw [hsize]
            apply adjusted_mod_lt
            omega)
        exact array_size_eq_of_perm hpermStep
      · intro j hj
        exact hindices j (by simp [hj])
      ·
        apply (swp_perm a (len / 4 * 2 - 1 + i)
          _ (by
            rw [hsize]
            have hi := hindices i (by simp)
            omega) (by
            rw [hsize]
            apply adjusted_mod_lt
            omega)).trans hperm
-/

private def xorshift32 (random : UInt32) : UInt32 :=
  let random := random ^^^ (random <<< 13)
  let random := random ^^^ (random >>> 17)
  random ^^^ (random <<< 5)

private def breakNextRandom (random : UInt32) : UInt32 :=
  xorshift32 (xorshift32 random)

private def breakOther (random : UInt32) (len : ℕ) : ℕ :=
  let hi := xorshift32 random
  let lo := xorshift32 hi
  let g : UInt64 := (hi.toUInt64 <<< 32) ||| lo.toUInt64
  let raw := g.toNat % nextPow2 len
  if raw ≥ len then raw - len else raw

private def breakWord (random : UInt32) : ℕ :=
  let hi := xorshift32 random
  let lo := xorshift32 hi
  let g : UInt64 := (hi.toUInt64 <<< 32) ||| lo.toUInt64
  g.toNat

private theorem breakOther_lt (random : UInt32) (len : ℕ)
    (hlen : 0 < len) :
    breakOther random len < len := by
  unfold breakOther
  apply adjusted_mod_lt
  exact hlen

private theorem breakPatterns_loop_perm_clean :
    ∀ (indices : List ℕ) (len : ℕ)
      (random : UInt32) (a original : Array T),
      8 ≤ len →
      a.size = len →
      (∀ i ∈ indices, i < 3) →
      List.Perm a.toList original.toList →
      let result : MProd UInt32 (Array T) := Id.run <|
        forIn indices (⟨random, a⟩ : MProd UInt32 (Array T))
          fun i (r : MProd UInt32 (Array T)) =>
            pure (.yield ⟨breakNextRandom r.fst,
              swp r.snd (len / 4 * 2 - 1 + i)
                (breakOther r.fst len)⟩)
      List.Perm result.snd.toList original.toList := by
  intro indices
  induction indices with
  | nil =>
      intro len random a original hlen hsize hindices hperm
      simpa using hperm
  | cons i indices ih =>
      intro len random a original hlen hsize hindices hperm
      simp only [List.forIn_cons]
      apply ih
      · exact hlen
      ·
        have hstep := swp_perm a (len / 4 * 2 - 1 + i)
          (breakOther random len)
          (by
            rw [hsize]
            have hi := hindices i (by simp)
            omega)
          (by
            rw [hsize]
            exact breakOther_lt random len (by omega))
        exact (array_size_eq_of_perm hstep).trans hsize
      · intro j hj
        exact hindices j (by simp [hj])
      ·
        exact (swp_perm a (len / 4 * 2 - 1 + i)
          (breakOther random len)
          (by
            rw [hsize]
            have hi := hindices i (by simp)
            omega)
          (by
            rw [hsize]
            exact breakOther_lt random len (by omega))).trans hperm

private def breakChoice (random : UInt32) (len : ℕ) :
    MProd UInt32 ℕ :=
  let random := random ^^^ (random <<< 13)
  let random := random ^^^ (random >>> 17)
  let random := random ^^^ (random <<< 5)
  let hi := random
  let random := random ^^^ (random <<< 13)
  let random := random ^^^ (random >>> 17)
  let random := random ^^^ (random <<< 5)
  let lo := random
  let g : UInt64 := (hi.toUInt64 <<< 32) ||| lo.toUInt64
  let raw := g.toNat % nextPow2 len
  ⟨random, if raw ≥ len then raw - len else raw⟩

private theorem breakChoice_other_lt (random : UInt32) (len : ℕ)
    (hlen : 0 < len) :
    (breakChoice random len).snd < len := by
  unfold breakChoice
  apply adjusted_mod_lt
  exact hlen

private theorem breakPatterns_loop_perm_choice :
    ∀ (indices : List ℕ) (len : ℕ)
      (random : UInt32) (a original : Array T),
      8 ≤ len →
      a.size = len →
      (∀ i ∈ indices, i < 3) →
      List.Perm a.toList original.toList →
      let result : MProd UInt32 (Array T) := Id.run <|
        forIn indices (⟨random, a⟩ : MProd UInt32 (Array T))
          fun i (r : MProd UInt32 (Array T)) =>
            let choice := breakChoice r.fst len
            pure (.yield ⟨choice.fst,
              swp r.snd (len / 4 * 2 - 1 + i) choice.snd⟩)
      List.Perm result.snd.toList original.toList := by
  intro indices
  induction indices with
  | nil =>
      intro len random a original hlen hsize hindices hperm
      simpa using hperm
  | cons i indices ih =>
      intro len random a original hlen hsize hindices hperm
      simp only [List.forIn_cons]
      apply ih
      · exact hlen
      ·
        have hstep := swp_perm a (len / 4 * 2 - 1 + i)
          (breakChoice random len).snd
          (by
            rw [hsize]
            have hi := hindices i (by simp)
            omega)
          (by
            rw [hsize]
            exact breakChoice_other_lt random len (by omega))
        exact (array_size_eq_of_perm hstep).trans hsize
      · intro j hj
        exact hindices j (by simp [hj])
      ·
        exact (swp_perm a (len / 4 * 2 - 1 + i)
          (breakChoice random len).snd
          (by
            rw [hsize]
            have hi := hindices i (by simp)
            omega)
          (by
            rw [hsize]
            exact breakChoice_other_lt random len (by omega))).trans hperm

omit [Inhabited T] in
private theorem state_forIn_perm
    (indices : List ℕ)
    (step : ℕ → MProd UInt32 (Array T) →
      MProd UInt32 (Array T))
    (initial : MProd UInt32 (Array T)) (original : Array T)
    (hstep : ∀ i ∈ indices, ∀ r,
      List.Perm r.snd.toList original.toList →
      List.Perm (step i r).snd.toList original.toList)
    (hperm : List.Perm initial.snd.toList original.toList) :
    let result : MProd UInt32 (Array T) := Id.run <|
      forIn indices initial fun i r =>
        pure (.yield (step i r))
    List.Perm result.snd.toList original.toList := by
  induction indices generalizing initial with
  | nil =>
      simpa using hperm
  | cons i indices ih =>
      simp only [List.forIn_cons]
      apply ih
      · intro j hj r
        exact hstep j (by simp [hj]) r
      · exact hstep i (by simp) initial hperm

omit [Inhabited T] in
private theorem state_forIn_body_perm
    (indices : List ℕ)
    (body : ℕ → MProd UInt32 (Array T) →
      Id (ForInStep (MProd UInt32 (Array T))))
    (initial : MProd UInt32 (Array T)) (original : Array T)
    (hbody : ∀ i ∈ indices, ∀ r,
      List.Perm r.snd.toList original.toList →
      match body i r with
      | .done s => List.Perm s.snd.toList original.toList
      | .yield s => List.Perm s.snd.toList original.toList)
    (hperm : List.Perm initial.snd.toList original.toList) :
    let result : MProd UInt32 (Array T) := Id.run <|
      forIn indices initial body
    List.Perm result.snd.toList original.toList := by
  induction indices generalizing initial with
  | nil =>
      simpa using hperm
  | cons i indices ih =>
      rw [List.forIn_cons]
      generalize hb : body i initial = b
      cases b with
      | done s =>
          have hs := hbody i (by simp) initial hperm
          rw [hb] at hs
          exact hs
      | yield s =>
          apply ih
          · intro j hj r hr
            exact hbody j (by simp [hj]) r hr
          ·
            have hs := hbody i (by simp) initial hperm
            rw [hb] at hs
            exact hs

omit [Inhabited T] in
private theorem state_forIn_body_result_perm
    (indices : List ℕ)
    (body : ℕ → MProd UInt32 (Array T) →
      Id (ForInStep (MProd UInt32 (Array T))))
    (initial : MProd UInt32 (Array T)) (original : Array T)
    (hbody : ∀ i ∈ indices, ∀ r,
      List.Perm r.snd.toList original.toList →
      match body i r with
      | .done s => List.Perm s.snd.toList original.toList
      | .yield s => List.Perm s.snd.toList original.toList)
    (hperm : List.Perm initial.snd.toList original.toList) :
    List.Perm
      (Id.run do
        let r ← forIn indices initial body
        pure PUnit.unit
        pure r.snd).toList
      original.toList := by
  simpa using state_forIn_body_perm indices body initial original
    hbody hperm

private def breakPatternsStep (len modulus pos : ℕ) (i : ℕ)
    (r : MProd UInt32 (Array T)) : MProd UInt32 (Array T) :=
  let random := r.fst ^^^ (r.fst <<< 13)
  let random := random ^^^ (random >>> 17)
  let random := random ^^^ (random <<< 5)
  let hi := random
  let random := random ^^^ (random <<< 13)
  let random := random ^^^ (random >>> 17)
  let random := random ^^^ (random <<< 5)
  let lo := random
  let g : UInt64 := (hi.toUInt64 <<< 32) ||| lo.toUInt64
  let raw := g.toNat % modulus
  let other := if raw ≥ len then raw - len else raw
  ⟨random, swp r.snd (pos - 1 + i) other⟩

private theorem breakPatternsStep_perm (v : Array T) (i : ℕ)
    (hi : i < 3) (r : MProd UInt32 (Array T))
    (hlen : 8 ≤ v.size)
    (hr : List.Perm r.snd.toList v.toList) :
    List.Perm
      (breakPatternsStep v.size (nextPow2 v.size)
        (v.size / 4 * 2) i r).snd.toList v.toList := by
  have hrsize : r.snd.size = v.size :=
    array_size_eq_of_perm hr
  unfold breakPatternsStep
  exact (swp_perm r.snd (v.size / 4 * 2 - 1 + i) _
    (by rw [hrsize]; omega)
    (by rw [hrsize]; apply adjusted_mod_lt; omega)).trans hr

theorem breakPatterns_perm (v : Array T) :
    List.Perm (breakPatterns v).toList v.toList := by
  simp only [breakPatterns]
  split
  ·
    simp only [Std.Legacy.Range.forIn_eq_forIn_range']
    let body : ℕ → MProd UInt32 (Array T) →
        Id (ForInStep (MProd UInt32 (Array T))) :=
      fun i r => do
        let mut a := r.snd
        let mut random := r.fst
        random := random ^^^ (random <<< 13)
        random := random ^^^ (random >>> 17)
        random := random ^^^ (random <<< 5)
        let hi := random
        random := random ^^^ (random <<< 13)
        random := random ^^^ (random >>> 17)
        random := random ^^^ (random <<< 5)
        let lo := random
        let g : UInt64 := (hi.toUInt64 <<< 32) ||| lo.toUInt64
        let mut other : ℕ := g.toNat % nextPow2 v.size
        if other ≥ v.size then other := other - v.size
        a := swp a (v.size / 4 * 2 - 1 + i) other
        pure PUnit.unit
        pure (.yield ⟨random, a⟩)
    have hbody :
        ∀ i ∈ List.range' 0 3, ∀ r,
          List.Perm r.snd.toList v.toList →
          match body i r with
          | .done s => List.Perm s.snd.toList v.toList
          | .yield s => List.Perm s.snd.toList v.toList := by
      intro i hi r hr
      simp only [List.mem_range'] at hi
      have hrsize : r.snd.size = v.size :=
        array_size_eq_of_perm hr
      simp only [body]
      split_ifs with hother
      ·
        exact (swp_perm r.snd (v.size / 4 * 2 - 1 + i) _
          (by rw [hrsize]; omega)
          (by
            rw [hrsize]
            simpa only [breakWord, xorshift32, if_pos hother] using
              (adjusted_mod_lt (breakWord r.fst) v.size
                (by omega)))).trans hr
      ·
        exact (swp_perm r.snd (v.size / 4 * 2 - 1 + i) _
          (by rw [hrsize]; omega)
          (by
            rw [hrsize]
            simpa only [breakWord, xorshift32, if_neg hother] using
              (adjusted_mod_lt (breakWord r.fst) v.size
                (by omega)))).trans hr
    have hmain := state_forIn_body_result_perm
      (List.range' 0 3) body ⟨v.size.toUInt32, v⟩ v
      hbody (List.Perm.refl _)
    simpa only [body] using hmain
  · simp

private theorem partialInsertionMutation_perm
    (v0 : Array T) (isLess : T → T → Bool) (i : ℕ)
    (hi0 : 0 < i) (hi : i < v0.size) :
    let v := swp v0 (i - 1) i
    let v := overwrite v 0 (shiftTail (v.extract 0 i) isLess)
    let v := overwrite v i (shiftHead (v.extract i v.size) isLess)
    List.Perm v.toList v0.toList := by
  let v1 := swp v0 (i - 1) i
  have hp1 : List.Perm v1.toList v0.toList := by
    apply swp_perm
    · omega
    · exact hi
  have hv1size : v1.size = v0.size :=
    array_size_eq_of_perm hp1
  let sub1 := shiftTail (v1.extract 0 i) isLess
  have hsub1 :
      List.Perm sub1.toList (v1.extract 0 i).toList :=
    shiftTail_perm _ isLess
  have hsub1size : sub1.size = i := by
    have hs := array_size_eq_of_perm hsub1
    simp only [Array.size_extract] at hs
    omega
  have hp2 :
      List.Perm (overwrite v1 0 sub1).toList v1.toList := by
    apply overwrite_perm_of_extract
    · simp [hsub1size]
      omega
    · simpa [hsub1size] using hsub1
  let v2 := overwrite v1 0 sub1
  have hv2size : v2.size = v1.size :=
    array_size_eq_of_perm hp2
  have hi2 : i < v2.size := by omega
  let sub2 := shiftHead (v2.extract i v2.size) isLess
  have hsub2 :
      List.Perm sub2.toList (v2.extract i v2.size).toList :=
    shiftHead_perm _ isLess
  have hsub2size : sub2.size = v2.size - i := by
    have hs := array_size_eq_of_perm hsub2
    simp only [Array.size_extract] at hs
    omega
  have hp3 :
      List.Perm (overwrite v2 i sub2).toList v2.toList := by
    apply overwrite_perm_of_extract
    · omega
    ·
      have hend : i + sub2.size = v2.size := by omega
      simpa [hend] using hsub2
  exact hp3.trans (hp2.trans hp1)

private theorem list_forIn_invariant
    {S : Type} (indices : List ℕ)
    (body : ℕ → S → Id (ForInStep S))
    (Inv : S → Prop) (initial : S)
    (hbody : ∀ i ∈ indices, ∀ s s', Inv s →
      ((body i s).run = .done s' ∨
        (body i s).run = .yield s') → Inv s')
    (hinit : Inv initial) :
    Inv (Id.run <| forIn indices initial body) := by
  induction indices generalizing initial with
  | nil =>
      simpa using hinit
  | cons i indices ih =>
      rw [List.forIn_cons]
      generalize hb : body i initial = b
      cases b with
      | done s =>
          exact hbody i (by simp) initial s hinit
            (Or.inl (by simpa using congrArg Id.run hb))
      | yield s =>
          apply ih
          · intro j hj t t' ht hstep
            exact hbody j (by simp [hj]) t t' ht hstep
          ·
            exact hbody i (by simp) initial s hinit
              (Or.inr (by simpa using congrArg Id.run hb))

private theorem bounded_scan
    (indices : List ℕ) (len i0 : ℕ)
    (pred : ℕ → Bool)
    (hpred : ∀ i, pred i = true → i < len)
    (hi0 : 0 < i0) (hile : i0 ≤ len) :
    let result : ℕ := Id.run <|
      forIn indices i0 fun _ i =>
        if pred i then do
          pure PUnit.unit
          pure (.yield (i + 1))
        else pure (.done i)
    0 < result ∧ result ≤ len := by
  induction indices generalizing i0 with
  | nil =>
      exact ⟨hi0, hile⟩
  | cons x indices ih =>
      simp only [List.forIn_cons]
      split
      · apply ih
        · omega
        · have := hpred i0 (by assumption)
          omega
      · exact ⟨hi0, hile⟩

private theorem scan_le
    (indices : List ℕ) (bound i0 : ℕ)
    (pred : ℕ → Bool)
    (hpred : ∀ i, pred i = true → i < bound)
    (hile : i0 ≤ bound) :
    let result : ℕ := Id.run <|
      forIn indices i0 fun _ i =>
        if pred i then do
          pure PUnit.unit
          pure (.yield (i + 1))
        else pure (.done i)
    result ≤ bound := by
  induction indices generalizing i0 with
  | nil =>
      exact hile
  | cons x indices ih =>
      simp only [List.forIn_cons]
      split
      · apply ih
        have := hpred i0 (by assumption)
        omega
      · exact hile

private theorem scan_down_bounds
    (indices : List ℕ) (lower r0 : ℕ)
    (pred : ℕ → Bool)
    (hpred : ∀ r, pred r = true → lower < r)
    (hlower : lower ≤ r0) :
    let result : ℕ := Id.run <|
      forIn indices r0 fun _ r =>
        if pred r then do
          pure PUnit.unit
          pure (.yield (r - 1))
        else pure (.done r)
    lower ≤ result ∧ result ≤ r0 := by
  induction indices generalizing r0 with
  | nil =>
      exact ⟨hlower, Nat.le_refl _⟩
  | cons x indices ih =>
      simp only [List.forIn_cons]
      split
      ·
        have hlt := hpred r0 (by assumption)
        have hrest := ih (r0 - 1) (by omega)
        exact ⟨hrest.1,
          hrest.2.trans (Nat.sub_le r0 1)⟩
      · exact ⟨hlower, Nat.le_refl _⟩

theorem partialInsertionSort_perm (v : Array T)
    (isLess : T → T → Bool) :
    List.Perm (partialInsertionSort v isLess).2.toList v.toList := by
  simp only [partialInsertionSort,
    Std.Legacy.Range.forIn_eq_forIn_range',
    Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel,
    Nat.div_one]
  let body :
      ℕ → MProd ℕ (MProd (Option Bool) (Array T)) →
        Id (ForInStep
          (MProd ℕ (MProd (Option Bool) (Array T)))) :=
    fun _ r =>
      if r.snd.fst.isNone = true then do
        let i ←
          forIn (List.range' 0 (v.size + 1)) r.fst fun _ i =>
            if (decide (i < v.size) &&
                !isLess r.snd.snd[i]! r.snd.snd[i - 1]!) = true then do
              pure PUnit.unit
              pure (.yield (i + 1))
            else
              pure (.done i)
        if (i == v.size) = true then do
          pure PUnit.unit
          pure (.yield ⟨i, some true, r.snd.snd⟩)
        else if v.size < 50 then do
          pure PUnit.unit
          pure (.yield ⟨i, some false, r.snd.snd⟩)
        else do
          pure PUnit.unit
          pure (.yield
            ⟨i, r.snd.fst,
              overwrite
                (overwrite (swp r.snd.snd (i - 1) i) 0
                  (shiftTail
                    ((swp r.snd.snd (i - 1) i).extract 0 i)
                    isLess))
                i
                (shiftHead
                  ((overwrite (swp r.snd.snd (i - 1) i) 0
                    (shiftTail
                      ((swp r.snd.snd (i - 1) i).extract 0 i)
                      isLess)).extract i)
                  isLess)⟩)
      else do
        pure PUnit.unit
        pure (.yield ⟨r.fst, r.snd.fst, r.snd.snd⟩)
  let Inv :=
    fun r : MProd ℕ (MProd (Option Bool) (Array T)) =>
      List.Perm r.snd.snd.toList v.toList ∧
      (r.snd.fst.isNone = true → 50 ≤ v.size →
        0 < r.fst ∧ r.fst ≤ v.size)
  have hbody :
      ∀ x ∈ List.range' 0 5, ∀ r, Inv r →
        match (body x r).run with
        | .done r' => Inv r'
        | .yield r' => Inv r' := by
    intro x hx r hr
    by_cases hnone : r.snd.fst.isNone = true
    ·
      simp only [body, hnone, ↓reduceIte, Id.run_bind]
      generalize hscan :
        (Id.run <| forIn (List.range' 0 (v.size + 1)) r.fst
          fun _ i =>
            if (decide (i < v.size) &&
                !isLess r.snd.snd[i]! r.snd.snd[i - 1]!) = true then do
              pure PUnit.unit
              pure (.yield (i + 1))
            else
              pure (.done i)) = i
      by_cases heq : (i == v.size) = true
      · simp only [heq, ↓reduceIte, Inv]
        exact ⟨hr.1, by simp⟩
      · simp only [heq]
        by_cases hshort : v.size < 50
        · simp only [hshort, ↓reduceIte, Inv]
          exact ⟨hr.1, by simp⟩
        · simp only [hshort, ↓reduceIte, Inv]
          have hstart := hr.2 hnone (by omega)
          have hscanBounds := bounded_scan
            (List.range' 0 (v.size + 1)) v.size r.fst
            (fun j =>
              decide (j < v.size) &&
                !isLess r.snd.snd[j]! r.snd.snd[j - 1]!)
            (by
              intro j hj
              simp only [Bool.and_eq_true, decide_eq_true_eq] at hj
              exact hj.1)
            hstart.1 hstart.2
          rw [hscan] at hscanBounds
          have hilt : i < v.size := by
            have hne : i ≠ v.size := by
              intro hieq
              apply heq
              simp [hieq]
            omega
          have hrsize : r.snd.snd.size = v.size :=
            array_size_eq_of_perm hr.1
          have hilt' : i < r.snd.snd.size := by omega
          exact ⟨partialInsertionMutation_perm r.snd.snd isLess i
              hscanBounds.1 hilt' |>.trans hr.1,
            fun _ _ => hscanBounds⟩
    · simp only [body, hnone, Inv]
      exact hr
  have hinit : Inv ⟨1, none, v⟩ := by
    exact ⟨List.Perm.refl _, by simp; omega⟩
  have hloop := list_forIn_invariant
    (List.range' 0 5) body Inv ⟨1, none, v⟩
    (fun x hx r r' hr hstep => by
      have h := hbody x hx r hr
      rcases hstep with hstep | hstep
      · rw [hstep] at h
        exact h
      · rw [hstep] at h
        exact h)
    hinit
  simpa only [body, Inv] using hloop.1

private theorem KeySorted.take_succ
    (array : Array T) (key : T → ℕ) (index : ℕ)
    (hpositive : 0 < index) (hindex : index < array.size)
    (hsorted : KeySorted key (array.toList.take index))
    (hnext : key array[index - 1]! ≤ key array[index]!) :
    KeySorted key (array.toList.take (index + 1)) := by
  rw [List.take_succ_eq_append_getElem (by simpa using hindex)]
  rw [Array.getElem_toList hindex]
  rw [getElem!_pos array index hindex] at hnext
  apply KeySorted.append key _ _ hsorted (KeySorted.singleton key array[index])
  intro left hleft right hright
  simp only [List.mem_singleton] at hright
  subst right
  have hlength : (array.toList.take index).length = index := by
    simp only [List.length_take, Array.length_toList]
    omega
  have hprefixBound := KeySorted.keysLE_last key
    (array.toList.take index) hsorted (by omega)
  have hleftLast := hprefixBound left hleft
  have hlast : (array.toList.take index)[index - 1]! =
      array[index - 1]! := by
    rw [getElem!_pos _ _ (by rw [hlength]; omega),
      List.getElem_take]
    rw [Array.getElem_toList (by omega)]
    rw [getElem!_pos array (index - 1) (by omega)]
  rw [hlength, hlast] at hleftLast
  exact hleftLast.trans hnext

private theorem ascendingScan_sorted
    (indices : List ℕ) (array : Array T) (key : T → ℕ)
    (initial : ℕ) (hpositive : 0 < initial)
    (hbound : initial ≤ array.size)
    (hsorted : KeySorted key (array.toList.take initial)) :
    let result := Id.run <| forIn indices initial fun _ index =>
      if index < array.size &&
          !lessBy key array[index]! array[index - 1]! then do
        pure PUnit.unit
        pure (.yield (index + 1))
      else
        pure (.done index)
    0 < result ∧ result ≤ array.size ∧
      KeySorted key (array.toList.take result) := by
  induction indices generalizing initial with
  | nil => exact ⟨hpositive, hbound, hsorted⟩
  | cons _ indices inductionHypothesis =>
      simp only [List.forIn_cons]
      split
      next hstep =>
        simp only [Bool.and_eq_true, decide_eq_true_eq,
          Bool.not_eq_true'] at hstep
        have hnext : key array[initial - 1]! ≤ key array[initial]! := by
          rw [lessBy_eq_false_iff] at hstep
          exact hstep.2
        exact inductionHypothesis (initial + 1) (by omega) (by omega)
          (KeySorted.take_succ array key initial hpositive hstep.1
            hsorted hnext)
      next _ => exact ⟨hpositive, hbound, hsorted⟩

private theorem swp_toList_take_before
    (array : Array T) (left right stop : ℕ)
    (hleft : left < array.size) (hright : right < array.size)
    (hstopLeft : stop ≤ left) (hstopRight : stop ≤ right) :
    (swp array left right).toList.take stop =
      array.toList.take stop := by
  apply List.ext_getElem
  · simp only [List.length_take, Array.length_toList, swp_size]
  · intro index hindexLeft hindexRight
    rw [List.getElem_take, List.getElem_take]
    have hindex : index < array.size := by
      have := hindexRight
      simp only [List.length_take, Array.length_toList] at this
      omega
    have hindexStop : index < stop := by
      have := hindexRight
      simp only [List.length_take, Array.length_toList] at this
      omega
    rw [Array.getElem_toList (by simpa only [swp_size] using hindex),
      Array.getElem_toList hindex,
      ← getElem!_pos (swp array left right) index
        (by simpa only [swp_size] using hindex),
      ← getElem!_pos array index hindex,
      swp_get! array left right index hleft hright,
      getElem!_pos array index hindex,
      if_neg (by omega), if_neg (by omega)]

private theorem partialInsertionMutation_prefix_sorted
    (array : Array T) (key : T → ℕ) (index : ℕ)
    (hpositive : 0 < index) (hindex : index < array.size)
    (hsorted : KeySorted key (array.toList.take index)) :
    let swapped := swp array (index - 1) index
    let sortedPrefix := shiftTail (swapped.extract 0 index) (lessBy key)
    let prefixed := overwrite swapped 0 sortedPrefix
    let suffix := shiftHead (prefixed.extract index prefixed.size) (lessBy key)
    let output := overwrite prefixed index suffix
    KeySorted key (output.toList.take index) := by
  let swapped := swp array (index - 1) index
  let prefixSource := swapped.extract 0 index
  let sortedPrefix := shiftTail prefixSource (lessBy key)
  let prefixed := overwrite swapped 0 sortedPrefix
  let suffixSource := prefixed.extract index prefixed.size
  let suffix := shiftHead suffixSource (lessBy key)
  let output := overwrite prefixed index suffix
  show KeySorted key (output.toList.take index)
  have hswappedSize : swapped.size = array.size := swp_size _ _ _
  have hprefixSourceSize : prefixSource.size = index := by
    simp [prefixSource]
    omega
  have hbeforeSwap : swapped.toList.take (index - 1) =
      array.toList.take (index - 1) := by
    exact swp_toList_take_before array (index - 1) index (index - 1)
      (by omega) hindex (Nat.le_refl _) (by omega)
  have hbeforeSorted : KeySorted key
      (prefixSource.toList.take (prefixSource.size - 1)) := by
    have hsmaller := KeySorted.take key
      (array.toList.take index) (index - 1) hsorted
    have horiginal : KeySorted key (array.toList.take (index - 1)) := by
      rw [List.take_take,
        show min (index - 1) index = index - 1 by omega] at hsmaller
      exact hsmaller
    simp only [prefixSource, Array.toList_extract,
      List.extract_eq_take_drop, List.drop_zero, Nat.sub_zero,
      hprefixSourceSize, List.take_take]
    rw [show min (index - 1) index = index - 1 by omega]
    rw [hbeforeSwap]
    exact horiginal
  have hprefixSorted : KeySorted key sortedPrefix.toList :=
    shiftTail_sorted prefixSource key hbeforeSorted
  have hprefixPerm := shiftTail_perm prefixSource (lessBy key)
  have hprefixSize : sortedPrefix.size = index := by
    have := array_size_eq_of_perm hprefixPerm
    rw [hprefixSourceSize] at this
    exact this
  have hprefixedSize : prefixed.size = array.size := by
    simp [prefixed, overwrite_size, hswappedSize]
  have hprefixedPrefix :
      KeySorted key (prefixed.toList.take index) := by
    have hoverwrite := overwrite_toList swapped 0 sortedPrefix (by
      simp only [Nat.zero_add, hprefixSize]
      omega)
    simp only [List.take_zero, List.nil_append, Nat.zero_add] at hoverwrite
    have hlength : sortedPrefix.toList.length = index := by
      simp only [Array.length_toList, hprefixSize]
    rw [hoverwrite, List.take_append_of_le_length (by omega),
      ← hlength, List.take_length]
    exact hprefixSorted
  have hsuffixPerm := shiftHead_perm suffixSource (lessBy key)
  have hsuffixSourceSize : suffixSource.size = prefixed.size - index := by
    simp [suffixSource]
  have hsuffixSize : suffix.size = prefixed.size - index := by
    have := array_size_eq_of_perm hsuffixPerm
    rw [hsuffixSourceSize] at this
    exact this
  have houtputPrefix : output.toList.take index =
      prefixed.toList.take index := by
    have hoverwrite := overwrite_toList prefixed index suffix (by
      rw [hsuffixSize]
      omega)
    rw [hoverwrite]
    rw [List.append_assoc]
    rw [List.take_append_of_le_length (by
      simp only [List.length_take, Array.length_toList]
      omega)]
    rw [List.take_of_length_le (by
      simp only [List.length_take, Array.length_toList]
      omega)]
  rw [houtputPrefix]
  exact hprefixedPrefix

/-- A successful nearly-sorted fast path really has scanned a sorted prefix
through the end of the array. -/
theorem partialInsertionSort_sorted
    (array : Array T) (key : T → ℕ)
    (hsuccess :
      (partialInsertionSort array (lessBy key)).1 = true) :
    KeySorted key
      (partialInsertionSort array (lessBy key)).2.toList := by
  by_cases hempty : array.size = 0
  · exfalso
    norm_num [partialInsertionSort, hempty, List.range'_eq_map_range,
      List.range_succ, List.forIn_cons] at hsuccess
  · simp only [partialInsertionSort,
      Std.Legacy.Range.forIn_eq_forIn_range',
      Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel,
      Nat.div_one] at hsuccess ⊢
    let body :
        ℕ → MProd ℕ (MProd (Option Bool) (Array T)) →
          Id (ForInStep
            (MProd ℕ (MProd (Option Bool) (Array T)))) :=
      fun _ state =>
        if state.snd.fst.isNone = true then do
          let index ←
            forIn (List.range' 0 (array.size + 1)) state.fst fun _ index =>
              if (decide (index < array.size) &&
                  !lessBy key state.snd.snd[index]!
                    state.snd.snd[index - 1]!) = true then do
                pure PUnit.unit
                pure (.yield (index + 1))
              else
                pure (.done index)
          if (index == array.size) = true then do
            pure PUnit.unit
            pure (.yield ⟨index, some true, state.snd.snd⟩)
          else if array.size < 50 then do
            pure PUnit.unit
            pure (.yield ⟨index, some false, state.snd.snd⟩)
          else do
            pure PUnit.unit
            pure (.yield
              ⟨index, state.snd.fst,
                overwrite
                  (overwrite (swp state.snd.snd (index - 1) index) 0
                    (shiftTail
                      ((swp state.snd.snd (index - 1) index).extract 0 index)
                      (lessBy key)))
                  index
                  (shiftHead
                    ((overwrite (swp state.snd.snd (index - 1) index) 0
                      (shiftTail
                        ((swp state.snd.snd (index - 1) index).extract 0 index)
                        (lessBy key))).extract index)
                    (lessBy key))⟩)
        else do
          pure PUnit.unit
          pure (.yield
            ⟨state.fst, state.snd.fst, state.snd.snd⟩)
    let Inv :=
      fun state : MProd ℕ (MProd (Option Bool) (Array T)) =>
        state.snd.snd.size = array.size ∧
        (state.snd.fst.isNone = true →
          0 < state.fst ∧ state.fst ≤ array.size ∧
            KeySorted key (state.snd.snd.toList.take state.fst)) ∧
        (state.snd.fst = some true →
          KeySorted key state.snd.snd.toList)
    have hbody :
        ∀ outer ∈ List.range' 0 5, ∀ state, Inv state →
          match (body outer state).run with
          | .done next => Inv next
          | .yield next => Inv next := by
      intro outer houter state hinvariant
      by_cases hnone : state.snd.fst.isNone = true
      · simp only [body, hnone, ↓reduceIte, Id.run_bind]
        generalize hscan :
          (Id.run <| forIn (List.range' 0 (array.size + 1)) state.fst
            fun _ index =>
              if (decide (index < array.size) &&
                  !lessBy key state.snd.snd[index]!
                    state.snd.snd[index - 1]!) = true then do
                pure PUnit.unit
                pure (.yield (index + 1))
              else
                pure (.done index)) = index
        have hstart := hinvariant.2.1 hnone
        have hscanResult := ascendingScan_sorted
          (List.range' 0 (array.size + 1)) state.snd.snd key
          state.fst hstart.1 (by omega) hstart.2.2
        rw [hinvariant.1] at hscanResult
        rw [hscan] at hscanResult
        by_cases hend : (index == array.size) = true
        · simp only [hend, ↓reduceIte, Inv]
          have hindex : index = array.size := by simpa using hend
          refine ⟨hinvariant.1, by simp, ?_⟩
          intro _
          have hlength : state.snd.snd.toList.length = index := by
            simp only [Array.length_toList, hinvariant.1, hindex]
          have hsorted := hscanResult.2.2
          rw [← hlength, List.take_length] at hsorted
          exact hsorted
        · simp only [hend]
          by_cases hshort : array.size < 50
          · simp only [hshort, ↓reduceIte, Inv]
            exact ⟨hinvariant.1, by simp⟩
          · simp only [hshort, ↓reduceIte, Inv]
            have hindexLt : index < state.snd.snd.size := by
              have hindexNe : index ≠ array.size := by
                intro heq
                exact hend (by simp [heq])
              omega
            have hmutationPerm := partialInsertionMutation_perm
              state.snd.snd (lessBy key) index hscanResult.1 hindexLt
            have hmutationSize := array_size_eq_of_perm hmutationPerm
            refine ⟨hmutationSize.trans hinvariant.1,
              fun _ => ⟨hscanResult.1, hscanResult.2.1, ?_⟩, ?_⟩
            · exact partialInsertionMutation_prefix_sorted
                state.snd.snd key index hscanResult.1 hindexLt
                hscanResult.2.2
            · intro himpossible
              have : False := by
                rw [himpossible] at hnone
                simp at hnone
              exact this.elim
      · simp only [body, hnone, Inv]
        exact hinvariant
    have hinitial : Inv ⟨1, none, array⟩ := by
      dsimp only [Inv]
      refine ⟨rfl, ?_, by simp⟩
      intro _
      refine ⟨by omega, by omega, ?_⟩
      have hsingle : KeySorted key (array.toList.take 1) := by
        rw [KeySorted, List.sortedLE_iff_pairwise,
          List.pairwise_map, List.pairwise_iff_get]
        intro left right horder
        have hleft := left.isLt
        have hright := right.isLt
        simp only [List.length_take] at hleft hright
        omega
      exact hsingle
    have hloop := list_forIn_invariant
      (List.range' 0 5) body Inv ⟨1, none, array⟩
      (fun outer houter state next hinvariant hstep => by
        have h := hbody outer houter state hinvariant
        rcases hstep with hstep | hstep
        · rw [hstep] at h
          exact h
        · rw [hstep] at h
          exact h)
      hinitial
    let final := Id.run <| forIn (List.range' 0 5)
      ⟨1, none, array⟩ body
    change final.snd.fst.getD false = true at hsuccess
    change KeySorted key final.snd.snd.toList
    have hsuccessOption : final.snd.fst = some true := by
      cases hoption : final.snd.fst <;> simp_all
    have hfinalSorted := hloop.2.2 hsuccessOption
    exact hfinalSorted

omit [Inhabited T] in
theorem extract_split_toList (a : Array T) (i : ℕ) :
    (a.extract 0 i ++ a.extract i a.size).toList = a.toList := by
  simp only [Array.toList_append, Array.toList_extract,
    List.extract_eq_take_drop, List.drop_zero]
  rw [Nat.sub_zero]
  have hlen :
      a.size - i = (a.toList.drop i).length := by simp
  rw [hlen, List.take_length]
  rw [List.take_append_drop]

omit [Inhabited T] in
theorem reverse_perm (a : Array T) :
    List.Perm a.reverse.toList a.toList := by
  rw [Array.toList_reverse]
  exact List.reverse_perm _

theorem extract_pivot_split_toList (a : Array T) (i : ℕ)
    (hi : i < a.size) :
    (a.extract 0 i).toList ++ [a[i]!] ++
        (a.extract (i + 1) a.size).toList =
      a.toList := by
  simp only [Array.toList_extract, List.extract_eq_take_drop,
    List.drop_zero, Nat.sub_zero]
  have hget : a[i]! = a.toList[i] := by simp [hi]
  rw [hget]
  have htail :
      (a.toList.drop (i + 1)).take (a.size - (i + 1)) =
        a.toList.drop (i + 1) := by
    have hlen :
        (a.toList.drop (i + 1)).length = a.size - (i + 1) := by
      simp
    rw [← hlen, List.take_length]
  rw [htail, List.take_concat_get' _ _ (by simpa using hi),
    List.take_append_drop]

def PartitionInBlocksPermContract : Prop :=
  ∀ (v : Array T) (pivot : T) (isLess : T → T → Bool),
    let result := partitionInBlocks v pivot isLess
    result.1 ≤ v.size ∧ List.Perm result.2.toList v.toList

theorem partitionInBlocks_perm_contract :
    PartitionInBlocksPermContract (T := T) :=
  partitionInBlocks_contract

private theorem partitionP_mutations_perm
    (hblocks : PartitionInBlocksPermContract (T := T))
    (v0 : Array T) (pivotIdx l r : ℕ)
    (isLess : T → T → Bool)
    (hpivot : pivotIdx < v0.size)
    (hlr : l ≤ r) (hr : r < v0.size) :
    let v1 := swp v0 0 pivotIdx
    let block := partitionInBlocks
      (v1.extract (1 + l) (1 + r)) v1[0]! isLess
    let v2 := overwrite v1 (1 + l) block.2
    let mid := l + block.1
    List.Perm (swp v2 0 mid).toList v0.toList := by
  let v1 := swp v0 0 pivotIdx
  have hp1 : List.Perm v1.toList v0.toList := by
    apply swp_perm
    · omega
    · exact hpivot
  have hv1size : v1.size = v0.size :=
    array_size_eq_of_perm hp1
  let source := v1.extract (1 + l) (1 + r)
  let block := partitionInBlocks source v1[0]! isLess
  have hb := hblocks source v1[0]! isLess
  have hsourceSize : source.size = r - l := by
    simp only [source, Array.size_extract]
    omega
  have hblockSize : block.2.size = source.size :=
    array_size_eq_of_perm hb.2
  let v2 := overwrite v1 (1 + l) block.2
  have hp2 : List.Perm v2.toList v1.toList := by
    apply overwrite_perm_of_extract
    · omega
    ·
      have hend : 1 + l + block.2.size = 1 + r := by omega
      simpa [source, hend] using hb.2
  have hv2size : v2.size = v1.size :=
    array_size_eq_of_perm hp2
  have hmid : l + block.1 < v2.size := by
    have hcount := hb.1
    change block.1 ≤ source.size at hcount
    omega
  exact (swp_perm v2 0 (l + block.1)
    (by omega) hmid).trans (hp2.trans hp1)

private theorem partitionP_scan_bounds
    (a : Array T) (isLess : T → T → Bool)
    (hsize : 0 < a.size) :
    let l := Id.run <| forIn (List.range' 0 a.size) 0 fun _ l =>
      if (decide (l < a.size - 1) &&
          isLess a[1 + l]! a[0]!) = true then do
        pure PUnit.unit
        pure (.yield (l + 1))
      else
        pure (.done l)
    let r := Id.run <|
      forIn (List.range' 0 a.size) (a.size - 1) fun _ r =>
        if (decide (l < r) &&
            !isLess a[1 + (r - 1)]! a[0]!) = true then do
          pure PUnit.unit
          pure (.yield (r - 1))
        else
          pure (.done r)
    l ≤ r ∧ r < a.size := by
  let l := Id.run <| forIn (List.range' 0 a.size) 0 fun _ l =>
    if (decide (l < a.size - 1) &&
        isLess a[1 + l]! a[0]!) = true then do
      pure PUnit.unit
      pure (.yield (l + 1))
    else
      pure (.done l)
  have hl : l ≤ a.size - 1 := by
    exact scan_le (List.range' 0 a.size)
      (a.size - 1) 0
      (fun l =>
        decide (l < a.size - 1) &&
          isLess a[1 + l]! a[0]!)
      (by
        intro j hj
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hj
        exact hj.1)
      (by omega)
  let r := Id.run <|
    forIn (List.range' 0 a.size) (a.size - 1) fun _ r =>
      if (decide (l < r) &&
          !isLess a[1 + (r - 1)]! a[0]!) = true then do
        pure PUnit.unit
        pure (.yield (r - 1))
      else
        pure (.done r)
  have hrange : l ≤ r ∧ r ≤ a.size - 1 := by
    exact scan_down_bounds (List.range' 0 a.size)
      l (a.size - 1)
      (fun r =>
        decide (l < r) &&
          !isLess a[1 + (r - 1)]! a[0]!)
      (by
        intro j hj
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hj
        exact hj.1)
      hl
  have hout : l ≤ r ∧ r < a.size :=
    ⟨hrange.1, hrange.2.trans_lt (by omega)⟩
  simpa only [l, r] using hout

theorem partitionP_perm_of_blocks_contract
    (hblocks : PartitionInBlocksPermContract (T := T))
    (v : Array T) (pivotIdx : ℕ)
    (isLess : T → T → Bool)
    (hpivot : pivotIdx < v.size) :
    List.Perm (partitionP v pivotIdx isLess).2.toList v.toList := by
  simp only [partitionP,
    Std.Legacy.Range.forIn_eq_forIn_range',
    Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel,
    Nat.div_one, Id.run_bind]
  generalize hscanL :
    (Id.run <| forIn
      (List.range' 0 (swp v 0 pivotIdx).size) 0 fun _ l =>
      if (decide (l < (swp v 0 pivotIdx).size - 1) &&
          isLess
            (swp v 0 pivotIdx)[1 + l]!
            (swp v 0 pivotIdx)[0]!) = true then do
        pure PUnit.unit
        pure (.yield (l + 1))
      else
        pure (.done l)) = l
  generalize hscanR :
    (Id.run <| forIn
      (List.range' 0 (swp v 0 pivotIdx).size)
      ((swp v 0 pivotIdx).size - 1)
      fun _ r =>
        if (decide (l < r) &&
            !isLess
              (swp v 0 pivotIdx)[1 + (r - 1)]!
              (swp v 0 pivotIdx)[0]!) = true then do
          pure PUnit.unit
          pure (.yield (r - 1))
        else
          pure (.done r)) = r
  have hp1 := swp_perm v 0 pivotIdx (by omega) hpivot
  have hv1size :
      (swp v 0 pivotIdx).size = v.size :=
    array_size_eq_of_perm hp1
  have hrange := partitionP_scan_bounds
    (swp v 0 pivotIdx) isLess (by omega)
  dsimp only at hrange
  rw [hscanL, hscanR] at hrange
  generalize hblock :
    partitionInBlocks
      ((swp v 0 pivotIdx).extract (1 + l) (1 + r))
      (swp v 0 pivotIdx)[0]! isLess = block
  have hr : r < v.size := by
    rw [← hv1size]
    exact hrange.2
  have hmut := partitionP_mutations_perm
    hblocks v pivotIdx l r isLess hpivot hrange.1 hr
  dsimp only at hmut
  rw [hblock] at hmut
  exact hmut

/- The remaining end-to-end proof can be cleanly factored through these
helper contracts.  This theorem is intentionally left below the concrete
primitive milestones while the loop contracts are established. -/
private def scanLeft :
    List ℕ → ℕ → ℕ → T → Array T →
      (T → T → Bool) → ℕ
  | [], left, _, _, _, _ => left
  | _ :: indices, left, right, pivot, array, isLess =>
      if left < right && !isLess pivot (array[1 + left]!) then
        scanLeft indices (left + 1) right pivot array isLess
      else
        left

private def scanRight :
    List ℕ → ℕ → ℕ → T → Array T →
      (T → T → Bool) → ℕ
  | [], _, right, _, _, _ => right
  | _ :: indices, left, right, pivot, array, isLess =>
      if left < right && isLess pivot (array[1 + (right - 1)]!) then
        scanRight indices left (right - 1) pivot array isLess
      else
        right

/-- Reversing and complementing a strict comparison turns the scans used by
`partitionEqual` into the two scans used by `partitionP`. -/
private def dualLess (isLess : T → T → Bool) (left right : T) : Bool :=
  !isLess right left

private theorem scanLeft_lt
    (indices : List ℕ) (left right bound : ℕ)
    (pivot : T) (array : Array T)
    (isLess : T → T → Bool)
    (hleft : left < bound) (hright : right < bound) :
    scanLeft indices left right pivot array isLess < bound := by
  induction indices generalizing left with
  | nil =>
      exact hleft
  | cons index indices ih =>
      simp only [scanLeft]
      split
      · exact ih (left + 1) (by
          simp only [Bool.and_eq_true, decide_eq_true_eq] at *
          omega)
      · exact hleft

private theorem scanRight_le
    (indices : List ℕ) (left right : ℕ)
    (pivot : T) (array : Array T)
    (isLess : T → T → Bool) :
    scanRight indices left right pivot array isLess ≤ right := by
  induction indices generalizing right with
  | nil =>
      exact Nat.le_refl _
  | cons index indices ih =>
      simp only [scanRight]
      split
      · exact (ih (right - 1)).trans (Nat.sub_le right 1)
      · exact Nat.le_refl _

private theorem scanLeft_le
    (indices : List ℕ) (left right : ℕ)
    (pivot : T) (array : Array T)
    (isLess : T → T → Bool) (hle : left ≤ right) :
    scanLeft indices left right pivot array isLess ≤ right := by
  induction indices generalizing left with
  | nil => exact hle
  | cons index indices inductionHypothesis =>
      simp only [scanLeft]
      split
      · apply inductionHypothesis
        simp only [Bool.and_eq_true, decide_eq_true_eq] at *
        omega
      · exact hle

private theorem scanLeft_ge
    (indices : List ℕ) (left right : ℕ)
    (pivot : T) (array : Array T)
    (isLess : T → T → Bool) :
    left ≤ scanLeft indices left right pivot array isLess := by
  induction indices generalizing left with
  | nil => exact Nat.le_refl _
  | cons index indices inductionHypothesis =>
      simp only [scanLeft]
      split
      · exact Nat.le_add_right left 1 |>.trans (inductionHypothesis (left + 1))
      · exact Nat.le_refl _

private theorem scanRight_ge
    (indices : List ℕ) (left right : ℕ)
    (pivot : T) (array : Array T)
    (isLess : T → T → Bool) (hle : left ≤ right) :
    left ≤ scanRight indices left right pivot array isLess := by
  induction indices generalizing right with
  | nil => exact hle
  | cons index indices inductionHypothesis =>
      simp only [scanRight]
      split
      · apply inductionHypothesis
        simp only [Bool.and_eq_true, decide_eq_true_eq] at *
        omega
      · exact hle

private theorem scanLeft_rangeAll
    (indices : List ℕ) (left right : ℕ)
    (pivot : T) (array : Array T)
    (isLess : T → T → Bool) :
    RangeAll array (1 + left)
      (1 + scanLeft indices left right pivot array isLess)
      (fun item => isLess pivot item = false) := by
  induction indices generalizing left with
  | nil => exact RangeAll.empty array (1 + left) _
  | cons index indices inductionHypothesis =>
      simp only [scanLeft]
      split
      next hstep =>
        have hless : isLess pivot array[1 + left]! = false := by
          simp only [Bool.and_eq_true, decide_eq_true_eq,
            Bool.not_eq_true'] at hstep
          exact hstep.2
        have hrest := inductionHypothesis (left + 1)
        intro position hpositionStart hpositionStop
        by_cases hfirst : position = 1 + left
        · simpa [hfirst] using hless
        · apply hrest position <;> omega
      next _ => exact RangeAll.empty array (1 + left) _

private theorem scanRight_rangeAll
    (indices : List ℕ) (left right : ℕ)
    (pivot : T) (array : Array T)
    (isLess : T → T → Bool) :
    RangeAll array (1 + scanRight indices left right pivot array isLess)
      (1 + right) (fun item => isLess pivot item = true) := by
  induction indices generalizing right with
  | nil => exact RangeAll.empty array (1 + right) _
  | cons index indices inductionHypothesis =>
      simp only [scanRight]
      split
      next hstep =>
        have hless : isLess pivot array[1 + (right - 1)]! = true := by
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hstep
          exact hstep.2
        have hrest := inductionHypothesis (right - 1)
        intro position hpositionStart hpositionStop
        by_cases hlast : position = right
        · simpa [hlast, show 1 + (right - 1) = right by
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hstep
            omega] using hless
        · apply hrest position <;> omega
      next _ => exact RangeAll.empty array (1 + right) _

private theorem scanLeft_stops_on_greater
    (indices : List ℕ) (left right : ℕ)
    (pivot : T) (array : Array T)
    (isLess : T → T → Bool)
    (hcapacity : right - left ≤ indices.length)
    (hresult : scanLeft indices left right pivot array isLess < right) :
    isLess pivot
      array[1 + scanLeft indices left right pivot array isLess]! = true := by
  induction indices generalizing left with
  | nil =>
      simp only [scanLeft, List.length_nil] at hcapacity hresult
      omega
  | cons index indices inductionHypothesis =>
      by_cases hstep :
          (decide (left < right) &&
            !isLess pivot array[1 + left]!) = true
      · rw [scanLeft, if_pos hstep] at hresult ⊢
        apply inductionHypothesis
        · simp only [List.length_cons] at hcapacity
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hstep
          omega
        · exact hresult
      · rw [scanLeft, if_neg hstep] at hresult ⊢
        have hleftRight : left < right := hresult
        simp only [Bool.and_eq_true, decide_eq_true_eq,
          Bool.not_eq_true'] at hstep
        cases hless : isLess pivot array[1 + left]! with
        | false => exact (hstep ⟨hleftRight, hless⟩).elim
        | true => rfl

private theorem scanRight_stops_on_not_greater
    (indices : List ℕ) (left right : ℕ)
    (pivot : T) (array : Array T)
    (isLess : T → T → Bool)
    (hcapacity : right - left ≤ indices.length)
    (hresult : left < scanRight indices left right pivot array isLess) :
    isLess pivot
      array[scanRight indices left right pivot array isLess]! = false := by
  induction indices generalizing right with
  | nil =>
      exfalso
      simp only [scanRight, List.length_nil] at hresult hcapacity
      omega
  | cons index indices inductionHypothesis =>
      by_cases hstep :
          (decide (left < right) &&
            isLess pivot array[1 + (right - 1)]!) = true
      · rw [scanRight, if_pos hstep] at hresult ⊢
        apply inductionHypothesis
        · simp only [List.length_cons] at hcapacity
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hstep
          omega
        · exact hresult
      · rw [scanRight, if_neg hstep] at hresult ⊢
        have hleftRight : left < right := hresult
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hstep
        cases hless : isLess pivot array[1 + (right - 1)]! with
        | true => exact (hstep ⟨hleftRight, hless⟩).elim
        | false =>
            simpa [show 1 + (right - 1) = right by omega] using hless

private theorem scanLeft_forIn
    (indices : List ℕ) (left right : ℕ)
    (pivot : T) (array : Array T)
    (isLess : T → T → Bool) :
    (Id.run <| forIn indices left fun _ current =>
      if current < right &&
          !isLess pivot (array[1 + current]!) then
        do
          pure PUnit.unit
          pure (.yield (current + 1))
      else
        pure (.done current)) =
      scanLeft indices left right pivot array isLess := by
  induction indices generalizing left with
  | nil => rfl
  | cons index indices ih =>
      simp only [List.forIn_cons, scanLeft]
      split
      · exact ih (left + 1)
      · rfl

private theorem scanRight_forIn
    (indices : List ℕ) (left right : ℕ)
    (pivot : T) (array : Array T)
    (isLess : T → T → Bool) :
    (Id.run <| forIn indices right fun _ current =>
      if left < current &&
          isLess pivot (array[1 + (current - 1)]!) then
        do
          pure PUnit.unit
          pure (.yield (current - 1))
      else
        pure (.done current)) =
      scanRight indices left right pivot array isLess := by
  induction indices generalizing right with
  | nil => rfl
  | cons index indices ih =>
      simp only [List.forIn_cons, scanRight]
      split
      · exact ih (right - 1)
      · rfl

private theorem partitionScanLeft_forIn
    (indices : List ℕ) (left right : ℕ)
    (pivot : T) (array : Array T)
    (isLess : T → T → Bool) :
    (Id.run <| forIn indices left fun _ current =>
      if current < right &&
          isLess (array[1 + current]!) pivot then
        do
          pure PUnit.unit
          pure (.yield (current + 1))
      else
        pure (.done current)) =
      scanLeft indices left right pivot array (dualLess isLess) := by
  simpa only [dualLess, Bool.not_not] using
    scanLeft_forIn indices left right pivot array (dualLess isLess)

private theorem partitionScanRight_forIn
    (indices : List ℕ) (left right : ℕ)
    (pivot : T) (array : Array T)
    (isLess : T → T → Bool) :
    (Id.run <| forIn indices right fun _ current =>
      if left < current &&
          !isLess (array[1 + (current - 1)]!) pivot then
        do
          pure PUnit.unit
          pure (.yield (current - 1))
      else
        pure (.done current)) =
      scanRight indices left right pivot array (dualLess isLess) := by
  simpa only [dualLess] using
    scanRight_forIn indices left right pivot array (dualLess isLess)

private theorem partitionScanLeft_rangeAll
    (indices : List ℕ) (left right : ℕ)
    (pivot : T) (array : Array T)
    (isLess : T → T → Bool) :
    RangeAll array (1 + left)
      (1 + scanLeft indices left right pivot array (dualLess isLess))
      (fun item => isLess item pivot = true) := by
  have h :=
    scanLeft_rangeAll indices left right pivot array (dualLess isLess)
  intro index hstart hstop
  have hnot := h index hstart hstop
  simp only [dualLess] at hnot
  cases hvalue : isLess array[index]! pivot <;> simp_all

private theorem partitionScanRight_rangeAll
    (indices : List ℕ) (left right : ℕ)
    (pivot : T) (array : Array T)
    (isLess : T → T → Bool) :
    RangeAll array
      (1 + scanRight indices left right pivot array (dualLess isLess))
      (1 + right) (fun item => isLess item pivot = false) := by
  have h :=
    scanRight_rangeAll indices left right pivot array (dualLess isLess)
  intro index hstart hstop
  have hnot := h index hstart hstop
  simp only [dualLess] at hnot
  cases hvalue : isLess array[index]! pivot <;> simp_all

/-- `partitionP` places its selected pivot between the strictly-smaller and
the remaining elements. -/
theorem partitionP_order
    (array : Array T) (pivotIndex : ℕ)
    (isLess : T → T → Bool)
    (hpivot : pivotIndex < array.size) :
    let result := partitionP array pivotIndex isLess
    RangeAll result.2 0 result.1.1
        (fun item => isLess item result.2[result.1.1]! = true) ∧
      RangeAll result.2 (result.1.1 + 1) result.2.size
        (fun item => isLess item result.2[result.1.1]! = false) := by
  simp only [partitionP,
    Std.Legacy.Range.forIn_eq_forIn_range',
    Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel,
    Nat.div_one, Id.run_bind]
  generalize hscanLeft :
    (Id.run <| forIn
      (List.range' 0 (swp array 0 pivotIndex).size) 0
      fun _ left =>
        if decide (left < (swp array 0 pivotIndex).size - 1) &&
            isLess
              (swp array 0 pivotIndex)[1 + left]!
              (swp array 0 pivotIndex)[0]! then
          do
            pure PUnit.unit
            pure (.yield (left + 1))
        else
          pure (.done left)) = left
  generalize hscanRight :
    (Id.run <| forIn
      (List.range' 0 (swp array 0 pivotIndex).size)
      ((swp array 0 pivotIndex).size - 1)
      fun _ right =>
        if decide (left < right) &&
            !isLess
              (swp array 0 pivotIndex)[1 + (right - 1)]!
              (swp array 0 pivotIndex)[0]! then
          do
            pure PUnit.unit
            pure (.yield (right - 1))
        else
          pure (.done right)) = right
  generalize hblock :
    partitionInBlocks
      ((swp array 0 pivotIndex).extract
        (1 + left) (1 + right))
      (swp array 0 pivotIndex)[0]! isLess = block
  let swapped := swp array 0 pivotIndex
  let source := swapped.extract (1 + left) (1 + right)
  let rewritten := overwrite swapped (1 + left) block.2
  let middle := left + block.1
  have hswappedSize : swapped.size = array.size := swp_size _ _ _
  have hpositive : 0 < swapped.size := by
    rw [hswappedSize]
    omega
  have hrange := partitionP_scan_bounds swapped isLess hpositive
  dsimp only [swapped] at hrange
  rw [hscanLeft, hscanRight] at hrange
  have hrangeSwapped : left ≤ right ∧ right < swapped.size := by
    simpa only [swapped] using hrange
  have hleftDefinition := partitionScanLeft_forIn
    (List.range' 0 swapped.size) 0 (swapped.size - 1)
    swapped[0]! swapped isLess
  dsimp only [swapped] at hleftDefinition
  rw [hscanLeft] at hleftDefinition
  have hrightDefinition := partitionScanRight_forIn
    (List.range' 0 swapped.size) left (swapped.size - 1)
    swapped[0]! swapped isLess
  dsimp only [swapped] at hrightDefinition
  rw [hscanRight] at hrightDefinition
  have hleftOrder := partitionScanLeft_rangeAll
    (List.range' 0 swapped.size) 0 (swapped.size - 1)
    swapped[0]! swapped isLess
  rw [← hleftDefinition] at hleftOrder
  simp only [Nat.add_zero] at hleftOrder
  have hrightOrder := partitionScanRight_rangeAll
    (List.range' 0 swapped.size) left (swapped.size - 1)
    swapped[0]! swapped isLess
  rw [← hrightDefinition] at hrightOrder
  have hblockContract := partitionInBlocks_contract
    source swapped[0]! isLess
  have hblockOrder := partitionInBlocks_order
    source swapped[0]! isLess
  dsimp only [source, swapped] at hblockContract hblockOrder
  rw [hblock] at hblockContract hblockOrder
  have hsourceSize : source.size = right - left := by
    simp only [source, Array.size_extract]
    omega
  have hblockSize : block.2.size = source.size :=
    array_size_eq_of_perm hblockContract.2
  have hblockCount : block.1 ≤ block.2.size := by
    rw [hblockSize]
    simpa only [source, swapped] using hblockContract.1
  have hfit : 1 + left + block.2.size ≤ swapped.size := by
    rw [hblockSize, hsourceSize]
    omega
  have hmiddle : middle < rewritten.size := by
    have hcount : block.1 ≤ source.size := by
      simpa only [source, swapped] using hblockContract.1
    simp only [middle, rewritten, overwrite_size]
    rw [hsourceSize] at hcount
    omega
  have hprefix : RangeAll rewritten 1 (1 + middle)
      (fun item => isLess item swapped[0]! = true) := by
    intro index hindexStart hindexStop
    simp only [middle] at hindexStop
    rw [overwrite_get! swapped block.2 (1 + left) index hfit]
    by_cases hbefore : index < 1 + left
    · rw [if_neg (by omega)]
      exact hleftOrder index hindexStart hbefore
    · rw [if_pos (by
          constructor
          · omega
          · rw [hblockSize, hsourceSize]
            omega)]
      apply hblockOrder.1 (index - (1 + left))
      · omega
      · omega
  have hsuffix : RangeAll rewritten (1 + middle) rewritten.size
      (fun item => isLess item swapped[0]! = false) := by
    intro index hindexStart hindexStop
    rw [overwrite_get! swapped block.2 (1 + left) index hfit]
    by_cases hbeforeRight : index < 1 + right
    · rw [if_pos (by
          constructor
          · simp only [middle] at hindexStart
            omega
          · rw [hblockSize, hsourceSize]
            omega)]
      apply hblockOrder.2 (index - (1 + left))
      · simp only [middle] at hindexStart
        omega
      · rw [hblockSize, hsourceSize]
        omega
    · rw [if_neg (by
          rw [hblockSize, hsourceSize]
          omega)]
      apply hrightOrder index
      · omega
      · have hrightStop : 1 + (swapped.size - 1) = swapped.size := by
          omega
        rw [hrightStop]
        simpa only [rewritten, overwrite_size] using hindexStop
  have hpivotValue : (swp rewritten 0 middle)[middle]! = swapped[0]! := by
    rw [swp_get! rewritten 0 middle middle (by
      simpa only [rewritten, overwrite_size] using hpositive) hmiddle]
    have hzero : rewritten[0]! = swapped[0]! := by
      simp only [rewritten]
      rw [overwrite_get! swapped block.2 (1 + left) 0 hfit,
        if_neg (by omega)]
    by_cases hmiddleZero : middle = 0
    · simp [hmiddleZero, hzero]
    · simp [hmiddleZero, hzero]
  show
    RangeAll (swp rewritten 0 middle) 0 middle
        (fun item => isLess item (swp rewritten 0 middle)[middle]! = true) ∧
      RangeAll (swp rewritten 0 middle) (middle + 1)
        (swp rewritten 0 middle).size
        (fun item => isLess item (swp rewritten 0 middle)[middle]! = false)
  constructor
  · intro index hindexStart hindexStop
    rw [hpivotValue,
      swp_get! rewritten 0 middle index (by
        simpa only [rewritten, overwrite_size] using hpositive) hmiddle]
    by_cases hindexZero : index = 0
    · rw [if_pos hindexZero]
      exact hprefix middle (by omega) (by omega)
    · rw [if_neg hindexZero, if_neg (by omega)]
      exact hprefix index (by omega) (by omega)
  · intro index hindexStart hindexStop
    rw [hpivotValue,
      swp_get! rewritten 0 middle index (by
        simpa only [rewritten, overwrite_size] using hpositive) hmiddle,
      if_neg (by omega), if_neg (by omega)]
    apply hsuffix index
    · omega
    · simpa only [swp_size] using hindexStop

private def partitionEqualLoop
    (indices scanIndices : List ℕ)
    (pivot : T) (isLess : T → T → Bool)
    (state : MProd Bool (MProd ℕ (MProd ℕ (Array T)))) :
    MProd Bool (MProd ℕ (MProd ℕ (Array T))) := Id.run do
  let mut state := state
  for _ in indices do
    let ⟨done, left, right, array⟩ := state
    if !done then
      let mut left := left
      for _ in scanIndices do
        if left < right &&
            !isLess pivot (array[1 + left]!) then
          left := left + 1
        else
          break
      let mut right := right
      for _ in scanIndices do
        if left < right &&
            isLess pivot (array[1 + (right - 1)]!) then
          right := right - 1
        else
          break
      if left ≥ right then
        state := ⟨true, left, right, array⟩
      else
        let swapRight := right - 1
        let nextArray := swp array (1 + left) (1 + swapRight)
        let nextLeft := left + 1
        state := ⟨done, nextLeft, swapRight, nextArray⟩
  return state

private def partitionEqualStep
    (scanIndices : List ℕ) (pivot : T)
    (isLess : T → T → Bool)
    (state : MProd Bool (MProd ℕ (MProd ℕ (Array T)))) :
    ForInStep (MProd Bool (MProd ℕ (MProd ℕ (Array T)))) :=
  Id.run do
    let ⟨done, initialLeft, initialRight, array⟩ := state
    if !done then
      let mut left := initialLeft
      for _ in scanIndices do
        if left < initialRight &&
            !isLess pivot (array[1 + left]!) then
          left := left + 1
        else
          break
      let mut right := initialRight
      for _ in scanIndices do
        if left < right &&
            isLess pivot (array[1 + (right - 1)]!) then
          right := right - 1
        else
          break
      if left ≥ right then
        return .yield ⟨true, left, right, array⟩
      else
        return .yield ⟨done, left + 1, right - 1,
          swp array (1 + left) (1 + (right - 1))⟩
    else
      return .yield state

private theorem partitionEqualStep_isYield
    (scanIndices : List ℕ) (pivot : T)
    (isLess : T → T → Bool)
    (state : MProd Bool (MProd ℕ (MProd ℕ (Array T)))) :
    ∃ next, partitionEqualStep scanIndices pivot isLess state =
      .yield next := by
  rcases state with ⟨done, left, right, array⟩
  cases done with
  | true =>
      exact ⟨⟨true, left, right, array⟩,
        by simp [partitionEqualStep]⟩
  | false =>
      simp only [partitionEqualStep, Bool.not_false, ↓reduceIte]
      simp only [Id.run_bind]
      split
      · exact ⟨_, rfl⟩
      · exact ⟨_, rfl⟩

private theorem partitionEqualLoop_cons
    (index : ℕ) (indices scanIndices : List ℕ)
    (pivot : T) (isLess : T → T → Bool)
    (state : MProd Bool (MProd ℕ (MProd ℕ (Array T)))) :
    partitionEqualLoop (index :: indices) scanIndices pivot isLess state =
      partitionEqualLoop indices scanIndices pivot isLess
        (partitionEqualStep scanIndices pivot isLess state).run := by
  rcases partitionEqualStep_isYield scanIndices pivot isLess state with
    ⟨next, hnext⟩
  rw [partitionEqualLoop]
  simp only [List.forIn_cons]
  simp only [Id.run_bind, Id.run_pure, LawfulMonad.pure_bind]
  have hbody := hnext
  simp [partitionEqualStep] at hbody
  simp only [Bool.not_eq_true', Bool.and_eq_true,
    decide_eq_true_eq, ge_iff_le] at ⊢
  rw [hbody, hnext]
  simp only [ForInStep.run]
  rw [partitionEqualLoop]
  simp only [Id.run_bind, Id.run_pure, LawfulMonad.pure_bind,
    Bool.not_eq_true', Bool.and_eq_true, decide_eq_true_eq,
    ge_iff_le]

private theorem partitionEqualLoop_perm
    (indices scanIndices : List ℕ) (bound : ℕ)
    (pivot : T) (isLess : T → T → Bool) :
    ∀ (done : Bool) (left right : ℕ) (array original : Array T),
      left < bound →
      right < bound →
      array.size = bound →
      List.Perm array.toList original.toList →
      let result :=
        partitionEqualLoop indices scanIndices pivot isLess
          ⟨done, left, right, array⟩
      result.2.1 < bound ∧
        List.Perm result.2.2.2.toList original.toList := by
  induction indices with
  | nil =>
      intro done left right array original hleft hright hsize hperm
      simpa [partitionEqualLoop] using And.intro hleft hperm
  | cons index indices ih =>
      intro done left right array original hleft hright hsize hperm
      cases done with
      | false =>
        let scannedLeft := Id.run <|
          forIn scanIndices left fun _ current =>
            if current < right &&
                !isLess pivot (array[1 + current]!) then do
              pure PUnit.unit
              pure (.yield (current + 1))
            else
              pure (.done current)
        let scannedRight := Id.run <|
          forIn scanIndices right fun _ current =>
            if scannedLeft < current &&
                isLess pivot (array[1 + (current - 1)]!) then do
              pure PUnit.unit
              pure (.yield (current - 1))
            else
              pure (.done current)
        have hleftEq :
            scannedLeft =
              scanLeft scanIndices left right pivot array isLess :=
          scanLeft_forIn scanIndices left right pivot array isLess
        have hrightEq :
            scannedRight =
              scanRight scanIndices scannedLeft right pivot array isLess :=
          scanRight_forIn scanIndices scannedLeft right pivot array isLess
        have hscannedLeft : scannedLeft < bound := by
          rw [hleftEq]
          exact scanLeft_lt scanIndices left right bound pivot array
            isLess hleft hright
        have hscannedRightLe : scannedRight ≤ right := by
          rw [hrightEq]
          exact scanRight_le scanIndices scannedLeft right pivot array
            isLess
        have hscannedRight : scannedRight < bound :=
          hscannedRightLe.trans_lt hright
        by_cases hfinished : scannedLeft ≥ scannedRight
        · have hstate :
              partitionEqualStep scanIndices pivot isLess
                  ⟨false, left, right, array⟩ =
                .yield ⟨true, scannedLeft, scannedRight, array⟩ := by
            unfold partitionEqualStep
            simp only [Bool.not_false, ↓reduceIte]
            change
              Id.run (if scannedRight ≤ scannedLeft then
                pure
                  (.yield ⟨true, scannedLeft, scannedRight, array⟩ :
                    ForInStep
                      (MProd Bool (MProd ℕ (MProd ℕ (Array T)))))
              else
                pure
                  (.yield ⟨false, scannedLeft + 1, scannedRight - 1,
                    swp array (1 + scannedLeft)
                      (1 + (scannedRight - 1))⟩)) = _
            rw [if_pos hfinished]
            rfl
          rw [partitionEqualLoop_cons, hstate]
          exact ih true scannedLeft scannedRight array original
            hscannedLeft hscannedRight hsize hperm
        · have hleftIndex : 1 + scannedLeft < bound := by
            omega
          have hrightIndex : 1 + (scannedRight - 1) < bound := by
            omega
          have hswap :=
            swp_perm array (1 + scannedLeft)
              (1 + (scannedRight - 1))
              (hsize ▸ hleftIndex) (hsize ▸ hrightIndex)
          have hnext :=
            ih false (scannedLeft + 1) (scannedRight - 1)
              (swp array (1 + scannedLeft)
                (1 + (scannedRight - 1))) original
              (by omega) (by omega)
              (by simpa [swp, Array.set!] using hsize)
              (hswap.trans hperm)
          have hstate :
              partitionEqualStep scanIndices pivot isLess
                  ⟨false, left, right, array⟩ =
                .yield ⟨false, scannedLeft + 1, scannedRight - 1,
                  swp array (1 + scannedLeft)
                    (1 + (scannedRight - 1))⟩ := by
            unfold partitionEqualStep
            simp only [Bool.not_false, ↓reduceIte]
            change
              Id.run (if scannedRight ≤ scannedLeft then
                pure
                  (.yield ⟨true, scannedLeft, scannedRight, array⟩ :
                    ForInStep
                      (MProd Bool (MProd ℕ (MProd ℕ (Array T)))))
              else
                pure
                  (.yield ⟨false, scannedLeft + 1, scannedRight - 1,
                    swp array (1 + scannedLeft)
                      (1 + (scannedRight - 1))⟩)) = _
            rw [if_neg hfinished]
            rfl
          rw [partitionEqualLoop_cons, hstate]
          exact hnext
      | true =>
        have hstate :
            partitionEqualStep scanIndices pivot isLess
                ⟨true, left, right, array⟩ =
              .yield ⟨true, left, right, array⟩ := by
          simp [partitionEqualStep]
        rw [partitionEqualLoop_cons, hstate]
        exact ih true left right array original
          hleft hright hsize hperm

private def EqualPartitionInvariant
    (key : T → ℕ) (pivot : T) (original : Array T)
    (left right : ℕ) (array : Array T) : Prop :=
  left ≤ right ∧ right < array.size ∧
    List.Perm array.toList original.toList ∧
    KeysGE key array.toList (key pivot) ∧
    RangeAll array 0 (1 + left)
      (fun item => key item = key pivot) ∧
    RangeAll array (1 + right) array.size
      (fun item => key pivot < key item)

private theorem equalPartitionScanStep
    (indices : List ℕ) (key : T → ℕ) (pivot : T)
    (original array : Array T) (left right : ℕ)
    (hcapacity : right - left ≤ indices.length)
    (hinvariant :
      EqualPartitionInvariant key pivot original left right array) :
    let scannedLeft :=
      scanLeft indices left right pivot array (lessBy key)
    let scannedRight :=
      scanRight indices scannedLeft right pivot array (lessBy key)
    let next :=
      if scannedLeft ≥ scannedRight then
        (scannedLeft, scannedRight, array)
      else
        (scannedLeft + 1, scannedRight - 1,
          swp array (1 + scannedLeft) scannedRight)
    EqualPartitionInvariant key pivot original
      next.1 next.2.1 next.2.2 := by
  rcases hinvariant with
    ⟨hle, hright, hperm, hglobal, hprefix, hsuffix⟩
  let scannedLeft :=
    scanLeft indices left right pivot array (lessBy key)
  let scannedRight :=
    scanRight indices scannedLeft right pivot array (lessBy key)
  have hscannedLeftLe : scannedLeft ≤ right :=
    scanLeft_le indices left right pivot array (lessBy key) hle
  have hscannedRightLe : scannedRight ≤ right :=
    scanRight_le indices scannedLeft right pivot array (lessBy key)
  have hscannedLeftRight : scannedLeft ≤ scannedRight :=
    scanRight_ge indices scannedLeft right pivot array (lessBy key)
      hscannedLeftLe
  have hleftScanRaw :=
    scanLeft_rangeAll indices left right pivot array (lessBy key)
  have hleftScan : RangeAll array (1 + left) (1 + scannedLeft)
      (fun item => key item = key pivot) := by
    intro position hpositionStart hpositionStop
    have hnotGreater := hleftScanRaw position hpositionStart hpositionStop
    change lessBy key pivot array[position]! = false at hnotGreater
    rw [lessBy_eq_false_iff] at hnotGreater
    have hlower := KeysGE.get! key array (key pivot) position hglobal
      (by omega)
    omega
  have hrightScanRaw :=
    scanRight_rangeAll indices scannedLeft right pivot array (lessBy key)
  have hrightScan : RangeAll array (1 + scannedRight) (1 + right)
      (fun item => key pivot < key item) := by
    intro position hpositionStart hpositionStop
    have hgreater := hrightScanRaw position hpositionStart hpositionStop
    simpa only [lessBy_eq_true_iff] using hgreater
  have hprefixScanned : RangeAll array 0 (1 + scannedLeft)
      (fun item => key item = key pivot) :=
    hprefix.append hleftScan
  have hsuffixScanned : RangeAll array (1 + scannedRight) array.size
      (fun item => key pivot < key item) :=
    hrightScan.append hsuffix
  show EqualPartitionInvariant key pivot original
    (if scannedLeft ≥ scannedRight then
      (scannedLeft, scannedRight, array)
    else
      (scannedLeft + 1, scannedRight - 1,
        swp array (1 + scannedLeft) scannedRight)).1
    (if scannedLeft ≥ scannedRight then
      (scannedLeft, scannedRight, array)
    else
      (scannedLeft + 1, scannedRight - 1,
        swp array (1 + scannedLeft) scannedRight)).2.1
    (if scannedLeft ≥ scannedRight then
      (scannedLeft, scannedRight, array)
    else
      (scannedLeft + 1, scannedRight - 1,
        swp array (1 + scannedLeft) scannedRight)).2.2
  split
  next hfinished =>
    exact ⟨hscannedLeftRight, hscannedRightLe.trans_lt hright,
      hperm, hglobal, hprefixScanned, hsuffixScanned⟩
  next hfinished =>
    have hstrict : scannedLeft < scannedRight := by omega
    have hleftGreater :
        key pivot < key array[scannedLeft + 1]! := by
      have hresult := scanLeft_stops_on_greater indices left right
        pivot array (lessBy key) hcapacity
        (hstrict.trans_le hscannedRightLe)
      simpa only [scannedLeft, lessBy_eq_true_iff, Nat.add_comm] using hresult
    have hrightNotGreater :
        key array[scannedRight]! ≤ key pivot := by
      have hresult := scanRight_stops_on_not_greater indices
        scannedLeft right pivot array (lessBy key)
        (by
          have hleftLe := scanLeft_ge indices left right pivot array
            (lessBy key)
          omega)
        hstrict
      simpa only [scannedRight, lessBy_eq_false_iff] using hresult
    have hrightLower := KeysGE.get! key array (key pivot) scannedRight
      hglobal (hscannedRightLe.trans_lt hright)
    have hrightEqual : key array[scannedRight]! = key pivot := by omega
    have hgap : scannedLeft + 1 < scannedRight := by
      by_contra hnot
      have heq : scannedRight = scannedLeft + 1 := by omega
      rw [heq] at hrightEqual
      omega
    let next := swp array (1 + scannedLeft) scannedRight
    have hleftIndex : 1 + scannedLeft < array.size := by omega
    have hrightIndex : scannedRight < array.size := by omega
    have hnextPerm : List.Perm next.toList original.toList :=
      (swp_perm array (1 + scannedLeft) scannedRight
        hleftIndex hrightIndex).trans hperm
    have hnextGlobal : KeysGE key next.toList (key pivot) :=
      KeysGE.perm key
        (swp_perm array (1 + scannedLeft) scannedRight
          hleftIndex hrightIndex).symm hglobal
    have hnextPrefixBase : RangeAll next 0 (1 + scannedLeft)
        (fun item => key item = key pivot) := by
      apply RangeAll.swp array (1 + scannedLeft) scannedRight
        0 (1 + scannedLeft) _ hleftIndex hrightIndex hprefixScanned
      · omega
      · omega
    have hnextPrefixPoint : RangeAll next (1 + scannedLeft)
        (1 + (scannedLeft + 1))
        (fun item => key item = key pivot) := by
      intro position hpositionStart hpositionStop
      have hposition : position = 1 + scannedLeft := by omega
      subst position
      rw [swp_get! array (1 + scannedLeft) scannedRight
        (1 + scannedLeft) hleftIndex hrightIndex, if_pos rfl]
      exact hrightEqual
    have hnextPrefix := hnextPrefixBase.append hnextPrefixPoint
    have hnextSuffixBase : RangeAll next (1 + scannedRight) next.size
        (fun item => key pivot < key item) := by
      rw [swp_size]
      apply RangeAll.swp array (1 + scannedLeft) scannedRight
        (1 + scannedRight) array.size _ hleftIndex hrightIndex
        hsuffixScanned
      · omega
      · omega
    have hnextSuffixPoint : RangeAll next (1 + (scannedRight - 1))
        (1 + scannedRight) (fun item => key pivot < key item) := by
      intro position hpositionStart hpositionStop
      have hposition : position = scannedRight := by omega
      subst position
      rw [swp_get! array (1 + scannedLeft) scannedRight scannedRight
        hleftIndex hrightIndex, if_neg (by omega), if_pos rfl]
      simpa only [Nat.add_comm] using hleftGreater
    have hnextSuffix : RangeAll next (1 + (scannedRight - 1)) next.size
        (fun item => key pivot < key item) := by
      exact hnextSuffixPoint.append hnextSuffixBase
    show EqualPartitionInvariant key pivot original
      (scannedLeft + 1) (scannedRight - 1) next
    exact ⟨by omega, by simpa [next, swp_size] using
        show scannedRight - 1 < array.size by omega,
      hnextPerm, hnextGlobal, hnextPrefix, hnextSuffix⟩

private def EqualPartitionStateInvariant
    (key : T → ℕ) (pivot : T) (original : Array T)
    (state : MProd Bool (MProd ℕ (MProd ℕ (Array T)))) : Prop :=
  EqualPartitionInvariant key pivot original
      state.2.1 state.2.2.1 state.2.2.2 ∧
    (state.1 = true → state.2.1 = state.2.2.1)

private theorem partitionEqualStep_stateInvariant
    (scanIndices : List ℕ) (key : T → ℕ) (pivot : T)
    (original : Array T)
    (state : MProd Bool (MProd ℕ (MProd ℕ (Array T))))
    (hscanCapacity : state.2.2.2.size ≤ scanIndices.length)
    (hinvariant : EqualPartitionStateInvariant key pivot original state) :
    EqualPartitionStateInvariant key pivot original
      (partitionEqualStep scanIndices pivot (lessBy key) state).run := by
  rcases state with ⟨done, left, right, array⟩
  rcases hinvariant with ⟨hinvariant, hdoneEqual⟩
  cases done with
  | true =>
      simpa [partitionEqualStep, EqualPartitionStateInvariant] using
        And.intro hinvariant hdoneEqual
  | false =>
      have harrayCapacity : array.size ≤ scanIndices.length := by
        simpa using hscanCapacity
      let scannedLeft := Id.run <| forIn scanIndices left fun _ current =>
        if current < right &&
            !lessBy key pivot array[1 + current]! then do
          pure PUnit.unit
          pure (.yield (current + 1))
        else
          pure (.done current)
      let scannedRight := Id.run <|
        forIn scanIndices right fun _ current =>
          if scannedLeft < current &&
              lessBy key pivot array[1 + (current - 1)]! then do
            pure PUnit.unit
            pure (.yield (current - 1))
          else
            pure (.done current)
      have hleftEq : scannedLeft =
          scanLeft scanIndices left right pivot array (lessBy key) :=
        scanLeft_forIn scanIndices left right pivot array (lessBy key)
      have hrightEq : scannedRight =
          scanRight scanIndices scannedLeft right pivot array (lessBy key) :=
        scanRight_forIn scanIndices scannedLeft right pivot array (lessBy key)
      have hcapacity : right - left ≤ scanIndices.length := by
        have hright : right < array.size := by
          simpa using hinvariant.2.1
        omega
      have hsemantic := equalPartitionScanStep scanIndices key pivot
        original array left right hcapacity hinvariant
      dsimp only at hsemantic
      rw [← hleftEq] at hsemantic
      simp only [← hrightEq] at hsemantic
      by_cases hfinished : scannedLeft ≥ scannedRight
      · have hstep :
            partitionEqualStep scanIndices pivot (lessBy key)
                ⟨false, left, right, array⟩ =
              .yield ⟨true, scannedLeft, scannedRight, array⟩ := by
          unfold partitionEqualStep
          simp only [Bool.not_false, ↓reduceIte]
          change Id.run (if scannedRight ≤ scannedLeft then
            pure (.yield ⟨true, scannedLeft, scannedRight, array⟩ :
              ForInStep
                (MProd Bool (MProd ℕ (MProd ℕ (Array T)))))
          else pure (.yield ⟨false, scannedLeft + 1, scannedRight - 1,
            swp array (1 + scannedLeft) (1 + (scannedRight - 1))⟩)) = _
          rw [if_pos hfinished]
          rfl
        rw [hstep]
        simp only [ForInStep.run]
        have hnextInvariant : EqualPartitionInvariant key pivot original
            scannedLeft scannedRight array := by
          simpa only [hfinished, if_true, Prod.fst, Prod.snd] using hsemantic
        refine ⟨hnextInvariant, ?_⟩
        · intro _
          show scannedLeft = scannedRight
          have hle := hnextInvariant.1
          omega
      · have hstep :
            partitionEqualStep scanIndices pivot (lessBy key)
                ⟨false, left, right, array⟩ =
              .yield ⟨false, scannedLeft + 1, scannedRight - 1,
                swp array (1 + scannedLeft) scannedRight⟩ := by
          unfold partitionEqualStep
          simp only [Bool.not_false, ↓reduceIte]
          change Id.run (if scannedRight ≤ scannedLeft then
            pure (.yield ⟨true, scannedLeft, scannedRight, array⟩ :
              ForInStep
                (MProd Bool (MProd ℕ (MProd ℕ (Array T)))))
          else pure (.yield ⟨false, scannedLeft + 1, scannedRight - 1,
            swp array (1 + scannedLeft) (1 + (scannedRight - 1))⟩)) = _
          rw [if_neg hfinished]
          simp only [Id.run_pure]
          rw [show 1 + (scannedRight - 1) = scannedRight by omega]
        rw [hstep]
        simp only [ForInStep.run]
        refine ⟨?_, by simp⟩
        simpa only [scannedLeft, scannedRight, hfinished,
          if_false, Prod.fst, Prod.snd] using hsemantic

private theorem partitionEqualLoop_stateInvariant
    (indices scanIndices : List ℕ) (key : T → ℕ) (pivot : T)
    (original : Array T)
    (state : MProd Bool (MProd ℕ (MProd ℕ (Array T))))
    (hscanCapacity : original.size ≤ scanIndices.length)
    (hinvariant : EqualPartitionStateInvariant key pivot original state) :
    EqualPartitionStateInvariant key pivot original
      (partitionEqualLoop indices scanIndices pivot (lessBy key) state) := by
  induction indices generalizing state with
  | nil => simpa [partitionEqualLoop] using hinvariant
  | cons index indices inductionHypothesis =>
      rw [partitionEqualLoop_cons]
      apply inductionHypothesis
      have hstateSize : state.2.2.2.size = original.size := by
        have hlength := hinvariant.1.2.2.1.length_eq
        simpa using hlength
      apply partitionEqualStep_stateInvariant
      · omega
      · exact hinvariant

private theorem partitionEqualStep_progress
    (scanIndices : List ℕ) (pivot : T) (isLess : T → T → Bool)
    (state : MProd Bool (MProd ℕ (MProd ℕ (Array T)))) :
    let next := (partitionEqualStep scanIndices pivot isLess state).run
    next.1 = true ∨
      next.2.2.1 - next.2.1 < state.2.2.1 - state.2.1 := by
  rcases state with ⟨done, left, right, array⟩
  cases done with
  | true => simp [partitionEqualStep]
  | false =>
      let scannedLeft := Id.run <| forIn scanIndices left fun _ current =>
        if current < right && !isLess pivot array[1 + current]! then do
          pure PUnit.unit
          pure (.yield (current + 1))
        else
          pure (.done current)
      let scannedRight := Id.run <|
        forIn scanIndices right fun _ current =>
          if scannedLeft < current &&
              isLess pivot array[1 + (current - 1)]! then do
            pure PUnit.unit
            pure (.yield (current - 1))
          else
            pure (.done current)
      have hleftEq : scannedLeft =
          scanLeft scanIndices left right pivot array isLess :=
        scanLeft_forIn scanIndices left right pivot array isLess
      have hrightEq : scannedRight =
          scanRight scanIndices scannedLeft right pivot array isLess :=
        scanRight_forIn scanIndices scannedLeft right pivot array isLess
      have hleftGe : left ≤ scannedLeft := by
        have hbound := scanLeft_ge scanIndices left right pivot array isLess
        rwa [← hleftEq] at hbound
      have hrightLe : scannedRight ≤ right := by
        have hbound := scanRight_le scanIndices scannedLeft right pivot array isLess
        rwa [← hrightEq] at hbound
      by_cases hfinished : scannedLeft ≥ scannedRight
      · left
        unfold partitionEqualStep
        simp only [Bool.not_false, ↓reduceIte]
        change (Id.run (if scannedRight ≤ scannedLeft then
          pure (.yield ⟨true, scannedLeft, scannedRight, array⟩ :
            ForInStep
              (MProd Bool (MProd ℕ (MProd ℕ (Array T)))))
        else pure (.yield ⟨false, scannedLeft + 1, scannedRight - 1,
          swp array (1 + scannedLeft) (1 + (scannedRight - 1))⟩))).run.1 = true
        rw [if_pos hfinished]
        rfl
      · right
        have hstrict : scannedLeft < scannedRight := by omega
        unfold partitionEqualStep
        simp only [Bool.not_false, ↓reduceIte]
        change (Id.run (if scannedRight ≤ scannedLeft then
          pure (.yield ⟨true, scannedLeft, scannedRight, array⟩ :
            ForInStep
              (MProd Bool (MProd ℕ (MProd ℕ (Array T)))))
        else pure (.yield ⟨false, scannedLeft + 1, scannedRight - 1,
          swp array (1 + scannedLeft) (1 + (scannedRight - 1))⟩)) |>.run).2.2.1 -
            (Id.run (if scannedRight ≤ scannedLeft then
          pure (.yield ⟨true, scannedLeft, scannedRight, array⟩ :
            ForInStep
              (MProd Bool (MProd ℕ (MProd ℕ (Array T)))))
        else pure (.yield ⟨false, scannedLeft + 1, scannedRight - 1,
          swp array (1 + scannedLeft) (1 + (scannedRight - 1))⟩)) |>.run).2.1 <
            right - left
        rw [if_neg hfinished]
        simp only [ForInStep.run]
        omega

private theorem partitionEqualLoop_done_of_done
    (indices scanIndices : List ℕ) (pivot : T)
    (isLess : T → T → Bool)
    (state : MProd Bool (MProd ℕ (MProd ℕ (Array T))))
    (hdone : state.1 = true) :
    (partitionEqualLoop indices scanIndices pivot isLess state).1 = true := by
  induction indices generalizing state with
  | nil => simpa [partitionEqualLoop] using hdone
  | cons index indices inductionHypothesis =>
      rw [partitionEqualLoop_cons]
      apply inductionHypothesis
      rcases state with ⟨done, left, right, array⟩
      cases done <;> simp_all [partitionEqualStep]

private theorem partitionEqualLoop_eventually_done
    (indices scanIndices : List ℕ) (pivot : T)
    (isLess : T → T → Bool)
    (state : MProd Bool (MProd ℕ (MProd ℕ (Array T))))
    (hsteps : state.2.2.1 - state.2.1 < indices.length) :
    (partitionEqualLoop indices scanIndices pivot isLess state).1 = true := by
  induction indices generalizing state with
  | nil => simp at hsteps
  | cons index indices inductionHypothesis =>
      rw [partitionEqualLoop_cons]
      let next := (partitionEqualStep scanIndices pivot isLess state).run
      show (partitionEqualLoop indices scanIndices pivot isLess next).1 = true
      have hprogress := partitionEqualStep_progress
        scanIndices pivot isLess state
      change next.1 = true ∨
        next.2.2.1 - next.2.1 < state.2.2.1 - state.2.1 at hprogress
      rcases hprogress with hdone | hsmaller
      · exact partitionEqualLoop_done_of_done
          indices scanIndices pivot isLess next hdone
      · apply inductionHypothesis
        simp only [List.length_cons] at hsteps
        omega

theorem partitionEqual_perm
    (array : Array T) (pivotIndex : ℕ)
    (isLess : T → T → Bool)
    (hpivot : pivotIndex < array.size) :
    List.Perm
      (partitionEqual array pivotIndex isLess).2.toList
      array.toList := by
  have hnonempty : 0 < array.size := by omega
  let swapped := swp array 0 pivotIndex
  have hswap : List.Perm swapped.toList array.toList :=
    swp_perm array 0 pivotIndex hnonempty hpivot
  have hsize : swapped.size = array.size := by
    simp [swapped, swp, Array.set!]
  have hloop :=
    partitionEqualLoop_perm (List.range (swapped.size + 1))
      (List.range swapped.size) swapped.size swapped[0]! isLess
      false 0 (swapped.size - 1) swapped array
      (by omega) (by omega) rfl hswap
  simpa [partitionEqual, partitionEqualLoop, scanLeft, scanRight,
    List.range'_eq_map_range, swapped] using hloop.2

theorem partitionEqual_bound
    (array : Array T) (pivotIndex : ℕ)
    (isLess : T → T → Bool)
    (hpivot : pivotIndex < array.size) :
    let result := partitionEqual array pivotIndex isLess
    1 ≤ result.1 ∧ result.1 ≤ result.2.size := by
  dsimp only
  have hnonempty : 0 < array.size := by omega
  let swapped := swp array 0 pivotIndex
  have hswap : List.Perm swapped.toList array.toList :=
    swp_perm array 0 pivotIndex hnonempty hpivot
  have hsize : swapped.size = array.size := by
    simp [swapped, swp, Array.set!]
  have hloop :=
    partitionEqualLoop_perm (List.range (swapped.size + 1))
      (List.range swapped.size) swapped.size swapped[0]! isLess
      false 0 (swapped.size - 1) swapped array
      (by omega) (by omega) rfl hswap
  have hmidle :
      (partitionEqual array pivotIndex isLess).1 ≤ swapped.size := by
    simpa [partitionEqual, partitionEqualLoop, scanLeft, scanRight,
      List.range'_eq_map_range, swapped] using
        Nat.succ_le_iff.mpr hloop.1
  have hresultSize :
      (partitionEqual array pivotIndex isLess).2.size = array.size := by
    have hperm :=
      partitionEqual_perm array pivotIndex isLess hpivot
    simpa using hperm.length_eq
  constructor
  · simp [partitionEqual]
  · omega

/-- Under the predecessor condition used by pdqsort, `partitionEqual`
returns an equality prefix followed by elements strictly greater than the
pivot. -/
theorem partitionEqual_ordered
    (array : Array T) (pivotIndex : ℕ) (key : T → ℕ)
    (hpivot : pivotIndex < array.size)
    (hlower : KeysGE key array.toList (key array[pivotIndex]!)) :
    let result := partitionEqual array pivotIndex (lessBy key)
    RangeAll result.2 0 result.1
        (fun item => key item = key array[pivotIndex]!) ∧
      RangeAll result.2 result.1 result.2.size
        (fun item => key array[pivotIndex]! < key item) := by
  have hnonempty : 0 < array.size := by omega
  let swapped := swp array 0 pivotIndex
  have hswap : List.Perm swapped.toList array.toList :=
    swp_perm array 0 pivotIndex hnonempty hpivot
  have hswappedSize : swapped.size = array.size := by
    simp [swapped, swp_size]
  have hpivotValue : swapped[0]! = array[pivotIndex]! := by
    simp only [swapped]
    rw [swp_get! array 0 pivotIndex 0 hnonempty hpivot, if_pos rfl]
  let initial : MProd Bool (MProd ℕ (MProd ℕ (Array T))) :=
    ⟨false, 0, swapped.size - 1, swapped⟩
  have hinitial : EqualPartitionStateInvariant key swapped[0]! array initial := by
    refine ⟨⟨?_, ?_, hswap, ?_, ?_, ?_⟩, by simp [initial]⟩
    · simp [initial]
    · simp [initial]
      omega
    · apply KeysGE.perm key hswap.symm
      simpa only [hpivotValue] using hlower
    · intro position hpositionStart hpositionStop
      have hposition : position = 0 := by
        simp only [initial] at hpositionStop
        omega
      subst position
      rfl
    · have hstart : 1 + (swapped.size - 1) = swapped.size := by omega
      rw [hstart]
      exact RangeAll.empty swapped swapped.size _
  let loopResult := partitionEqualLoop
    (List.range (swapped.size + 1)) (List.range swapped.size)
    swapped[0]! (lessBy key) initial
  have hloop : EqualPartitionStateInvariant key swapped[0]! array loopResult := by
    apply partitionEqualLoop_stateInvariant
    · simp [hswappedSize]
    · exact hinitial
  have hdone : loopResult.1 = true := by
    apply partitionEqualLoop_eventually_done
    simp [initial]
  have hcursors : loopResult.2.1 = loopResult.2.2.1 :=
    hloop.2 hdone
  have hdefinition :
      partitionEqual array pivotIndex (lessBy key) =
        (loopResult.2.1 + 1, loopResult.2.2.2) := by
    simp [partitionEqual, partitionEqualLoop,
      List.range'_eq_map_range, swapped, initial, loopResult]
  clear hinitial hdone
  clear_value loopResult swapped
  rw [hdefinition]
  constructor
  · simpa only [hpivotValue, Nat.add_comm] using hloop.1.2.2.2.2.1
  · rw [hcursors]
    simpa only [hpivotValue, Nat.add_comm] using hloop.1.2.2.2.2.2

private def pivotSort2 (v : Array T) (isLess : T → T → Bool)
    (x y swaps : ℕ) : ℕ × ℕ × ℕ :=
  if isLess (v[y]!) (v[x]!) then
    (y, x, swaps + 1)
  else
    (x, y, swaps)

private def pivotSort3
    (sort2 : ℕ → ℕ → ℕ → ℕ × ℕ × ℕ)
    (x y z swaps : ℕ) : ℕ × ℕ × ℕ × ℕ :=
  let (x, y, swaps) := sort2 x y swaps
  let (y, z, swaps) := sort2 y z swaps
  let (x, y, swaps) := sort2 x y swaps
  (x, y, z, swaps)

private def choosePivotCore (v : Array T)
    (sort3 : ℕ → ℕ → ℕ → ℕ → ℕ × ℕ × ℕ × ℕ) :
    (ℕ × Bool) × Array T := Id.run do
  let len := v.size
  let mut a := len / 4 * 1
  let mut b := len / 4 * 2
  let mut c := len / 4 * 3
  let mut swaps : ℕ := 0
  if len ≥ 8 then
    if len ≥ 50 then
      let (_, ya, _, sw) := sort3 (a - 1) a (a + 1) swaps
      a := ya
      swaps := sw
      let (_, yb, _, sw) := sort3 (b - 1) b (b + 1) swaps
      b := yb
      swaps := sw
      let (_, yc, _, sw) := sort3 (c - 1) c (c + 1) swaps
      c := yc
      swaps := sw
    let (xa, yb, zc, sw) := sort3 a b c swaps
    a := xa
    b := yb
    c := zc
    swaps := sw
  if swaps < 4 * 3 then
    return ((b, decide (swaps == 0)), v)
  else
    return ((len - 1 - b, true), v.reverse)

private theorem choosePivot_eq_core (v : Array T)
    (isLess : T → T → Bool) :
    choosePivot v isLess =
      choosePivotCore v (pivotSort3 (pivotSort2 v isLess)) := by
  rfl

omit [Inhabited T] in
private theorem choosePivotCore_perm (v : Array T)
    (sort3 : ℕ → ℕ → ℕ → ℕ → ℕ × ℕ × ℕ × ℕ) :
    List.Perm (choosePivotCore v sort3).2.toList v.toList := by
  unfold choosePivotCore
  by_cases h8 : v.size ≥ 8
  · simp only [h8, ↓reduceIte]
    by_cases h50 : v.size ≥ 50
    · simp only [h50, ↓reduceIte]
      generalize sort3 (v.size / 4 * 1 - 1) (v.size / 4 * 1)
          (v.size / 4 * 1 + 1) 0 = ra
      rcases ra with ⟨xa, ya, za, sa⟩
      generalize sort3 (v.size / 4 * 2 - 1) (v.size / 4 * 2)
          (v.size / 4 * 2 + 1) sa = rb
      rcases rb with ⟨xb, yb, zb, sb⟩
      generalize sort3 (v.size / 4 * 3 - 1) (v.size / 4 * 3)
          (v.size / 4 * 3 + 1) sb = rc
      rcases rc with ⟨xc, yc, zc, sc⟩
      generalize sort3 ya yb yc sc = r
      rcases r with ⟨x, y, z, swaps⟩
      split
      · exact List.Perm.refl _
      · change List.Perm v.reverse.toList v.toList
        rw [Array.toList_reverse]
        exact List.reverse_perm _
    · simp only [h50, ↓reduceIte]
      generalize sort3 (v.size / 4 * 1) (v.size / 4 * 2)
          (v.size / 4 * 3) 0 = r
      rcases r with ⟨x, y, z, swaps⟩
      split
      · exact List.Perm.refl _
      · change List.Perm v.reverse.toList v.toList
        rw [Array.toList_reverse]
        exact List.reverse_perm _
  · simp only [h8, ↓reduceIte]
    split
    · exact List.Perm.refl _
    · change List.Perm v.reverse.toList v.toList
      rw [Array.toList_reverse]
      exact List.reverse_perm _

theorem choosePivot_perm (v : Array T)
    (isLess : T → T → Bool) :
    List.Perm (choosePivot v isLess).2.toList v.toList := by
  rw [choosePivot_eq_core]
  exact choosePivotCore_perm v _

private theorem pivotSort2_bounds (v : Array T)
    (isLess : T → T → Bool) (x y swaps : ℕ)
    (hx : x < v.size) (hy : y < v.size) :
    let r := pivotSort2 v isLess x y swaps
    r.1 < v.size ∧ r.2.1 < v.size := by
  unfold pivotSort2
  split <;> simp_all

private theorem pivotSort3_bounds (v : Array T)
    (isLess : T → T → Bool) (x y z swaps : ℕ)
    (hx : x < v.size) (hy : y < v.size) (hz : z < v.size) :
    let r := pivotSort3 (pivotSort2 v isLess) x y z swaps
    r.1 < v.size ∧ r.2.1 < v.size ∧ r.2.2.1 < v.size := by
  unfold pivotSort3
  have hxy := pivotSort2_bounds v isLess x y swaps hx hy
  generalize hxyEq : pivotSort2 v isLess x y swaps = rxy at hxy ⊢
  rcases rxy with ⟨x₁, y₁, swaps₁⟩
  simp only at hxy
  have hyz := pivotSort2_bounds v isLess y₁ z swaps₁ hxy.2 hz
  generalize hyzEq : pivotSort2 v isLess y₁ z swaps₁ = ryz at hyz ⊢
  rcases ryz with ⟨y₂, z₂, swaps₂⟩
  simp only at hyz
  have hxy₂ := pivotSort2_bounds v isLess x₁ y₂ swaps₂ hxy.1 hyz.1
  generalize hxy₂Eq : pivotSort2 v isLess x₁ y₂ swaps₂ = rxy₂ at hxy₂ ⊢
  rcases rxy₂ with ⟨x₃, y₃, swaps₃⟩
  simp only [hyzEq, hxy₂Eq]
  exact ⟨hxy₂.1, hxy₂.2, hyz.2⟩

omit [Inhabited T] in
private theorem choosePivotCore_bound (v : Array T)
    (sort3 : ℕ → ℕ → ℕ → ℕ → ℕ × ℕ × ℕ × ℕ)
    (hsort3 : ∀ x y z swaps, x < v.size → y < v.size → z < v.size →
      let r := sort3 x y z swaps
      r.1 < v.size ∧ r.2.1 < v.size ∧ r.2.2.1 < v.size)
    (hsize : 0 < v.size) :
    (choosePivotCore v sort3).1.1 < (choosePivotCore v sort3).2.size := by
  unfold choosePivotCore
  by_cases h8 : v.size ≥ 8
  · simp only [h8, ↓reduceIte]
    by_cases h50 : v.size ≥ 50
    · simp only [h50, ↓reduceIte]
      have ha := hsort3 (v.size / 4 * 1 - 1) (v.size / 4 * 1)
        (v.size / 4 * 1 + 1) 0 (by omega) (by omega) (by omega)
      generalize hra : sort3 (v.size / 4 * 1 - 1) (v.size / 4 * 1)
          (v.size / 4 * 1 + 1) 0 = ra at ha ⊢
      rcases ra with ⟨xa, ya, za, sa⟩
      simp only at ha
      have hb := hsort3 (v.size / 4 * 2 - 1) (v.size / 4 * 2)
        (v.size / 4 * 2 + 1) sa (by omega) (by omega) (by omega)
      generalize hrb : sort3 (v.size / 4 * 2 - 1) (v.size / 4 * 2)
          (v.size / 4 * 2 + 1) sa = rb at hb ⊢
      rcases rb with ⟨xb, yb, zb, sb⟩
      simp only at hb
      have hc := hsort3 (v.size / 4 * 3 - 1) (v.size / 4 * 3)
        (v.size / 4 * 3 + 1) sb (by omega) (by omega) (by omega)
      generalize hrc : sort3 (v.size / 4 * 3 - 1) (v.size / 4 * 3)
          (v.size / 4 * 3 + 1) sb = rc at hc ⊢
      rcases rc with ⟨xc, yc, zc, sc⟩
      simp only at hc
      have hfinal := hsort3 ya yb yc sc ha.2.1 hb.2.1 hc.2.1
      generalize hrf : sort3 ya yb yc sc = r at hfinal ⊢
      rcases r with ⟨x, y, z, swaps⟩
      simp only at hfinal
      split
      · change y < v.size
        exact hfinal.2.1
      · change v.size - 1 - y < v.reverse.size
        simp only [Array.size_reverse]
        omega
    · simp only [h50, ↓reduceIte]
      have hfinal := hsort3 (v.size / 4 * 1) (v.size / 4 * 2)
        (v.size / 4 * 3) 0 (by omega) (by omega) (by omega)
      generalize hrf : sort3 (v.size / 4 * 1) (v.size / 4 * 2)
          (v.size / 4 * 3) 0 = r at hfinal ⊢
      rcases r with ⟨x, y, z, swaps⟩
      simp only at hfinal
      split
      · change y < v.size
        exact hfinal.2.1
      · change v.size - 1 - y < v.reverse.size
        simp only [Array.size_reverse]
        omega
  · simp only [h8, ↓reduceIte]
    split
    · change v.size / 4 * 2 < v.size
      omega
    · omega

theorem choosePivot_bound (v : Array T)
    (isLess : T → T → Bool) (hsize : 0 < v.size) :
    (choosePivot v isLess).1.1 < (choosePivot v isLess).2.size := by
  rw [choosePivot_eq_core]
  exact choosePivotCore_bound v _ (pivotSort3_bounds v isLess) hsize

def PartitionInBlocksCountContract : Prop :=
  ∀ (array : Array T) (pivot : T)
      (isLess : T → T → Bool),
    (partitionInBlocks array pivot isLess).1 ≤ array.size

theorem partitionP_bound_of_blocks_count
    (hblocks : PartitionInBlocksCountContract (T := T))
    (array : Array T) (pivotIndex : ℕ)
    (isLess : T → T → Bool)
    (hpivot : pivotIndex < array.size) :
    (partitionP array pivotIndex isLess).1.1 <
      (partitionP array pivotIndex isLess).2.size := by
  simp only [partitionP,
    Std.Legacy.Range.forIn_eq_forIn_range',
    Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel,
    Nat.div_one, Id.run_bind]
  generalize hscanLeft :
    (Id.run <| forIn
      (List.range' 0 (swp array 0 pivotIndex).size) 0
      fun _ left =>
        if decide (left < (swp array 0 pivotIndex).size - 1) &&
            isLess
              (swp array 0 pivotIndex)[1 + left]!
              (swp array 0 pivotIndex)[0]! then
          do
            pure PUnit.unit
            pure (.yield (left + 1))
        else
          pure (.done left)) = left
  generalize hscanRight :
    (Id.run <| forIn
      (List.range' 0 (swp array 0 pivotIndex).size)
      ((swp array 0 pivotIndex).size - 1)
      fun _ right =>
        if decide (left < right) &&
            !isLess
              (swp array 0 pivotIndex)[1 + (right - 1)]!
              (swp array 0 pivotIndex)[0]! then
          do
            pure PUnit.unit
            pure (.yield (right - 1))
        else
          pure (.done right)) = right
  have hswappedSize :
      (swp array 0 pivotIndex).size = array.size := by
    simp [swp, Array.set!]
  have hrange :=
    partitionP_scan_bounds (swp array 0 pivotIndex) isLess
      (by omega)
  dsimp only at hrange
  rw [hscanLeft, hscanRight] at hrange
  generalize hblock :
    partitionInBlocks
      ((swp array 0 pivotIndex).extract
        (1 + left) (1 + right))
      (swp array 0 pivotIndex)[0]! isLess = block
  have hcount := hblocks
    ((swp array 0 pivotIndex).extract
      (1 + left) (1 + right))
    (swp array 0 pivotIndex)[0]! isLess
  rw [hblock] at hcount
  have hsourceSize :
      ((swp array 0 pivotIndex).extract
        (1 + left) (1 + right)).size =
        right - left := by
    simp only [Array.size_extract]
    omega
  have hmid :
      left + block.1 < (swp array 0 pivotIndex).size := by
    change block.1 ≤
      ((swp array 0 pivotIndex).extract
        (1 + left) (1 + right)).size at hcount
    omega
  change left + block.1 <
    (swp
      (overwrite (swp array 0 pivotIndex) (1 + left) block.2)
      0 (left + block.1)).size
  rw [show
    (swp
      (overwrite (swp array 0 pivotIndex) (1 + left) block.2)
      0 (left + block.1)).size =
      (swp array 0 pivotIndex).size by
        simp [swp, Array.set!, overwrite_size]]
  exact hmid

omit [Inhabited T] in
private theorem array_extract_append_extract
    (a : Array T) (mid : ℕ) (hmid : mid ≤ a.size) :
    (a.extract 0 mid ++ a.extract mid a.size).toList = a.toList := by
  simp [hmid]

omit [Inhabited T] in
private theorem perm_extract_append_extract
    (a : Array T) (mid : ℕ) (hmid : mid ≤ a.size)
    (left' right' : Array T)
    (hleft : List.Perm left'.toList (a.extract 0 mid).toList)
    (hright : List.Perm right'.toList (a.extract mid a.size).toList) :
    List.Perm (left' ++ right').toList a.toList := by
  have heq := array_extract_append_extract a mid hmid
  rw [Array.toList_append] at heq ⊢
  exact (hleft.append hright).trans <|
    heq ▸ List.Perm.refl _

private theorem array_pivot_decomposition
    (a : Array T) (mid : ℕ) (hmid : mid < a.size) :
    (a.extract 0 mid ++ #[a[mid]!] ++ a.extract (mid + 1) a.size).toList =
      a.toList := by
  simp only [Array.toList_append, Array.toList_extract]
  simp only [List.extract, List.drop_zero, Nat.sub_zero]
  have hlen : a.toList.length = a.size := Array.length_toList
  have htail :
      List.take (a.size - (mid + 1)) (List.drop (mid + 1) a.toList) =
        List.drop (mid + 1) a.toList := by
    apply (List.take_eq_self_iff _).2
    simp [hlen]
  rw [htail]
  rw [show a[mid]! = a.toList[mid] by simp [hmid]]
  have hlist : mid < a.toList.length := by simpa [hlen] using hmid
  rw [List.take_concat_get' a.toList mid hlist,
    List.take_append_drop]

private theorem perm_pivot_decomposition
    (a : Array T) (mid : ℕ) (hmid : mid < a.size)
    (left' right' : Array T)
    (hleft : List.Perm left'.toList (a.extract 0 mid).toList)
    (hright : List.Perm right'.toList (a.extract (mid + 1) a.size).toList) :
    List.Perm (left' ++ #[a[mid]!] ++ right').toList a.toList := by
  have heq := array_pivot_decomposition a mid hmid
  simp only [Array.toList_append] at heq ⊢
  exact
    ((hleft.append (List.Perm.refl [a[mid]!])).append hright).trans <|
      heq ▸ List.Perm.refl _

/-- The contracts needed by the recursive pdqsort driver.  This deliberately
mentions only multiset preservation and the bounds needed to split arrays. -/
structure DriverContracts (T : Type) [Inhabited T] where
  insertionSort_perm :
    ∀ (v : Array T) (isLess : T → T → Bool),
      List.Perm (insertionSort v isLess).toList v.toList
  heapsort_perm :
    ∀ (v : Array T) (isLess : T → T → Bool),
      List.Perm (heapsort v isLess).toList v.toList
  breakPatterns_perm :
    ∀ (v : Array T), List.Perm (breakPatterns v).toList v.toList
  choosePivot_perm :
    ∀ (v : Array T) (isLess : T → T → Bool),
      List.Perm (choosePivot v isLess).2.toList v.toList
  choosePivot_bound :
    ∀ (v : Array T) (isLess : T → T → Bool), 0 < v.size →
      (choosePivot v isLess).1.1 < (choosePivot v isLess).2.size
  partialInsertionSort_perm :
    ∀ (v : Array T) (isLess : T → T → Bool),
      List.Perm (partialInsertionSort v isLess).2.toList v.toList
  partitionEqual_perm :
    ∀ (v : Array T) (pivot : ℕ) (isLess : T → T → Bool), pivot < v.size →
      List.Perm (partitionEqual v pivot isLess).2.toList v.toList
  partitionEqual_bound :
    ∀ (v : Array T) (pivot : ℕ) (isLess : T → T → Bool), pivot < v.size →
      let mid := (partitionEqual v pivot isLess).1
      1 ≤ mid ∧ mid ≤ (partitionEqual v pivot isLess).2.size
  partitionP_perm :
    ∀ (v : Array T) (pivot : ℕ) (isLess : T → T → Bool), pivot < v.size →
      List.Perm (partitionP v pivot isLess).2.toList v.toList
  partitionP_bound :
    ∀ (v : Array T) (pivot : ℕ) (isLess : T → T → Bool), pivot < v.size →
      (partitionP v pivot isLess).1.1 < (partitionP v pivot isLess).2.size

omit [Inhabited T] in
private theorem size_eq_of_perm {a b : Array T}
    (h : List.Perm a.toList b.toList) : a.size = b.size := by
  simpa using h.length_eq

private theorem partitionEqual_branch_perm
    (contracts : DriverContracts T)
    (v : Array T) (pivot : ℕ) (isLess : T → T → Bool)
    (hpivot : pivot < v.size)
    (tail' : Array T)
    (htail :
      List.Perm tail'.toList
        ((partitionEqual v pivot isLess).2.extract
          (partitionEqual v pivot isLess).1
          (partitionEqual v pivot isLess).2.size).toList) :
    List.Perm
      ((partitionEqual v pivot isLess).2.extract 0
          (partitionEqual v pivot isLess).1 ++ tail').toList
      v.toList := by
  let result := partitionEqual v pivot isLess
  have hbounds := contracts.partitionEqual_bound v pivot isLess hpivot
  have hresult := contracts.partitionEqual_perm v pivot isLess hpivot
  have hassembled :
      List.Perm
        (result.2.extract 0 result.1 ++ tail').toList
        result.2.toList := by
    exact perm_extract_append_extract result.2 result.1 hbounds.2
      _ _ (List.Perm.refl _) htail
  exact hassembled.trans hresult

private theorem partitionP_branch_perm
    (contracts : DriverContracts T)
    (v : Array T) (pivot : ℕ) (isLess : T → T → Bool)
    (hpivot : pivot < v.size)
    (left' right' : Array T)
    (hleft :
      List.Perm left'.toList
        ((partitionP v pivot isLess).2.extract 0
          (partitionP v pivot isLess).1.1).toList)
    (hright :
      List.Perm right'.toList
        ((partitionP v pivot isLess).2.extract
          ((partitionP v pivot isLess).1.1 + 1)
          (partitionP v pivot isLess).2.size).toList) :
    let result := partitionP v pivot isLess
    List.Perm
      (left' ++ #[result.2[result.1.1]!] ++ right').toList
      v.toList := by
  let result := partitionP v pivot isLess
  have hmid := contracts.partitionP_bound v pivot isLess hpivot
  have hresult := contracts.partitionP_perm v pivot isLess hpivot
  have hassembled :
      List.Perm
        (left' ++ #[result.2[result.1.1]!] ++ right').toList
        result.2.toList := by
    exact perm_pivot_decomposition result.2 result.1.1 hmid
      left' right' hleft hright
  exact hassembled.trans hresult

private theorem recursePartition_perm
    (contracts : DriverContracts T)
    (rec : Array T → Option T → ℕ → Bool → Bool → Array T)
    (hrec : ∀ v pred limit wasBalanced wasPartitioned,
      List.Perm
        (rec v pred limit wasBalanced wasPartitioned).toList
        v.toList)
    (v : Array T) (isLess : T → T → Bool) (pred : Option T)
    (limit len pivot : ℕ) (hpivot : pivot < v.size) :
    List.Perm
      (recursePartition rec v isLess pred limit len pivot).toList
      v.toList := by
  unfold recursePartition
  generalize hresult : partitionP v pivot isLess = result
  rcases result with ⟨⟨mid, wasP⟩, v4⟩
  dsimp only
  have hbranch :=
    partitionP_branch_perm contracts v pivot isLess hpivot
  rw [hresult] at hbranch
  dsimp only at hbranch
  split
  · apply hbranch
    · exact hrec _ _ _ _ _
    · exact hrec _ _ _ _ _
  · apply hbranch
    · exact hrec _ _ _ _ _
    · exact hrec _ _ _ _ _

private theorem recursePred_perm
    (contracts : DriverContracts T)
    (rec : Array T → Option T → ℕ → Bool → Bool → Array T)
    (hrec : ∀ v pred limit wasBalanced wasPartitioned,
      List.Perm
        (rec v pred limit wasBalanced wasPartitioned).toList
        v.toList)
    (v : Array T) (isLess : T → T → Bool) (pred : Option T)
    (limit len : ℕ) (wasBalanced wasPartitioned : Bool)
    (pivot : ℕ) (hpivot : pivot < v.size) :
    List.Perm
      (recursePred rec v isLess pred limit len
        wasBalanced wasPartitioned pivot).toList
      v.toList := by
  cases pred with
  | none =>
      simp only [recursePred]
      exact recursePartition_perm contracts rec hrec
        v isLess none limit len pivot hpivot
  | some p =>
      simp only [recursePred]
      split
      · exact partitionEqual_branch_perm contracts
          v pivot isLess hpivot _
          (hrec _ _ _ _ _)
      · exact recursePartition_perm contracts rec hrec
          v isLess (some p) limit len pivot hpivot

private theorem recurseAfterPivot_perm
    (contracts : DriverContracts T)
    (rec : Array T → Option T → ℕ → Bool → Bool → Array T)
    (hrec : ∀ v pred limit wasBalanced wasPartitioned,
      List.Perm
        (rec v pred limit wasBalanced wasPartitioned).toList
        v.toList)
    (v : Array T) (isLess : T → T → Bool) (pred : Option T)
    (limit len : ℕ) (wasBalanced wasPartitioned likelySorted : Bool)
    (pivot : ℕ) (hpivot : pivot < v.size) :
    List.Perm
      (recurseAfterPivot rec v isLess pred limit len
        wasBalanced wasPartitioned likelySorted pivot).toList
      v.toList := by
  cases wasBalanced <;> cases wasPartitioned <;> cases likelySorted
  all_goals
    simp only [recurseAfterPivot, Bool.false_and, Bool.true_and,
      if_true]
  all_goals
    first
    | exact recursePred_perm contracts rec hrec
        v isLess pred limit len _ _ pivot hpivot
    | skip
  generalize hpartial :
    partialInsertionSort v isLess = partialResult
  rcases partialResult with ⟨sorted, v2⟩
  have hpartialPerm :=
    contracts.partialInsertionSort_perm v isLess
  rw [hpartial] at hpartialPerm
  dsimp only at hpartialPerm
  split
  · exact hpartialPerm
  · have hsize : v2.size = v.size :=
      size_eq_of_perm hpartialPerm
    exact
      (recursePred_perm contracts rec hrec
        v2 isLess pred limit len true true
        pivot (by omega)).trans hpartialPerm

private theorem recurseChoose_perm
    (contracts : DriverContracts T)
    (rec : Array T → Option T → ℕ → Bool → Bool → Array T)
    (hrec : ∀ v pred limit wasBalanced wasPartitioned,
      List.Perm
        (rec v pred limit wasBalanced wasPartitioned).toList
        v.toList)
    (v : Array T) (isLess : T → T → Bool) (pred : Option T)
    (limit len : ℕ) (wasBalanced wasPartitioned : Bool)
    (hsize : 0 < v.size) :
    List.Perm
      (recurseChoose rec v isLess pred limit len
        wasBalanced wasPartitioned).toList
      v.toList := by
  unfold recurseChoose
  generalize hchoose : choosePivot v isLess = result
  rcases result with ⟨⟨pivot, likelySorted⟩, v1⟩
  have hchoosePerm := contracts.choosePivot_perm v isLess
  rw [hchoose] at hchoosePerm
  dsimp only at hchoosePerm
  have hpivot := contracts.choosePivot_bound v isLess hsize
  rw [hchoose] at hpivot
  dsimp only at hpivot
  exact
    (recurseAfterPivot_perm contracts rec hrec
      v1 isLess pred limit len wasBalanced wasPartitioned
      likelySorted pivot hpivot).trans hchoosePerm

private theorem recurseLong_perm
    (contracts : DriverContracts T)
    (rec : Array T → Option T → ℕ → Bool → Bool → Array T)
    (hrec : ∀ v pred limit wasBalanced wasPartitioned,
      List.Perm
        (rec v pred limit wasBalanced wasPartitioned).toList
        v.toList)
    (v : Array T) (isLess : T → T → Bool) (pred : Option T)
    (limit len : ℕ) (wasBalanced wasPartitioned : Bool)
    (hsize : 0 < v.size) :
    List.Perm
      (recurseLong rec v isLess pred limit len
        wasBalanced wasPartitioned).toList
      v.toList := by
  cases wasBalanced with
  | false =>
      simp only [recurseLong, Bool.not_false, ↓reduceIte]
      have hbreak := contracts.breakPatterns_perm v
      have hbreakSize : 0 < (breakPatterns v).size := by
        have := size_eq_of_perm hbreak
        omega
      exact
        (recurseChoose_perm contracts rec hrec
          (breakPatterns v) isLess pred (limit - 1) len
          false wasPartitioned hbreakSize).trans hbreak
  | true =>
      simp only [recurseLong, Bool.not_true]
      exact recurseChoose_perm contracts rec hrec
        v isLess pred limit len true wasPartitioned hsize

private theorem recurseStep_perm
    (contracts : DriverContracts T)
    (rec : Array T → Option T → ℕ → Bool → Bool → Array T)
    (hrec : ∀ v pred limit wasBalanced wasPartitioned,
      List.Perm
        (rec v pred limit wasBalanced wasPartitioned).toList
        v.toList)
    (v : Array T) (isLess : T → T → Bool) (pred : Option T)
    (limit : ℕ) (wasBalanced wasPartitioned : Bool) :
    List.Perm
      (recurseStep rec v isLess pred limit
        wasBalanced wasPartitioned).toList
      v.toList := by
  unfold recurseStep
  by_cases hsmall : v.size ≤ 20
  · simp only [hsmall, ↓reduceIte]
    exact contracts.insertionSort_perm v isLess
  · simp only [hsmall, ↓reduceIte]
    by_cases hlimit : limit == 0
    · simp only [hlimit]
      exact contracts.heapsort_perm v isLess
    · simp only [hlimit]
      exact recurseLong_perm contracts rec hrec
        v isLess pred limit v.size wasBalanced wasPartitioned
        (by omega)

theorem recurse_perm_of_contracts (contracts : DriverContracts T) :
    ∀ (fuel : ℕ) (v : Array T) (isLess : T → T → Bool)
      (pred : Option T) (limit : ℕ) (wasBalanced wasPartitioned : Bool),
      List.Perm
        (recurse fuel v isLess pred limit wasBalanced wasPartitioned).toList
        v.toList := by
  intro fuel
  induction fuel with
  | zero =>
      intro v isLess pred limit wasBalanced wasPartitioned
      exact contracts.heapsort_perm v isLess
  | succ fuel ih =>
      intro v isLess pred limit wasBalanced wasPartitioned
      rw [recurse]
      exact recurseStep_perm contracts
        (fun v pred limit wasBalanced wasPartitioned =>
          recurse fuel v isLess pred limit wasBalanced wasPartitioned)
        (fun v pred limit wasBalanced wasPartitioned =>
          ih v isLess pred limit wasBalanced wasPartitioned)
        v isLess pred limit wasBalanced wasPartitioned

theorem quicksort_perm_of_contracts
    (contracts : DriverContracts T)
    (v : Array T) (isLess : T → T → Bool) :
    List.Perm (quicksort v isLess).toList v.toList := by
  unfold quicksort
  split
  · exact List.Perm.refl _
  · exact recurse_perm_of_contracts contracts
      (v.size + 1) v isLess none
      (Nat.log2 v.size + 1) true true

variable {T : Type} [Inhabited T]

private theorem blocks_count_contract
    (hblocks : PartitionInBlocksPermContract (T := T)) :
    PartitionInBlocksCountContract (T := T) := by
  intro array pivot isLess
  exact (hblocks array pivot isLess).1

def driverContractsOfBlocksContract
    (hblocks : PartitionInBlocksPermContract (T := T)) :
    DriverContracts T where
  insertionSort_perm := insertionSort_perm
  heapsort_perm := heapsort_perm
  breakPatterns_perm := breakPatterns_perm
  choosePivot_perm := choosePivot_perm
  choosePivot_bound := choosePivot_bound
  partialInsertionSort_perm := partialInsertionSort_perm
  partitionEqual_perm := partitionEqual_perm
  partitionEqual_bound := partitionEqual_bound
  partitionP_perm := partitionP_perm_of_blocks_contract hblocks
  partitionP_bound :=
    partitionP_bound_of_blocks_count
      (blocks_count_contract hblocks)

theorem quicksort_perm
    (array : Array T) (isLess : T → T → Bool) :
    List.Perm (quicksort array isLess).toList array.toList :=
  quicksort_perm_of_contracts
    (driverContractsOfBlocksContract partitionInBlocks_perm_contract)
    array isLess

/-! ## Ordering correctness of the recursive driver -/

/-- The predecessor carried by pdqsort is a lower bound for the current
recursive slice. -/
def PredecessorBound
    (key : T → ℕ) (array : Array T) : Option T → Prop
  | none => True
  | some predecessor => KeysGE key array.toList (key predecessor)

omit [Inhabited T] in
theorem PredecessorBound.perm
    (key : T → ℕ) {left right : Array T} {pred : Option T}
    (hperm : left.toList.Perm right.toList)
    (h : PredecessorBound key left pred) :
    PredecessorBound key right pred := by
  cases pred with
  | none => trivial
  | some predecessor =>
      exact KeysGE.perm key hperm h

theorem PredecessorBound.extract
    (key : T → ℕ) (array : Array T) (start stop : ℕ)
    {pred : Option T} (h : PredecessorBound key array pred)
    (hstart : start ≤ stop) (hstop : stop ≤ array.size) :
    PredecessorBound key (array.extract start stop) pred := by
  cases pred with
  | none => trivial
  | some predecessor =>
      exact KeysGE.extract key array start stop (key predecessor)
        h hstart hstop

/-- The two ordering facts not supplied by the recursive partition proof:
heapsort's fallback and the successful nearly-sorted fast path. -/
structure OrderingContracts (T : Type) [Inhabited T] (key : T → ℕ) where
  heapsort_sorted :
    ∀ array, KeySorted key (heapsort array (lessBy key)).toList
  partialInsertionSort_sorted :
    ∀ array, (partialInsertionSort array (lessBy key)).1 = true →
      KeySorted key (partialInsertionSort array (lessBy key)).2.toList

variable {key : T → ℕ}

private def legacyDriverContracts : DriverContracts T :=
  driverContractsOfBlocksContract partitionInBlocks_perm_contract

theorem recurse_perm
    (fuel : ℕ) (array : Array T) (isLess : T → T → Bool)
    (pred : Option T) (limit : ℕ)
    (wasBalanced wasPartitioned : Bool) :
    List.Perm
      (recurse fuel array isLess pred limit
        wasBalanced wasPartitioned).toList
      array.toList :=
  recurse_perm_of_contracts legacyDriverContracts
    fuel array isLess pred limit wasBalanced wasPartitioned

private theorem recursePartition_sorted
    (rec : Array T → Option T → ℕ → Bool → Bool → Array T)
    (hrecSorted : ∀ array pred limit wasBalanced wasPartitioned,
      PredecessorBound key array pred →
      KeySorted key
        (rec array pred limit wasBalanced wasPartitioned).toList)
    (hrecPerm : ∀ array pred limit wasBalanced wasPartitioned,
      List.Perm
        (rec array pred limit wasBalanced wasPartitioned).toList
        array.toList)
    (array : Array T) (pred : Option T) (limit len pivot : ℕ)
    (hpivot : pivot < array.size)
    (hlower : PredecessorBound key array pred) :
    KeySorted key
      (recursePartition rec array (lessBy key) pred limit len pivot).toList := by
  unfold recursePartition
  generalize hpartition :
    partitionP array pivot (lessBy key) = result
  rcases result with ⟨⟨middle, wasPartitioned⟩, partitioned⟩
  dsimp only
  have hpartitionPerm :=
    legacyDriverContracts.partitionP_perm array pivot (lessBy key) hpivot
  have hmiddle :=
    legacyDriverContracts.partitionP_bound array pivot (lessBy key) hpivot
  have hpartitionOrder :=
    partitionP_order array pivot (lessBy key) hpivot
  rw [hpartition] at hpartitionPerm hmiddle hpartitionOrder
  dsimp only at hpartitionPerm hmiddle hpartitionOrder
  let pivotValue := partitioned[middle]!
  let left := partitioned.extract 0 middle
  let right := partitioned.extract (middle + 1) partitioned.size
  have hleftRange : RangeAll partitioned 0 middle
      (fun item => key item ≤ key pivotValue) := by
    intro index hstart hstop
    have hless := hpartitionOrder.1 index hstart hstop
    change lessBy key partitioned[index]! partitioned[middle]! = true at hless
    rw [lessBy_eq_true_iff] at hless
    simpa only [pivotValue] using hless.le
  have hrightRange : RangeAll partitioned (middle + 1) partitioned.size
      (fun item => key pivotValue ≤ key item) := by
    intro index hstart hstop
    have hnotLess := hpartitionOrder.2 index hstart hstop
    change lessBy key partitioned[index]! partitioned[middle]! = false at hnotLess
    rw [lessBy_eq_false_iff] at hnotLess
    simpa only [pivotValue] using hnotLess
  have hleftBound : KeysLE key left.toList (key pivotValue) := by
    apply RangeAll.keysLE_extract key partitioned 0 middle
      (key pivotValue) hleftRange <;> omega
  have hrightBound : KeysGE key right.toList (key pivotValue) := by
    apply RangeAll.keysGE_extract key partitioned (middle + 1)
      partitioned.size (key pivotValue) hrightRange <;> omega
  have hpartitionedLower : PredecessorBound key partitioned pred :=
    PredecessorBound.perm key hpartitionPerm.symm hlower
  have hleftLower : PredecessorBound key left pred := by
    apply PredecessorBound.extract key partitioned 0 middle
      hpartitionedLower <;> omega
  have hleftSorted := hrecSorted left pred limit true true hleftLower
  have hrightSorted (balanced partitionedFlag : Bool) :=
    hrecSorted right (some pivotValue) limit balanced partitionedFlag hrightBound
  have hleftOutputBound (balanced partitionedFlag : Bool) :
      KeysLE key
        (rec left pred limit balanced partitionedFlag).toList
        (key pivotValue) :=
    KeysLE.perm key
      (hrecPerm left pred limit balanced partitionedFlag).symm
      hleftBound
  have hrightOutputBound (balanced partitionedFlag : Bool) :
      KeysGE key
        (rec right (some pivotValue) limit balanced partitionedFlag).toList
        (key pivotValue) :=
    KeysGE.perm key
      (hrecPerm right (some pivotValue) limit balanced partitionedFlag).symm
      hrightBound
  split
  · simp only [Array.toList_append, List.append_assoc]
    exact KeySorted.append_pivot key _ pivotValue _
      hleftSorted (hrightSorted _ _)
      (hleftOutputBound _ _) (hrightOutputBound _ _)
  · simp only [Array.toList_append, List.append_assoc]
    exact KeySorted.append_pivot key _ pivotValue _
      (hrecSorted left pred limit _ _ hleftLower)
      (hrightSorted true true)
      (hleftOutputBound _ _) (hrightOutputBound true true)

private theorem recursePred_sorted
    (rec : Array T → Option T → ℕ → Bool → Bool → Array T)
    (hrecSorted : ∀ array pred limit wasBalanced wasPartitioned,
      PredecessorBound key array pred →
      KeySorted key
        (rec array pred limit wasBalanced wasPartitioned).toList)
    (hrecPerm : ∀ array pred limit wasBalanced wasPartitioned,
      List.Perm
        (rec array pred limit wasBalanced wasPartitioned).toList
        array.toList)
    (array : Array T) (pred : Option T) (limit len : ℕ)
    (wasBalanced wasPartitioned : Bool) (pivot : ℕ)
    (hpivot : pivot < array.size)
    (hlower : PredecessorBound key array pred) :
    KeySorted key
      (recursePred rec array (lessBy key) pred limit len
        wasBalanced wasPartitioned pivot).toList := by
  cases pred with
  | none =>
      simp only [recursePred]
      exact recursePartition_sorted rec hrecSorted hrecPerm
        array none limit len pivot hpivot hlower
  | some predecessor =>
      simp only [recursePred]
      split
      next hfast =>
        have hpivotLower : key predecessor ≤ key array[pivot]! :=
          KeysGE.get! key array (key predecessor) pivot hlower hpivot
        have hpivotUpper : key array[pivot]! ≤ key predecessor := by
          change (!lessBy key predecessor array[pivot]!) = true at hfast
          cases hcomparison : lessBy key predecessor array[pivot]! with
          | false =>
              rw [lessBy_eq_false_iff] at hcomparison
              exact hcomparison
          | true => simp_all
        have hpivotKey : key array[pivot]! = key predecessor := by omega
        have hpartitionOrder := partitionEqual_ordered
          array pivot key hpivot (by
            intro item hitem
            rw [hpivotKey]
            exact hlower item hitem)
        have hpartitionPerm :=
          legacyDriverContracts.partitionEqual_perm
            array pivot (lessBy key) hpivot
        have hpartitionBounds :=
          legacyDriverContracts.partitionEqual_bound
            array pivot (lessBy key) hpivot
        generalize hpartition :
          partitionEqual array pivot (lessBy key) = result
        rcases result with ⟨middle, partitioned⟩
        rw [hpartition] at hpartitionOrder hpartitionPerm hpartitionBounds
        dsimp only at hpartitionOrder hpartitionPerm hpartitionBounds ⊢
        let head := partitioned.extract 0 middle
        let tail := partitioned.extract middle partitioned.size
        have hheadEqual : ∀ item ∈ head.toList,
            key item = key predecessor := by
          intro item hitem
          have hmember := hpartitionOrder.1.forall_mem_extract
            (by omega) (by omega) item hitem
          exact hmember.trans hpivotKey
        have hheadSorted : KeySorted key head.toList :=
          KeySorted.of_constant key head.toList (key predecessor) hheadEqual
        have hheadBound : KeysLE key head.toList (key predecessor) := by
          intro item hitem
          exact (hheadEqual item hitem).le
        have htailBound : KeysGE key tail.toList (key predecessor) := by
          apply RangeAll.keysGE_extract key partitioned middle
            partitioned.size (key predecessor) _ (by omega) (by omega)
          intro index hstart hstop
          have hgreater := hpartitionOrder.2 index hstart hstop
          omega
        have htailSorted := hrecSorted tail (some predecessor) limit
          wasBalanced wasPartitioned htailBound
        have htailOutputBound : KeysGE key
            (rec tail (some predecessor) limit
              wasBalanced wasPartitioned).toList
            (key predecessor) :=
          KeysGE.perm key
            (hrecPerm tail (some predecessor) limit
              wasBalanced wasPartitioned).symm htailBound
        simp only [Array.toList_append]
        exact KeySorted.append key head.toList _ hheadSorted htailSorted (by
          intro leftItem hleftItem rightItem hrightItem
          exact (hheadBound leftItem hleftItem).trans
            (htailOutputBound rightItem hrightItem))
      next _ =>
        exact recursePartition_sorted rec hrecSorted hrecPerm
          array (some predecessor) limit len pivot hpivot hlower

private theorem recurseAfterPivot_sorted
    (contracts : OrderingContracts T key)
    (rec : Array T → Option T → ℕ → Bool → Bool → Array T)
    (hrecSorted : ∀ array pred limit wasBalanced wasPartitioned,
      PredecessorBound key array pred →
      KeySorted key
        (rec array pred limit wasBalanced wasPartitioned).toList)
    (hrecPerm : ∀ array pred limit wasBalanced wasPartitioned,
      List.Perm
        (rec array pred limit wasBalanced wasPartitioned).toList
        array.toList)
    (array : Array T) (pred : Option T) (limit len : ℕ)
    (wasBalanced wasPartitioned likelySorted : Bool) (pivot : ℕ)
    (hpivot : pivot < array.size)
    (hlower : PredecessorBound key array pred) :
    KeySorted key
      (recurseAfterPivot rec array (lessBy key) pred limit len
        wasBalanced wasPartitioned likelySorted pivot).toList := by
  cases wasBalanced <;> cases wasPartitioned <;> cases likelySorted
  all_goals
    simp only [recurseAfterPivot, Bool.false_and, Bool.true_and,
      if_true]
  all_goals
    first
    | exact recursePred_sorted rec hrecSorted hrecPerm
        array pred limit len _ _ pivot hpivot hlower
    | skip
  generalize hpartial :
    partialInsertionSort array (lessBy key) = partialResult
  rcases partialResult with ⟨sorted, partiallySorted⟩
  split
  next hsorted =>
    have hresult := contracts.partialInsertionSort_sorted array
    rw [hpartial] at hresult
    exact hresult hsorted
  next _ =>
    have hpartialPerm :=
      legacyDriverContracts.partialInsertionSort_perm
        array (lessBy key)
    rw [hpartial] at hpartialPerm
    dsimp only at hpartialPerm
    have hpartialLower :
        PredecessorBound key partiallySorted pred :=
      PredecessorBound.perm key hpartialPerm.symm hlower
    have hpartialSize : partiallySorted.size = array.size :=
      size_eq_of_perm hpartialPerm
    exact recursePred_sorted rec hrecSorted hrecPerm
      partiallySorted pred limit len true true pivot
      (by omega) hpartialLower

private theorem recurseChoose_sorted
    (contracts : OrderingContracts T key)
    (rec : Array T → Option T → ℕ → Bool → Bool → Array T)
    (hrecSorted : ∀ array pred limit wasBalanced wasPartitioned,
      PredecessorBound key array pred →
      KeySorted key
        (rec array pred limit wasBalanced wasPartitioned).toList)
    (hrecPerm : ∀ array pred limit wasBalanced wasPartitioned,
      List.Perm
        (rec array pred limit wasBalanced wasPartitioned).toList
        array.toList)
    (array : Array T) (pred : Option T) (limit len : ℕ)
    (wasBalanced wasPartitioned : Bool)
    (hsize : 0 < array.size)
    (hlower : PredecessorBound key array pred) :
    KeySorted key
      (recurseChoose rec array (lessBy key) pred limit len
        wasBalanced wasPartitioned).toList := by
  unfold recurseChoose
  generalize hchoose : choosePivot array (lessBy key) = result
  rcases result with ⟨⟨pivot, likelySorted⟩, chosen⟩
  have hchoosePerm :=
    legacyDriverContracts.choosePivot_perm array (lessBy key)
  have hpivot :=
    legacyDriverContracts.choosePivot_bound array (lessBy key) hsize
  rw [hchoose] at hchoosePerm hpivot
  dsimp only at hchoosePerm hpivot ⊢
  have hchosenLower : PredecessorBound key chosen pred :=
    PredecessorBound.perm key hchoosePerm.symm hlower
  exact recurseAfterPivot_sorted contracts rec hrecSorted hrecPerm
    chosen pred limit len wasBalanced wasPartitioned likelySorted pivot
    hpivot hchosenLower

private theorem recurseLong_sorted
    (contracts : OrderingContracts T key)
    (rec : Array T → Option T → ℕ → Bool → Bool → Array T)
    (hrecSorted : ∀ array pred limit wasBalanced wasPartitioned,
      PredecessorBound key array pred →
      KeySorted key
        (rec array pred limit wasBalanced wasPartitioned).toList)
    (hrecPerm : ∀ array pred limit wasBalanced wasPartitioned,
      List.Perm
        (rec array pred limit wasBalanced wasPartitioned).toList
        array.toList)
    (array : Array T) (pred : Option T) (limit len : ℕ)
    (wasBalanced wasPartitioned : Bool)
    (hsize : 0 < array.size)
    (hlower : PredecessorBound key array pred) :
    KeySorted key
      (recurseLong rec array (lessBy key) pred limit len
        wasBalanced wasPartitioned).toList := by
  cases wasBalanced with
  | false =>
      simp only [recurseLong, Bool.not_false, ↓reduceIte]
      have hbreak := legacyDriverContracts.breakPatterns_perm array
      have hbreakSize : 0 < (breakPatterns array).size := by
        have := size_eq_of_perm hbreak
        omega
      have hbreakLower :
          PredecessorBound key (breakPatterns array) pred :=
        PredecessorBound.perm key hbreak.symm hlower
      exact recurseChoose_sorted contracts rec hrecSorted hrecPerm
        (breakPatterns array) pred (limit - 1) len false wasPartitioned
        hbreakSize hbreakLower
  | true =>
      simp only [recurseLong, Bool.not_true]
      exact recurseChoose_sorted contracts rec hrecSorted hrecPerm
        array pred limit len true wasPartitioned hsize hlower

private theorem recurseStep_sorted
    (contracts : OrderingContracts T key)
    (rec : Array T → Option T → ℕ → Bool → Bool → Array T)
    (hrecSorted : ∀ array pred limit wasBalanced wasPartitioned,
      PredecessorBound key array pred →
      KeySorted key
        (rec array pred limit wasBalanced wasPartitioned).toList)
    (hrecPerm : ∀ array pred limit wasBalanced wasPartitioned,
      List.Perm
        (rec array pred limit wasBalanced wasPartitioned).toList
        array.toList)
    (array : Array T) (pred : Option T) (limit : ℕ)
    (wasBalanced wasPartitioned : Bool)
    (hlower : PredecessorBound key array pred) :
    KeySorted key
      (recurseStep rec array (lessBy key) pred limit
        wasBalanced wasPartitioned).toList := by
  unfold recurseStep
  by_cases hsmall : array.size ≤ 20
  · simp only [hsmall, ↓reduceIte]
    exact insertionSort_sorted array key
  · simp only [hsmall, ↓reduceIte]
    by_cases hlimit : limit == 0
    · simp only [hlimit]
      exact contracts.heapsort_sorted array
    · simp only [hlimit]
      exact recurseLong_sorted contracts rec hrecSorted hrecPerm
        array pred limit array.size wasBalanced wasPartitioned
        (by omega) hlower

theorem recurse_sorted_of_contracts
    (contracts : OrderingContracts T key) :
    ∀ (fuel : ℕ) (array : Array T) (pred : Option T) (limit : ℕ)
      (wasBalanced wasPartitioned : Bool),
      PredecessorBound key array pred →
      KeySorted key
        (recurse fuel array (lessBy key) pred limit
          wasBalanced wasPartitioned).toList := by
  intro fuel
  induction fuel with
  | zero =>
      intro array pred limit wasBalanced wasPartitioned hlower
      exact contracts.heapsort_sorted array
  | succ fuel inductionHypothesis =>
      intro array pred limit wasBalanced wasPartitioned hlower
      rw [recurse]
      exact recurseStep_sorted contracts
        (fun array pred limit wasBalanced wasPartitioned =>
          recurse fuel array (lessBy key) pred limit
            wasBalanced wasPartitioned)
        (fun array pred limit wasBalanced wasPartitioned =>
          inductionHypothesis array pred limit
            wasBalanced wasPartitioned)
        (fun array pred limit wasBalanced wasPartitioned =>
          recurse_perm fuel array (lessBy key) pred limit
            wasBalanced wasPartitioned)
        array pred limit wasBalanced wasPartitioned hlower

theorem quicksort_sorted_of_contracts
    (contracts : OrderingContracts T key) (array : Array T) :
    KeySorted key (quicksort array (lessBy key)).toList := by
  unfold quicksort
  split
  next hzero =>
    have hsize : array.size = 0 := by simpa using hzero
    have hempty : array.toList = [] := by
      apply List.eq_nil_of_length_eq_zero
      simpa using hsize
    rw [hempty]
    exact KeySorted.nil key
  next _ =>
    exact recurse_sorted_of_contracts contracts
      (array.size + 1) array none (Nat.log2 array.size + 1)
      true true trivial

end Pdqsort

/-! ## Column allocations (`v1/strategy.rs` `Allocations` / `CircuitAllocations`)

Per-column set of disjoint `[start, start+length)` allocated intervals, kept sorted by
`start` (Rust `BTreeSet<AllocatedRegion>` ordered by `start`). -/

/-- Disjointness of two half-open row intervals. -/
def RowIntervalsDisjoint
    (leftStart leftLength rightStart rightLength : ℕ) : Prop :=
  leftStart + leftLength ≤ rightStart ∨
    rightStart + rightLength ≤ leftStart

/-- A column's allocated intervals `(start, length)`, sorted by `start`, disjoint. -/
abbrev Allocations := Array (ℕ × ℕ)

/-- List-level core of sorted interval insertion. -/
def Allocations.insertList (start length : ℕ) :
    List (ℕ × ℕ) → List (ℕ × ℕ)
  | [] => [(start, length)]
  | head :: rest =>
      if start < head.1 then
        (start, length) :: head :: rest
      else
        head :: insertList start length rest

/-- Insert an allocated interval keeping the sort by `start` (`BTreeSet::insert`). -/
def Allocations.insert (a : Allocations) (start len : ℕ) : Allocations :=
  (insertList start len a.toList).toArray

/-- Strict row ordering carried by adjacent allocated intervals. -/
def Allocations.IntervalBefore (left right : ℕ × ℕ) : Prop :=
  left.1 + left.2 ≤ right.1

/-- The representation invariant of a column's allocation set. -/
def Allocations.Valid (allocations : Allocations) : Prop :=
  allocations.toList.Pairwise IntervalBefore

/-- A proposed interval is disjoint from every existing allocation. -/
def Allocations.Fits
    (allocations : Allocations) (start length : ℕ) : Prop :=
  ∀ allocated ∈ allocations.toList,
    RowIntervalsDisjoint start length allocated.1 allocated.2

private theorem Allocations.mem_insertList
    (items : List (ℕ × ℕ)) (start length : ℕ) :
    (start, length) ∈ insertList start length items := by
  induction items with
  | nil => simp [insertList]
  | cons head rest inductionHypothesis =>
      simp only [insertList]
      split <;> simp_all

private theorem Allocations.mem_insertList_of_mem
    (items : List (ℕ × ℕ)) (start length : ℕ)
    {allocated : ℕ × ℕ} (hallocated : allocated ∈ items) :
    allocated ∈ insertList start length items := by
  induction items with
  | nil => simp at hallocated
  | cons head rest inductionHypothesis =>
      simp only [insertList]
      split
      · simp_all
      · simp only [List.mem_cons] at hallocated ⊢
        exact hallocated.imp_right inductionHypothesis

private theorem Allocations.mem_insertList_iff
    (items : List (ℕ × ℕ)) (start length : ℕ)
    (item : ℕ × ℕ) :
    item ∈ insertList start length items ↔
      item = (start, length) ∨ item ∈ items := by
  induction items with
  | nil => simp [insertList]
  | cons head rest inductionHypothesis =>
      simp only [insertList]
      split <;> simp_all [or_left_comm]

private theorem Allocations.valid_head_before
    {head : ℕ × ℕ} {rest : List (ℕ × ℕ)}
    (hvalid : (head :: rest).Pairwise IntervalBefore)
    {item : ℕ × ℕ} (hitem : item ∈ rest) :
    IntervalBefore head item := by
  exact List.pairwise_cons.mp hvalid |>.1 item hitem

private theorem Allocations.valid_insertList
    (items : List (ℕ × ℕ)) (start length : ℕ)
    (hvalid : items.Pairwise IntervalBefore)
    (hfits : ∀ allocated ∈ items,
      RowIntervalsDisjoint start length allocated.1 allocated.2)
    (hlength : 0 < length) :
    (insertList start length items).Pairwise IntervalBefore := by
  induction items with
  | nil => simp [insertList]
  | cons head rest inductionHypothesis =>
      simp only [insertList]
      split
      next hlt =>
        rw [List.pairwise_cons]
        constructor
        · intro item hitem
          have hdisjoint := hfits item (by simp_all)
          rcases hdisjoint with hbefore | hafter
          · exact hbefore
          · have hstartLe : head.1 ≤ item.1 := by
              simp only [List.mem_cons] at hitem
              rcases hitem with rfl | hrest
              · exact le_rfl
              · exact (Nat.le_add_right head.1 head.2).trans
                  (valid_head_before hvalid hrest)
            omega
        · exact hvalid
      next hge =>
        rw [List.pairwise_cons] at hvalid ⊢
        constructor
        · intro item hitem
          by_cases hnew : item = (start, length)
          · subst item
            have hheadFits := hfits head (by simp)
            rcases hheadFits with hnewBefore | hheadBefore
            · omega
            · exact hheadBefore
          · rw [mem_insertList_iff] at hitem
            exact hvalid.1 item (hitem.resolve_left hnew)
        · apply inductionHypothesis hvalid.2
          intro allocated hallocated
          exact hfits allocated (by simp [hallocated])

/-- Inserting a positive fitting interval preserves sorted disjointness. -/
theorem Allocations.Valid.insert
    (allocations : Allocations) (start length : ℕ)
    (hvalid : allocations.Valid)
    (hfits : allocations.Fits start length)
    (hlength : 0 < length) :
    (allocations.insert start length).Valid := by
  simpa [Valid, insert] using
    valid_insertList allocations.toList start length hvalid hfits hlength

theorem Allocations.mem_insert
    (allocations : Allocations) (start length : ℕ) :
    (start, length) ∈ (allocations.insert start length).toList := by
  simpa [insert] using mem_insertList allocations.toList start length

theorem Allocations.mem_insert_iff
    (allocations : Allocations) (start length : ℕ)
    (interval : ℕ × ℕ) :
    interval ∈ (allocations.insert start length).toList ↔
      interval = (start, length) ∨ interval ∈ allocations.toList := by
  simpa [insert] using
    mem_insertList_iff allocations.toList start length interval

theorem Allocations.mem_insert_of_mem
    (allocations : Allocations) (start length : ℕ)
    {allocated : ℕ × ℕ} (hallocated : allocated ∈ allocations.toList) :
    allocated ∈ (allocations.insert start length).toList := by
  simpa [insert] using
    mem_insertList_of_mem allocations.toList start length hallocated

/-- `unbounded_interval_start` (`strategy.rs:53-59`): the row after the last allocated
interval, or 0. -/
def Allocations.unboundedStart (a : Allocations) : ℕ :=
  match a.toList.getLast? with
  | some (s, l) => s + l
  | none => 0

/-- Recursive core of `free_intervals`. The second component is the first row after
all processed allocations; the first contains the bounded gaps encountered so far. -/
def Allocations.scanFreeIntervals (endBound : Option ℕ) :
    List (ℕ × ℕ) → ℕ → List (ℕ × Option ℕ) × ℕ
  | [], row => ([], row)
  | (regionStart, regionLength) :: rest, row =>
      let past : Bool := match endBound with
        | some endRow => decide (regionStart ≥ endRow)
        | none => false
      if !past then
        let tail := scanFreeIntervals endBound rest
          (max row (regionStart + regionLength))
        (if row < regionStart then
            (row, some regionStart) :: tail.1
          else tail.1,
          tail.2)
      else
        scanFreeIntervals endBound rest row

/-- `free_intervals(start, end)` (`strategy.rs:64-98`): the unallocated intervals of this
column intersecting `[start, end)`, as `(spaceStart, spaceEnd?)` (`end? = none` unbounded).
The recursive scan is extensionally the Rust iterator: a region with `start ≥ end` is
skipped without advancing `row`, and the final item emits `[row, end)` when
`end = none ∨ row < end`. -/
def Allocations.freeIntervals (a : Allocations) (start : ℕ) (endBound : Option ℕ) :
    List (ℕ × Option ℕ) :=
  let result := scanFreeIntervals endBound a.toList start
  match endBound with
  | some endRow =>
      if result.2 < endRow then
        result.1 ++ [(result.2, some endRow)]
      else result.1
  | none => result.1 ++ [(result.2, none)]

/-- A candidate interval lies within a free-space descriptor. -/
def Allocations.SpaceAllows
    (space : ℕ × Option ℕ) (start length : ℕ) : Prop :=
  space.1 ≤ start ∧
    ∀ stop, space.2 = some stop → start + length ≤ stop

/-- If the requested interval already fits at the search boundary, the scan either
publishes that boundary as its first free interval or reaches the final free interval
without advancing it. -/
private theorem Allocations.scanFreeIntervals_head_of_fits
    (items : List (ℕ × ℕ)) (start length : ℕ)
    (endBound : Option ℕ)
    (hvalid : items.Pairwise IntervalBefore)
    (hfits : ∀ allocated ∈ items,
      RowIntervalsDisjoint start length allocated.1 allocated.2)
    (hlength : 0 < length)
    (hbound : ∀ stop, endBound = some stop → start + length ≤ stop) :
    let result := scanFreeIntervals endBound items start
    (∃ stop rest,
      result.1 = (start, stop) :: rest ∧
        SpaceAllows (start, stop) start length) ∨
      (result.1 = [] ∧ result.2 = start) := by
  induction items with
  | nil =>
      exact Or.inr ⟨rfl, rfl⟩
  | cons head rest inductionHypothesis =>
      have hrestValid := List.pairwise_cons.mp hvalid |>.2
      have hrestFits : ∀ allocated ∈ rest,
          RowIntervalsDisjoint start length allocated.1 allocated.2 := by
        intro allocated hallocated
        exact hfits allocated (by simp [hallocated])
      have hheadFits := hfits head (by simp)
      rcases hheadFits with hcandidateBefore | hheadBefore
      · cases endBound with
        | none =>
            simp only [scanFreeIntervals, Bool.not_false, ↓reduceIte]
            have hgap : start < head.1 := by omega
            rw [if_pos hgap]
            exact Or.inl ⟨some head.1,
              (scanFreeIntervals none rest
                (max start (head.1 + head.2))).1,
              rfl, ⟨le_rfl, by
                intro stop hstop
                simp only [Option.some.injEq] at hstop
                subst stop
                exact hcandidateBefore⟩⟩
        | some endRow =>
            by_cases hpast : endRow ≤ head.1
            · simp only [scanFreeIntervals, hpast, decide_true,
                Bool.not_true]
              exact inductionHypothesis hrestValid hrestFits
            · simp only [scanFreeIntervals, hpast, decide_false,
                Bool.not_false, ↓reduceIte]
              have hgap : start < head.1 := by omega
              rw [if_pos hgap]
              exact Or.inl ⟨some head.1,
                (scanFreeIntervals (some endRow) rest
                  (max start (head.1 + head.2))).1,
                rfl, ⟨le_rfl, by
                  intro stop hstop
                  simp only [Option.some.injEq] at hstop
                  subst stop
                  exact hcandidateBefore⟩⟩
      · have hheadEnd : head.1 + head.2 ≤ start := hheadBefore
        have hnotPast : ∀ endRow, endBound = some endRow →
            ¬ endRow ≤ head.1 := by
          intro endRow hend hpast
          have := hbound endRow hend
          omega
        cases endBound with
        | none =>
            simp only [scanFreeIntervals, Bool.not_false, ↓reduceIte]
            have hnoGap : ¬ start < head.1 := by omega
            rw [if_neg hnoGap, max_eq_left hheadEnd]
            exact inductionHypothesis hrestValid hrestFits
        | some endRow =>
            have hpast : ¬ endRow ≤ head.1 := hnotPast endRow rfl
            simp only [scanFreeIntervals, hpast, decide_false,
              Bool.not_false, ↓reduceIte]
            have hnoGap : ¬ start < head.1 := by omega
            rw [if_neg hnoGap, max_eq_left hheadEnd]
            exact inductionHypothesis hrestValid hrestFits

/-- A fitting interval at the requested start is the first interval enumerated by
`freeIntervals`. -/
theorem Allocations.freeIntervals_starts_with_of_fits
    (allocations : Allocations) (start length : ℕ)
    (endBound : Option ℕ)
    (hvalid : allocations.Valid)
    (hfits : allocations.Fits start length)
    (hlength : 0 < length)
    (hbound : ∀ stop, endBound = some stop → start + length ≤ stop) :
    ∃ stop rest,
      allocations.freeIntervals start endBound = (start, stop) :: rest ∧
        SpaceAllows (start, stop) start length := by
  have hscan := scanFreeIntervals_head_of_fits allocations.toList
    start length endBound (by simpa [Valid] using hvalid) hfits hlength hbound
  cases endBound with
  | none =>
      rcases hscan with ⟨stop, rest, hresult, hallows⟩ | ⟨hresult, hend⟩
      · refine ⟨stop, rest ++ [((scanFreeIntervals none
            allocations.toList start).2, none)], ?_, hallows⟩
        simp only [freeIntervals, hresult, List.cons_append]
      · refine ⟨none, [], ?_, ⟨le_rfl, by simp⟩⟩
        simp [freeIntervals, hresult, hend]
  | some endRow =>
      have hstartEnd : start < endRow := by
        have := hbound endRow rfl
        omega
      rcases hscan with ⟨stop, rest, hresult, hallows⟩ | ⟨hresult, hend⟩
      · simp only [freeIntervals, hresult]
        split <;> rename_i hfinal
        · exact ⟨stop, rest ++
            [((scanFreeIntervals (some endRow)
              allocations.toList start).2, some endRow)], by
              simp only [List.cons_append], hallows⟩
        · exact ⟨stop, rest, rfl, hallows⟩
      · have hfinal :
            (scanFreeIntervals (some endRow)
              allocations.toList start).2 < endRow := by
          rw [hend]
          exact hstartEnd
        refine ⟨some endRow, [], ?_, ⟨le_rfl, ?_⟩⟩
        · simp [freeIntervals, hresult, hend, hstartEnd]
        · intro stop hstop
          have : stop = endRow := Option.some.inj hstop.symm
          subst stop
          exact hbound endRow rfl

private def Allocations.EndsBefore
    (items : List (ℕ × ℕ)) (row : ℕ) : Prop :=
  ∀ item ∈ items, item.1 + item.2 ≤ row

private theorem Allocations.valid_head_start_le
    {head : ℕ × ℕ} {rest : List (ℕ × ℕ)}
    (hvalid : (head :: rest).Pairwise IntervalBefore)
    {item : ℕ × ℕ} (hitem : item ∈ head :: rest) :
    head.1 ≤ item.1 := by
  simp only [List.mem_cons] at hitem
  rcases hitem with rfl | hrest
  · exact le_rfl
  · exact (Nat.le_add_right head.1 head.2).trans
      (List.pairwise_cons.mp hvalid |>.1 item hrest)

private theorem Allocations.valid_suffix
    {previous items : List (ℕ × ℕ)}
    (hvalid : (previous ++ items).Pairwise IntervalBefore) :
    items.Pairwise IntervalBefore := by
  exact (List.pairwise_append.mp hvalid).2.1

private theorem Allocations.fits_of_before_and_after
    {previous suffix : List (ℕ × ℕ)} {boundary start length : ℕ}
    (hprevious : EndsBefore previous boundary)
    (hstart : boundary ≤ start)
    (hsuffix : ∀ item ∈ suffix, start + length ≤ item.1) :
    ∀ item ∈ previous ++ suffix,
      RowIntervalsDisjoint start length item.1 item.2 := by
  intro item hitem
  rw [List.mem_append] at hitem
  rcases hitem with hpast | hsuffixItem
  · exact Or.inr ((hprevious item hpast).trans hstart)
  · exact Or.inl (hsuffix item hsuffixItem)

private theorem Allocations.scanFreeIntervals_fst_eq_nil_of_starts_ge
    (items : List (ℕ × ℕ)) (row endRow : ℕ)
    (hstarts : ∀ item ∈ items, endRow ≤ item.1) :
    (scanFreeIntervals (some endRow) items row).1 = [] := by
  induction items with
  | nil => rfl
  | cons head rest inductionHypothesis =>
      have hhead := hstarts head (by simp)
      simp only [scanFreeIntervals, hhead, decide_true, Bool.not_true]
      apply inductionHypothesis
      intro item hitem
      exact hstarts item (by simp [hitem])

private theorem Allocations.endsBefore_append_singleton
    {previous : List (ℕ × ℕ)} {head : ℕ × ℕ} {row : ℕ}
    (hprevious : EndsBefore previous row) :
    EndsBefore (previous ++ [head])
      (max row (head.1 + head.2)) := by
  intro item hitem
  rw [List.mem_append, List.mem_singleton] at hitem
  rcases hitem with hpast | rfl
  · exact (hprevious item hpast).trans (Nat.le_max_left _ _)
  · exact Nat.le_max_right _ _

private theorem Allocations.scanFreeIntervals_spaces_fit
    (previous items : List (ℕ × ℕ)) (row : ℕ)
    (endBound : Option ℕ)
    (hvalid : (previous ++ items).Pairwise IntervalBefore)
    (hprevious : EndsBefore previous row)
    {space : ℕ × Option ℕ}
    (hspace : space ∈ (scanFreeIntervals endBound items row).1)
    {start length : ℕ} (hallows : SpaceAllows space start length) :
    ∀ allocated ∈ previous ++ items,
      RowIntervalsDisjoint start length allocated.1 allocated.2 := by
  cases endBound with
  | none =>
      induction items generalizing previous row with
      | nil => simp [scanFreeIntervals] at hspace
      | cons head rest inductionHypothesis =>
          simp only [scanFreeIntervals, Bool.not_false, ↓reduceIte] at hspace
          split at hspace
          next hgap =>
            simp only [List.mem_cons] at hspace
            rcases hspace with rfl | htail
            · apply fits_of_before_and_after hprevious hallows.1
              intro item hitem
              exact hallows.2 head.1 rfl |>.trans
                (valid_head_start_le (valid_suffix hvalid) hitem)
            · intro allocated hallocated
              exact inductionHypothesis (previous := previous ++ [head])
                (row := max row (head.1 + head.2))
                (by simpa only [List.append_assoc] using hvalid)
                (endsBefore_append_singleton hprevious)
                htail allocated
                (by simpa only [List.append_assoc] using hallocated)
          next hnoGap =>
            intro allocated hallocated
            exact inductionHypothesis (previous := previous ++ [head])
              (row := max row (head.1 + head.2))
              (by simpa only [List.append_assoc] using hvalid)
              (endsBefore_append_singleton hprevious)
              hspace allocated
              (by simpa only [List.append_assoc] using hallocated)
  | some endRow =>
      induction items generalizing previous row with
      | nil => simp [scanFreeIntervals] at hspace
      | cons head rest inductionHypothesis =>
          by_cases hpast : endRow ≤ head.1
          · have hstarts : ∀ item ∈ head :: rest, endRow ≤ item.1 := by
              intro item hitem
              exact hpast.trans
                (valid_head_start_le (valid_suffix hvalid) hitem)
            rw [scanFreeIntervals_fst_eq_nil_of_starts_ge
              (head :: rest) row endRow hstarts] at hspace
            contradiction
          · simp only [scanFreeIntervals, hpast, decide_false,
              Bool.not_false, ↓reduceIte] at hspace
            split at hspace
            next hgap =>
              simp only [List.mem_cons] at hspace
              rcases hspace with rfl | htail
              · apply fits_of_before_and_after hprevious hallows.1
                intro item hitem
                exact hallows.2 head.1 rfl |>.trans
                  (valid_head_start_le (valid_suffix hvalid) hitem)
              · intro allocated hallocated
                exact inductionHypothesis (previous := previous ++ [head])
                  (row := max row (head.1 + head.2))
                  (by simpa only [List.append_assoc] using hvalid)
                  (endsBefore_append_singleton hprevious)
                  htail allocated
                  (by simpa only [List.append_assoc] using hallocated)
            next hnoGap =>
              intro allocated hallocated
              exact inductionHypothesis (previous := previous ++ [head])
                (row := max row (head.1 + head.2))
                (by simpa only [List.append_assoc] using hvalid)
                (endsBefore_append_singleton hprevious)
                hspace allocated
                (by simpa only [List.append_assoc] using hallocated)

private theorem Allocations.row_le_scanFreeIntervals
    (items : List (ℕ × ℕ)) (row : ℕ) (endBound : Option ℕ) :
    row ≤ (scanFreeIntervals endBound items row).2 := by
  induction items generalizing row with
  | nil => exact le_rfl
  | cons head rest inductionHypothesis =>
      cases endBound with
      | none =>
          simp only [scanFreeIntervals, Bool.not_false, ↓reduceIte]
          exact (Nat.le_max_left _ _).trans (inductionHypothesis _)
      | some endRow =>
          by_cases hpast : endRow ≤ head.1
          · simp only [scanFreeIntervals, hpast, decide_true,
              Bool.not_true]
            exact inductionHypothesis row
          · simp only [scanFreeIntervals, hpast, decide_false,
              Bool.not_false, ↓reduceIte]
            exact (Nat.le_max_left _ _).trans (inductionHypothesis _)

private theorem Allocations.scanFreeIntervals_boundary
    (items : List (ℕ × ℕ)) (row : ℕ) (endBound : Option ℕ) :
    ∀ item ∈ items,
      item.1 + item.2 ≤ (scanFreeIntervals endBound items row).2 ∨
        ∃ endRow, endBound = some endRow ∧ endRow ≤ item.1 := by
  intro item hitem
  induction items generalizing row with
  | nil => simp at hitem
  | cons head rest inductionHypothesis =>
      simp only [List.mem_cons] at hitem
      cases endBound with
      | none =>
          simp only [scanFreeIntervals, Bool.not_false, ↓reduceIte]
          rcases hitem with heq | hrest
          · subst item
            exact Or.inl ((Nat.le_max_right row (head.1 + head.2)).trans
              (row_le_scanFreeIntervals rest
                (max row (head.1 + head.2)) none))
          · exact inductionHypothesis (max row (head.1 + head.2)) hrest
      | some endRow =>
          by_cases hpast : endRow ≤ head.1
          · simp only [scanFreeIntervals, hpast, decide_true,
              Bool.not_true]
            rcases hitem with heq | hrest
            · subst item
              exact Or.inr ⟨endRow, rfl, hpast⟩
            · exact inductionHypothesis row hrest
          · simp only [scanFreeIntervals, hpast, decide_false,
              Bool.not_false, ↓reduceIte]
            rcases hitem with heq | hrest
            · subst item
              exact Or.inl (Nat.le_max_right row (head.1 + head.2) |>.trans
                (row_le_scanFreeIntervals rest
                  (max row (head.1 + head.2)) (some endRow)))
            · exact inductionHypothesis (max row (head.1 + head.2)) hrest

/-- Every interval admitted by `freeIntervals` is disjoint from all allocations. -/
theorem Allocations.freeIntervals_fits
    (allocations : Allocations) (start : ℕ) (endBound : Option ℕ)
    (hvalid : allocations.Valid)
    {space : ℕ × Option ℕ}
    (hspace : space ∈ allocations.freeIntervals start endBound)
    {candidate length : ℕ}
    (hallows : SpaceAllows space candidate length) :
    allocations.Fits candidate length := by
  cases endBound with
  | none =>
      simp only [freeIntervals, List.mem_append,
        List.mem_singleton] at hspace
      rcases hspace with hscan | rfl
      · exact scanFreeIntervals_spaces_fit [] allocations.toList start none
          (by simpa [Valid] using hvalid) (by simp [EndsBefore]) hscan hallows
      · intro item hitem
        have hboundary :=
          scanFreeIntervals_boundary allocations.toList start none item hitem
        rcases hboundary with hbefore | ⟨_, hnone, _⟩
        · exact Or.inr (hbefore.trans hallows.1)
        · contradiction
  | some endRow =>
      simp only [freeIntervals] at hspace
      split at hspace
      next hfinal =>
        simp only [List.mem_append, List.mem_singleton] at hspace
        rcases hspace with hscan | rfl
        · exact scanFreeIntervals_spaces_fit [] allocations.toList start
            (some endRow) (by simpa [Valid] using hvalid)
            (by simp [EndsBefore]) hscan hallows
        · intro item hitem
          have hboundary := scanFreeIntervals_boundary allocations.toList
            start (some endRow) item hitem
          rcases hboundary with hbefore | ⟨foundEnd, heq, hafter⟩
          · exact Or.inr (hbefore.trans hallows.1)
          · simp only [Option.some.injEq] at heq
            subst foundEnd
            exact Or.inl ((hallows.2 endRow rfl).trans hafter)
      next hnoFinal =>
        exact scanFreeIntervals_spaces_fit [] allocations.toList start
          (some endRow) (by simpa [Valid] using hvalid)
          (by simp [EndsBefore]) hspace hallows

private theorem Allocations.scanFreeIntervals_end_le
    (items : List (ℕ × ℕ)) (row endRow : ℕ)
    {spaceStart spaceEnd : ℕ}
    (hspace : (spaceStart, some spaceEnd) ∈
      (scanFreeIntervals (some endRow) items row).1) :
    spaceEnd ≤ endRow := by
  induction items generalizing row with
  | nil => simp [scanFreeIntervals] at hspace
  | cons head rest inductionHypothesis =>
      by_cases hpast : endRow ≤ head.1
      · simp only [scanFreeIntervals, hpast, decide_true,
          Bool.not_true] at hspace
        exact inductionHypothesis row hspace
      · simp only [scanFreeIntervals, hpast, decide_false,
          Bool.not_false, ↓reduceIte] at hspace
        split at hspace
        next hgap =>
          simp only [List.mem_cons, Prod.mk.injEq,
            Option.some.injEq] at hspace
          rcases hspace with ⟨rfl, rfl⟩ | htail
          · omega
          · exact inductionHypothesis _ htail
        next hnoGap =>
          exact inductionHypothesis _ hspace

/-- Every bounded free interval ends within the requested upper bound. -/
theorem Allocations.freeIntervals_end_le
    (allocations : Allocations) (start endRow : ℕ)
    {intervalStart intervalEnd : ℕ}
    (hinterval :
      (intervalStart, some intervalEnd) ∈
        allocations.freeIntervals start (some endRow)) :
    intervalEnd ≤ endRow := by
  simp only [Allocations.freeIntervals] at hinterval
  split at hinterval
  next hfinal =>
    simp only [List.mem_append, List.mem_singleton,
      Prod.mk.injEq, Option.some.injEq] at hinterval
    rcases hinterval with hscan | ⟨_, rfl⟩
    · exact scanFreeIntervals_end_le allocations.toList start endRow hscan
    · exact le_rfl
  next hnoFinal =>
    exact scanFreeIntervals_end_le allocations.toList start endRow hinterval

private theorem Allocations.scanFreeIntervals_start_le
    (items : List (ℕ × ℕ)) (row : ℕ) (endBound : Option ℕ)
    {space : ℕ × Option ℕ}
    (hspace : space ∈ (scanFreeIntervals endBound items row).1) :
    row ≤ space.1 := by
  induction items generalizing row with
  | nil => simp [scanFreeIntervals] at hspace
  | cons head rest inductionHypothesis =>
      cases endBound with
      | none =>
          simp only [scanFreeIntervals, Bool.not_false, ↓reduceIte] at hspace
          split at hspace
          next hgap =>
            simp only [List.mem_cons] at hspace
            rcases hspace with rfl | htail
            · exact le_rfl
            · exact (Nat.le_max_left _ _).trans
                (inductionHypothesis _ htail)
          next =>
            exact (Nat.le_max_left _ _).trans
              (inductionHypothesis _ hspace)
      | some endRow =>
          by_cases hpast : endRow ≤ head.1
          · simp only [scanFreeIntervals, hpast, decide_true,
              Bool.not_true] at hspace
            exact inductionHypothesis row hspace
          · simp only [scanFreeIntervals, hpast, decide_false,
              Bool.not_false, ↓reduceIte] at hspace
            split at hspace
            next hgap =>
              simp only [List.mem_cons] at hspace
              rcases hspace with rfl | htail
              · exact le_rfl
              · exact (Nat.le_max_left _ _).trans
                  (inductionHypothesis _ htail)
            next =>
              exact (Nat.le_max_left _ _).trans
                (inductionHypothesis _ hspace)

theorem Allocations.freeIntervals_start_le
    (allocations : Allocations) (start : ℕ) (endBound : Option ℕ)
    {space : ℕ × Option ℕ}
    (hspace : space ∈ allocations.freeIntervals start endBound) :
    start ≤ space.1 := by
  cases endBound with
  | none =>
      simp only [Allocations.freeIntervals, List.mem_append,
        List.mem_singleton] at hspace
      rcases hspace with hscan | rfl
      · exact scanFreeIntervals_start_le _ _ _ hscan
      · exact row_le_scanFreeIntervals _ _ _
  | some endRow =>
      simp only [Allocations.freeIntervals] at hspace
      split at hspace
      next =>
        simp only [List.mem_append, List.mem_singleton] at hspace
        rcases hspace with hscan | rfl
        · exact scanFreeIntervals_start_le _ _ _ hscan
        · exact row_le_scanFreeIntervals _ _ _
      next => exact scanFreeIntervals_start_le _ _ _ hspace

private theorem Allocations.scanFreeIntervals_contains_fitting_candidate
    (items : List (ℕ × ℕ)) (row candidate length : ℕ)
    (endBound : Option ℕ)
    (hvalid : items.Pairwise IntervalBefore)
    (hrow : row ≤ candidate)
    (hlength : 0 < length)
    (hfits : ∀ allocated ∈ items,
      RowIntervalsDisjoint candidate length allocated.1 allocated.2) :
    (∃ space ∈ (scanFreeIntervals endBound items row).1,
      SpaceAllows space candidate length) ∨
      (scanFreeIntervals endBound items row).2 ≤ candidate := by
  induction items generalizing row with
  | nil => exact Or.inr hrow
  | cons head rest inductionHypothesis =>
      have hrestValid := List.pairwise_cons.mp hvalid |>.2
      have hrestFits : ∀ allocated ∈ rest,
          RowIntervalsDisjoint candidate length allocated.1 allocated.2 := by
        intro allocated hallocated
        exact hfits allocated (by simp [hallocated])
      have hheadFits := hfits head (by simp)
      cases endBound with
      | none =>
          simp only [scanFreeIntervals, Bool.not_false, ↓reduceIte]
          rcases hheadFits with hcandidateBefore | hheadBefore
          · have hgap : row < head.1 := by omega
            rw [if_pos hgap]
            exact Or.inl ⟨(row, some head.1), by simp,
              ⟨hrow, by intro stop hstop; simp_all⟩⟩
          · have hnext : max row (head.1 + head.2) ≤ candidate := by omega
            have htail := inductionHypothesis
              (max row (head.1 + head.2)) hrestValid hnext hrestFits
            split
            · rcases htail with ⟨space, hspace, hallows⟩ | hend
              · exact Or.inl ⟨space, by simp [hspace], hallows⟩
              · exact Or.inr hend
            · exact htail
      | some endRow =>
          by_cases hpast : endRow ≤ head.1
          · simp only [scanFreeIntervals, hpast, decide_true, Bool.not_true]
            exact inductionHypothesis row hrestValid hrow hrestFits
          · simp only [scanFreeIntervals, hpast, decide_false,
              Bool.not_false, ↓reduceIte]
            rcases hheadFits with hcandidateBefore | hheadBefore
            · have hgap : row < head.1 := by omega
              rw [if_pos hgap]
              exact Or.inl ⟨(row, some head.1), by simp,
                ⟨hrow, by intro stop hstop; simp_all⟩⟩
            · have hnext : max row (head.1 + head.2) ≤ candidate := by omega
              have htail := inductionHypothesis
                (max row (head.1 + head.2)) hrestValid hnext hrestFits
              split
              · rcases htail with ⟨space, hspace, hallows⟩ | hend
                · exact Or.inl ⟨space, by simp [hspace], hallows⟩
                · exact Or.inr hend
              · exact htail

/-- Every fitting candidate belongs to one of the free intervals enumerated from
an earlier search boundary. This is the completeness counterpart of
`freeIntervals_fits`. -/
theorem Allocations.exists_freeInterval_of_fits
    (allocations : Allocations) (start candidate length : ℕ)
    (endBound : Option ℕ)
    (hvalid : allocations.Valid) (hstart : start ≤ candidate)
    (hlength : 0 < length) (hfits : allocations.Fits candidate length)
    (hbound : ∀ stop, endBound = some stop → candidate + length ≤ stop) :
    ∃ space ∈ allocations.freeIntervals start endBound,
      SpaceAllows space candidate length := by
  have hscan := scanFreeIntervals_contains_fitting_candidate
    allocations.toList start candidate length endBound
    (by simpa [Valid] using hvalid) hstart hlength hfits
  cases endBound with
  | none =>
      rcases hscan with ⟨space, hspace, hallows⟩ | hend
      · exact ⟨space, by simp [freeIntervals, hspace], hallows⟩
      · refine ⟨((scanFreeIntervals none allocations.toList start).2, none),
          by simp [freeIntervals], ⟨hend, by simp⟩⟩
  | some endRow =>
      have hcandidateEnd := hbound endRow rfl
      rcases hscan with ⟨space, hspace, hallows⟩ | hend
      · by_cases hfinal :
            (scanFreeIntervals (some endRow) allocations.toList start).2 <
              endRow
        · exact ⟨space, by simp [freeIntervals, hfinal, hspace], hallows⟩
        · exact ⟨space, by simp [freeIntervals, hfinal, hspace], hallows⟩
      · have hfinal :
            (scanFreeIntervals (some endRow) allocations.toList start).2 <
              endRow := by omega
        refine ⟨((scanFreeIntervals (some endRow)
              allocations.toList start).2, some endRow),
            by simp [freeIntervals, hfinal], ⟨hend, ?_⟩⟩
        intro stop hstop
        simp only [Option.some.injEq] at hstop
        subst stop
        exact hcandidateEnd

/-- Earlier free intervals end before later free intervals begin. -/
def Allocations.SpaceBefore
    (left right : ℕ × Option ℕ) : Prop :=
  ∃ stop, left.2 = some stop ∧ stop ≤ right.1

private theorem Allocations.scanFreeIntervals_space_bounded
    (items : List (ℕ × ℕ)) (row : ℕ) (endBound : Option ℕ)
    {space : ℕ × Option ℕ}
    (hspace : space ∈ (scanFreeIntervals endBound items row).1) :
    ∃ stop, space.2 = some stop := by
  induction items generalizing row with
  | nil => simp [scanFreeIntervals] at hspace
  | cons head rest inductionHypothesis =>
      cases endBound with
      | none =>
          simp only [scanFreeIntervals, Bool.not_false, ↓reduceIte] at hspace
          split at hspace
          next =>
            simp only [List.mem_cons] at hspace
            rcases hspace with rfl | htail
            · exact ⟨head.1, rfl⟩
            · exact inductionHypothesis _ htail
          next => exact inductionHypothesis _ hspace
      | some endRow =>
          by_cases hpast : endRow ≤ head.1
          · simp only [scanFreeIntervals, hpast, decide_true,
              Bool.not_true] at hspace
            exact inductionHypothesis row hspace
          · simp only [scanFreeIntervals, hpast, decide_false,
              Bool.not_false, ↓reduceIte] at hspace
            split at hspace
            next =>
              simp only [List.mem_cons] at hspace
              rcases hspace with rfl | htail
              · exact ⟨head.1, rfl⟩
              · exact inductionHypothesis _ htail
            next => exact inductionHypothesis _ hspace

private theorem Allocations.scanFreeIntervals_space_end_le
    (items : List (ℕ × ℕ)) (row : ℕ) (endBound : Option ℕ)
    {space : ℕ × Option ℕ}
    (hspace : space ∈ (scanFreeIntervals endBound items row).1) :
    ∀ stop, space.2 = some stop →
      stop ≤ (scanFreeIntervals endBound items row).2 := by
  induction items generalizing row with
  | nil => simp [scanFreeIntervals] at hspace
  | cons head rest inductionHypothesis =>
      cases endBound with
      | none =>
          simp only [scanFreeIntervals, Bool.not_false, ↓reduceIte] at hspace ⊢
          split at hspace
          next hgap =>
            simp only [List.mem_cons] at hspace
            rcases hspace with rfl | htail
            · intro stop hstop
              simp only [Option.some.injEq] at hstop
              subst stop
              exact (Nat.le_add_right head.1 head.2).trans
                ((Nat.le_max_right row (head.1 + head.2)).trans
                  (row_le_scanFreeIntervals rest _ none))
            · exact inductionHypothesis _ htail
          next => exact inductionHypothesis _ hspace
      | some endRow =>
          by_cases hpast : endRow ≤ head.1
          · simp only [scanFreeIntervals, hpast, decide_true,
              Bool.not_true] at hspace ⊢
            exact inductionHypothesis row hspace
          · simp only [scanFreeIntervals, hpast, decide_false,
              Bool.not_false, ↓reduceIte] at hspace ⊢
            split at hspace
            next hgap =>
              simp only [List.mem_cons] at hspace
              rcases hspace with rfl | htail
              · intro stop hstop
                simp only [Option.some.injEq] at hstop
                subst stop
                exact (Nat.le_add_right head.1 head.2).trans
                  ((Nat.le_max_right row (head.1 + head.2)).trans
                    (row_le_scanFreeIntervals rest _ (some endRow)))
              · exact inductionHypothesis _ htail
            next => exact inductionHypothesis _ hspace

private theorem Allocations.scanFreeIntervals_pairwise
    (items : List (ℕ × ℕ)) (row : ℕ) (endBound : Option ℕ) :
    (scanFreeIntervals endBound items row).1.Pairwise SpaceBefore := by
  induction items generalizing row with
  | nil => simp [scanFreeIntervals]
  | cons head rest inductionHypothesis =>
      cases endBound with
      | none =>
          simp only [scanFreeIntervals, Bool.not_false, ↓reduceIte]
          split
          next hgap =>
            rw [List.pairwise_cons]
            constructor
            · intro space hspace
              exact ⟨head.1, rfl,
                (Nat.le_add_right head.1 head.2).trans
                  ((Nat.le_max_right row (head.1 + head.2)).trans
                    (scanFreeIntervals_start_le rest _ none hspace))⟩
            · exact inductionHypothesis _
          next => exact inductionHypothesis _
      | some endRow =>
          by_cases hpast : endRow ≤ head.1
          · simp only [scanFreeIntervals, hpast, decide_true, Bool.not_true]
            exact inductionHypothesis row
          · simp only [scanFreeIntervals, hpast, decide_false,
              Bool.not_false, ↓reduceIte]
            split
            next hgap =>
              rw [List.pairwise_cons]
              constructor
              · intro space hspace
                exact ⟨head.1, rfl,
                  (Nat.le_add_right head.1 head.2).trans
                    ((Nat.le_max_right row (head.1 + head.2)).trans
                      (scanFreeIntervals_start_le rest _ (some endRow) hspace))⟩
              · exact inductionHypothesis _
            next => exact inductionHypothesis _

/-- The free-space iterator enumerates disjoint spaces from low rows to high rows. -/
theorem Allocations.freeIntervals_pairwise
    (allocations : Allocations) (start : ℕ) (endBound : Option ℕ) :
    (allocations.freeIntervals start endBound).Pairwise SpaceBefore := by
  cases endBound with
  | none =>
      simp only [freeIntervals]
      rw [List.pairwise_append]
      exact ⟨scanFreeIntervals_pairwise _ _ _, by simp, by
        intro left hleft right hright
        simp only [List.mem_singleton] at hright
        subst right
        obtain ⟨stop, hstop⟩ := scanFreeIntervals_space_bounded _ _ _ hleft
        exact ⟨stop, hstop,
          scanFreeIntervals_space_end_le _ _ _ hleft stop hstop⟩⟩
  | some endRow =>
      simp only [freeIntervals]
      split
      next hfinal =>
        rw [List.pairwise_append]
        exact ⟨scanFreeIntervals_pairwise _ _ _, by simp, by
          intro left hleft right hright
          simp only [List.mem_singleton] at hright
          subst right
          obtain ⟨stop, hstop⟩ := scanFreeIntervals_space_bounded _ _ _ hleft
          exact ⟨stop, hstop,
            scanFreeIntervals_space_end_le _ _ _ hleft stop hstop⟩⟩
      next => exact scanFreeIntervals_pairwise _ _ _

private theorem Allocations.scanFreeIntervals_bounded
    (items : List (ℕ × ℕ)) (row endRow : ℕ)
    {space : ℕ × Option ℕ}
    (hspace : space ∈
      (scanFreeIntervals (some endRow) items row).1) :
    ∃ stop, space.2 = some stop := by
  induction items generalizing row with
  | nil => simp [scanFreeIntervals] at hspace
  | cons head rest inductionHypothesis =>
      by_cases hpast : endRow ≤ head.1
      · simp only [scanFreeIntervals, hpast, decide_true,
          Bool.not_true] at hspace
        exact inductionHypothesis row hspace
      · simp only [scanFreeIntervals, hpast, decide_false,
          Bool.not_false, ↓reduceIte] at hspace
        split at hspace
        next =>
          simp only [List.mem_cons] at hspace
          rcases hspace with rfl | htail
          · exact ⟨head.1, rfl⟩
          · exact inductionHypothesis _ htail
        next => exact inductionHypothesis _ hspace

theorem Allocations.freeIntervals_bounded
    (allocations : Allocations) (start endRow : ℕ)
    {space : ℕ × Option ℕ}
    (hspace : space ∈ allocations.freeIntervals start (some endRow)) :
    ∃ stop, space.2 = some stop := by
  simp only [Allocations.freeIntervals] at hspace
  split at hspace
  next =>
    simp only [List.mem_append, List.mem_singleton] at hspace
    rcases hspace with hscan | rfl
    · exact scanFreeIntervals_bounded _ _ _ hscan
    · exact ⟨endRow, rfl⟩
  next => exact scanFreeIntervals_bounded _ _ _ hspace

/-- The circuit's per-column allocations. -/
abbrev CircuitAllocations := Std.HashMap RegionColumn Allocations

/-- Every per-column allocation sequence satisfies its ordering invariant. -/
def CircuitAllocations.Valid (allocations : CircuitAllocations) : Prop :=
  ∀ column, (allocations.getD column #[]).Valid

/-- Every allocation recorded before remains recorded after an update. -/
def CircuitAllocations.Extends
    (before after : CircuitAllocations) : Prop :=
  ∀ column interval,
    interval ∈ (before.getD column #[]).toList →
      interval ∈ (after.getD column #[]).toList

/-- An update leaves columns outside the given footprint unchanged. -/
def CircuitAllocations.SameOutside
    (columns : List RegionColumn)
    (before after : CircuitAllocations) : Prop :=
  ∀ column, column ∉ columns →
    after.getD column #[] = before.getD column #[]

/-- An allocation map records one placed interval in every listed column. -/
def CircuitAllocations.Records
    (allocations : CircuitAllocations) (columns : List RegionColumn)
    (start length : ℕ) : Prop :=
  ∀ column ∈ columns,
    (start, length) ∈ (allocations.getD column #[]).toList

/-- Two allocation maps agree on the columns observable by a region. -/
def CircuitAllocations.AgreesOn (left right : CircuitAllocations)
    (columns : List RegionColumn) : Prop :=
  ∀ column, column ∈ columns →
    left.getD column #[] = right.getD column #[]

/-- Allocation maps with the same observable interval sequence in every column. -/
def CircuitAllocations.Equivalent
    (left right : CircuitAllocations) : Prop :=
  ∀ column, left.getD column #[] = right.getD column #[]

theorem CircuitAllocations.Equivalent.refl
    (allocations : CircuitAllocations) : allocations.Equivalent allocations := by
  intro column
  rfl

theorem CircuitAllocations.Equivalent.symm
    {left right : CircuitAllocations} (h : left.Equivalent right) :
    right.Equivalent left := by
  intro column
  exact (h column).symm

theorem CircuitAllocations.Equivalent.trans
    {left middle right : CircuitAllocations}
    (hleft : left.Equivalent middle) (hright : middle.Equivalent right) :
    left.Equivalent right := by
  intro column
  exact (hleft column).trans (hright column)

theorem CircuitAllocations.Equivalent.agreesOn
    {left right : CircuitAllocations} (h : left.Equivalent right)
    (columns : List RegionColumn) : left.AgreesOn right columns := by
  intro column _
  exact h column

theorem CircuitAllocations.AgreesOn.mono
    {left right : CircuitAllocations} {inner outer : List RegionColumn}
    (h : left.AgreesOn right outer) (hsubset : inner ⊆ outer) :
    left.AgreesOn right inner := by
  intro column hcolumn
  exact h column (hsubset hcolumn)

theorem CircuitAllocations.AgreesOn.insert
    {left right : CircuitAllocations} {columns : List RegionColumn}
    (h : left.AgreesOn right columns) (column : RegionColumn)
    {leftValue rightValue : Allocations} (hvalue : leftValue = rightValue) :
    CircuitAllocations.AgreesOn (left.insert column leftValue)
      (right.insert column rightValue) columns := by
  intro candidate hcandidate
  rw [Std.HashMap.getD_insert, Std.HashMap.getD_insert]
  split
  next => rw [hvalue]
  next => exact h candidate hcandidate

theorem CircuitAllocations.Valid.empty :
    (∅ : CircuitAllocations).Valid := by
  intro column
  simp [Allocations.Valid]

theorem CircuitAllocations.Extends.refl
    (allocations : CircuitAllocations) :
    allocations.Extends allocations := by
  intro column interval hinterval
  exact hinterval

theorem CircuitAllocations.Extends.trans
    {first second third : CircuitAllocations}
    (hfirst : first.Extends second) (hsecond : second.Extends third) :
    first.Extends third := by
  intro column interval hinterval
  exact hsecond column interval (hfirst column interval hinterval)

theorem CircuitAllocations.Valid.insertSame
    {allocations : CircuitAllocations} (hvalid : allocations.Valid)
    (column : RegionColumn) :
    CircuitAllocations.Valid
      (allocations.insert column (allocations.getD column #[])) := by
  intro candidate
  rw [Std.HashMap.getD_insert]
  split
  next heq =>
    have : column = candidate := by simpa using heq
    subst candidate
    exact hvalid column
  · exact hvalid candidate

theorem CircuitAllocations.Extends.insertSame
    (allocations : CircuitAllocations) (column : RegionColumn) :
    allocations.Extends
      (allocations.insert column (allocations.getD column #[])) := by
  intro candidate interval hinterval
  rw [Std.HashMap.getD_insert]
  split
  next heq =>
    have : column = candidate := by simpa using heq
    subst candidate
    exact hinterval
  · exact hinterval

theorem CircuitAllocations.SameOutside.insertSame
    (allocations : CircuitAllocations) (column : RegionColumn) :
    allocations.SameOutside [column]
      (allocations.insert column (allocations.getD column #[])) := by
  intro candidate hcandidate
  simp only [List.mem_singleton] at hcandidate
  rw [Std.HashMap.getD_insert]
  split
  next heq =>
    exact False.elim (hcandidate (beq_iff_eq.mp heq).symm)
  next => rfl

theorem CircuitAllocations.Valid.insertAllocation
    {allocations : CircuitAllocations} (hvalid : allocations.Valid)
    (column : RegionColumn) (start length : ℕ)
    (hfits : (allocations.getD column #[]).Fits start length)
    (hlength : 0 < length) :
    CircuitAllocations.Valid
      (allocations.insert column
        ((allocations.getD column #[]).insert start length)) := by
  intro candidate
  rw [Std.HashMap.getD_insert]
  split
  next heq =>
    have : column = candidate := by simpa using heq
    subst candidate
    exact Allocations.Valid.insert _ _ _
      (hvalid column) hfits hlength
  next hne => exact hvalid candidate

theorem CircuitAllocations.Extends.insertAllocation
    (allocations : CircuitAllocations) (column : RegionColumn)
    (start length : ℕ) :
    allocations.Extends
      (allocations.insert column
        ((allocations.getD column #[]).insert start length)) := by
  intro candidate interval hinterval
  rw [Std.HashMap.getD_insert]
  split
  next heq =>
    have : column = candidate := by simpa using heq
    subst candidate
    exact Allocations.mem_insert_of_mem _ _ _ hinterval
  next hne => exact hinterval

theorem CircuitAllocations.SameOutside.insertAllocation
    (allocations : CircuitAllocations) (column : RegionColumn)
    (start length : ℕ) :
    allocations.SameOutside [column]
      (allocations.insert column
        ((allocations.getD column #[]).insert start length)) := by
  intro candidate hcandidate
  simp only [List.mem_singleton] at hcandidate
  rw [Std.HashMap.getD_insert]
  split
  next heq =>
    exact False.elim (hcandidate (beq_iff_eq.mp heq).symm)
  next => rfl

mutual

/-- `first_fit_region` (`strategy.rs:107-161`): find the earliest common start row for all of
`cols` (already `RegionColumn::Ord`-sorted), inserting the placed interval into every column.
Returns the start row (`none` if unplaceable) and the updated allocations. `slack` bounds how
far the start may move (`end = start + region_length + slack`); the recursion threads it.

Total via explicit fuel: the Rust recursion consumes exactly one column per level
(`region_columns.split_first()`, `strategy.rs:114`), so `fuel = cols.length` at the top call
(`slotIn`) provably suffices. The `fuel = 0, cols ≠ []` arm is unreachable; it returns
`none` ("no placement"), which the fixture-equality checks would surface loudly. -/
def firstFit (fuel : ℕ) (colAllocs : CircuitAllocations) (cols : List RegionColumn)
    (regionLen : ℕ) (start : ℕ) (slack : Option ℕ) : Option ℕ × CircuitAllocations :=
  match fuel, cols with
  | _, [] => (some start, colAllocs)
  | 0, _ :: _ => (none, colAllocs)
  | fuel + 1, c :: rest =>
    let endBound := slack.map (fun s => start + regionLen + s)
    let cAlloc := colAllocs.getD c #[]
    -- `entry(*c).or_default()` — ensure the key exists (so it shows up in `first_unassigned_row`).
    let colAllocs := colAllocs.insert c cAlloc
    trySpaces fuel colAllocs c rest regionLen (cAlloc.freeIntervals start endBound)
termination_by (fuel, 0, 0)

/-- The `for space in …free_intervals` loop of `first_fit_region` (`strategy.rs:121-157`):
try each free interval of column `c` in order; a space with enough room recurses into the
remaining columns — success inserts the placed interval into `c` and returns
(`strategy.rs:142-154`), failure keeps the (mutated) allocations and moves to the next
space. The spaces are computed ONCE from the state at `firstFit` entry (Rust iterates a
`.clone()`, `strategy.rs:119-124`), so inner mutations do not re-enter the iteration. -/
def trySpaces (fuel : ℕ) (colAllocs : CircuitAllocations) (c : RegionColumn)
    (rest : List RegionColumn) (regionLen : ℕ) (spaces : List (ℕ × Option ℕ)) :
    Option ℕ × CircuitAllocations :=
  match spaces with
  | [] => (none, colAllocs)
  | (sStart, sEnd) :: more =>
    let sSlack : Option ℤ := sEnd.map (fun e => (e : ℤ) - (sStart : ℤ) - (regionLen : ℤ))
    let ok : Bool := match sSlack with | some ss => decide (ss ≥ 0) | none => true
    if ok then
      let recSlack : Option ℕ := sSlack.map Int.toNat
      let (row?, m') := firstFit fuel colAllocs rest regionLen sStart recSlack
      match row? with
      | some row =>
        let cA := (m'.getD c #[]).insert row regionLen
        (some row, m'.insert c cA)
      | none => trySpaces fuel m' c rest regionLen more
    else
      trySpaces fuel colAllocs c rest regionLen more
termination_by (fuel, 1, spaces.length)

end

/-- Once fuel covers every remaining column, its exact value is unobservable. -/
theorem firstFit_eq_of_sufficient_fuel
    (columns : List RegionColumn) :
    ∀ (leftFuel rightFuel : ℕ) (allocations : CircuitAllocations)
      (length start : ℕ) (slack : Option ℕ),
      columns.length ≤ leftFuel → columns.length ≤ rightFuel →
      firstFit leftFuel allocations columns length start slack =
        firstFit rightFuel allocations columns length start slack := by
  induction columns with
  | nil =>
      intro leftFuel rightFuel allocations length start slack _ _
      simp [firstFit]
  | cons column rest inductionHypothesis =>
      intro leftFuel rightFuel allocations length start slack
        hleftFuel hrightFuel
      cases leftFuel with
      | zero => simp at hleftFuel
      | succ leftFuel =>
          cases rightFuel with
          | zero => simp at hrightFuel
          | succ rightFuel =>
              have hleftRest : rest.length ≤ leftFuel := by
                simpa using hleftFuel
              have hrightRest : rest.length ≤ rightFuel := by
                simpa using hrightFuel
              let initialized := allocations.insert column
                (allocations.getD column #[])
              let spaces := (allocations.getD column #[]).freeIntervals start
                (slack.map fun available => start + length + available)
              have compareSpaces : ∀ (remaining : List (ℕ × Option ℕ))
                  (current : CircuitAllocations),
                  trySpaces leftFuel current column rest length remaining =
                    trySpaces rightFuel current column rest length remaining := by
                intro remaining
                induction remaining with
                | nil =>
                    intro current
                    simp [trySpaces]
                | cons space more spacesInduction =>
                    rcases space with ⟨spaceStart, spaceEnd⟩
                    intro current
                    let available : Option ℤ := spaceEnd.map fun stop =>
                      (stop : ℤ) - spaceStart - length
                    let ok : Bool := match available with
                      | some value => decide (value ≥ 0)
                      | none => true
                    by_cases hok : ok = true
                    · have hrecursive := inductionHypothesis leftFuel rightFuel
                        current length spaceStart (available.map Int.toNat)
                        hleftRest hrightRest
                      generalize hleft : firstFit leftFuel current rest length
                        spaceStart (available.map Int.toNat) = leftResult
                          at hrecursive
                      have hright := hrecursive.symm
                      rcases leftResult with ⟨row, updated⟩
                      cases row with
                      | some row =>
                          simp only [trySpaces]
                          change ((if ok = true then _ else _) :
                              Option ℕ × CircuitAllocations) =
                            ((if ok = true then _ else _) :
                              Option ℕ × CircuitAllocations)
                          simp only [if_pos hok]
                          have havailable :
                              (spaceEnd.map fun stop =>
                                (stop : ℤ) - spaceStart - length) =
                                available := rfl
                          rw [havailable, hleft, hright]
                      | none =>
                          have hnext := spacesInduction updated
                          simp only [trySpaces]
                          change ((if ok = true then _ else _) :
                              Option ℕ × CircuitAllocations) =
                            ((if ok = true then _ else _) :
                              Option ℕ × CircuitAllocations)
                          simp only [if_pos hok]
                          have havailable :
                              (spaceEnd.map fun stop =>
                                (stop : ℤ) - spaceStart - length) =
                                available := rfl
                          rw [havailable, hleft, hright]
                          exact hnext
                    · have hnext := spacesInduction current
                      simp only [trySpaces]
                      change ((if ok = true then _ else _) :
                          Option ℕ × CircuitAllocations) =
                        ((if ok = true then _ else _) :
                          Option ℕ × CircuitAllocations)
                      simpa only [if_neg hok] using hnext
              simp only [firstFit]
              exact compareSpaces spaces initialized


/-- A successful recursive placement remains inside its initial search window. -/
def Within (start : ℕ) (slack : Option ℕ)
    (length row : ℕ) : Prop :=
  start ≤ row ∧
    ∀ available, slack = some available →
      row + length ≤ start + length + available

/-- The allocation facts preserved by either a successful or failed first-fit search. -/
structure PlacementLaw
    (before : CircuitAllocations) (columns : List RegionColumn)
    (length : ℕ) (result : Option ℕ × CircuitAllocations) : Prop where
  valid : result.2.Valid
  preserves : before.Extends result.2
  sameOutside : before.SameOutside columns result.2
  records : ∀ row, result.1 = some row →
    result.2.Records columns row length
  fits : ∀ row, result.1 = some row →
    ∀ column ∈ columns,
      (before.getD column #[]).Fits row length

private def FirstFitLaw
    (fuel : ℕ) (allocations : CircuitAllocations)
    (columns : List RegionColumn) (length start : ℕ)
    (slack : Option ℕ) : Prop :=
  allocations.Valid → columns.Nodup → 0 < length →
    let result := firstFit fuel allocations columns length start slack
    PlacementLaw allocations columns length result ∧
      ∀ row, result.1 = some row → Within start slack length row

private def TrySpacesLaw
    (fuel : ℕ) (allocations : CircuitAllocations)
    (column : RegionColumn) (rest : List RegionColumn)
    (length : ℕ) (spaces : List (ℕ × Option ℕ)) : Prop :=
  allocations.Valid → rest.Nodup → column ∉ rest → 0 < length →
    (∀ space ∈ spaces, ∀ row,
      Allocations.SpaceAllows space row length →
        (allocations.getD column #[]).Fits row length) →
    let result := trySpaces fuel allocations column rest length spaces
    PlacementLaw allocations (column :: rest) length result ∧
      ∀ row, result.1 = some row →
        ∃ space ∈ spaces,
          Allocations.SpaceAllows space row length

theorem within_space_of_ok
    (spaceStart : ℕ) (spaceEnd : Option ℕ) (length row : ℕ)
    (hok : (match spaceEnd.map fun endRow =>
        (endRow : ℤ) - spaceStart - length with
      | some available => decide (available ≥ 0)
      | none => true) = true)
    (hwithin : Within spaceStart
      ((spaceEnd.map fun endRow =>
        (endRow : ℤ) - spaceStart - length).map Int.toNat)
      length row) :
    Allocations.SpaceAllows (spaceStart, spaceEnd) row length := by
  constructor
  · exact hwithin.1
  · intro stop hstop
    change spaceEnd = some stop at hstop
    subst spaceEnd
    change decide
      (((stop : ℤ) - spaceStart - length) ≥ 0) = true at hok
    rw [decide_eq_true_eq] at hok
    have hbound := hwithin.2
      ((stop : ℤ) - spaceStart - length).toNat rfl
    have hcast :
        (↑(((stop : ℤ) - spaceStart - length).toNat) : ℤ) =
          (stop : ℤ) - spaceStart - length :=
      Int.toNat_of_nonneg hok
    omega

/-- First-fit preserves allocation validity and records any successful placement. -/
theorem firstFit_law
    (fuel : ℕ) (allocations : CircuitAllocations)
    (columns : List RegionColumn) (length start : ℕ)
    (slack : Option ℕ) :
    FirstFitLaw fuel allocations columns length start slack := by
  apply firstFit.induct (regionLen := length)
    (motive1 := fun fuel allocations columns start slack =>
      FirstFitLaw fuel allocations columns length start slack)
    (motive2 := fun fuel allocations column rest spaces =>
      TrySpacesLaw fuel allocations column rest length spaces)
  all_goals simp only [FirstFitLaw, TrySpacesLaw]
  case case1 =>
    intro fuel allocations start slack hvalid hnodup hlength
    simp only [firstFit]
    constructor
    · exact
        { valid := hvalid
          preserves := CircuitAllocations.Extends.refl allocations
          sameOutside := by intro column hcolumn; rfl
          records := by
            intro row hrow column hcolumn
            simp at hcolumn
          fits := by
            intro row hrow column hcolumn
            simp at hcolumn }
    · intro row hrow
      simp only [Option.some.injEq] at hrow
      subst row
      exact ⟨le_rfl, by intro available havailable; omega⟩
  case case2 =>
    intro allocations start slack head tail hvalid hnodup hlength
    simp only [firstFit]
    constructor
    · exact
        { valid := hvalid
          preserves := CircuitAllocations.Extends.refl allocations
          sameOutside := by intro column hcolumn; rfl
          records := by simp
          fits := by simp }
    · simp
  case case3 =>
    intro allocations start slack fuel column rest inductionHypothesis
      hvalid hnodup hlength
    have hrestNodup := List.nodup_cons.mp hnodup |>.2
    have hcolumnRest := List.nodup_cons.mp hnodup |>.1
    let initialized :=
      allocations.insert column (allocations.getD column #[])
    have hinitializedValid : CircuitAllocations.Valid initialized :=
      CircuitAllocations.Valid.insertSame hvalid column
    have hspaceSafety :
        ∀ space ∈ (allocations.getD column #[]).freeIntervals start
            (slack.map fun available => start + length + available),
          ∀ row, Allocations.SpaceAllows space row length →
            (initialized.getD column #[]).Fits row length := by
      intro space hspace row hallows
      have hfits := Allocations.freeIntervals_fits
        (allocations.getD column #[]) start
        (slack.map fun available => start + length + available)
        (hvalid column) hspace hallows
      simpa [initialized, Std.HashMap.getD_insert] using hfits
    obtain ⟨hlaw, hwitness⟩ := inductionHypothesis
      hinitializedValid hrestNodup hcolumnRest hlength hspaceSafety
    simp only [firstFit]
    constructor
    · refine
        { valid := hlaw.valid
          preserves := ?_
          sameOutside := ?_
          records := hlaw.records
          fits := ?_ }
      · exact (CircuitAllocations.Extends.insertSame allocations column).trans
          hlaw.preserves
      · intro candidate hcandidate
        have hresult := hlaw.sameOutside candidate hcandidate
        rw [hresult]
        exact CircuitAllocations.SameOutside.insertSame allocations column
          candidate (by
            intro heq
            apply hcandidate
            simp only [List.mem_cons]
            exact Or.inl (by simpa using heq))
      · intro row hrow candidate hcandidate
        have hfits := hlaw.fits row hrow candidate hcandidate
        change (initialized.getD candidate #[]).Fits row length at hfits
        dsimp only [initialized] at hfits
        rw [Std.HashMap.getD_insert] at hfits
        split at hfits
        next heq =>
          have : column = candidate := beq_iff_eq.mp heq
          subst candidate
          exact hfits
        next => exact hfits
    · intro row hrow
      obtain ⟨space, hspace, hallows⟩ := hwitness row hrow
      constructor
      · exact (Allocations.freeIntervals_start_le _ _ _ hspace).trans
          hallows.1
      · intro available havailable
        subst slack
        simp only [Option.map_some] at hspace
        obtain ⟨stop, hstop⟩ :=
          Allocations.freeIntervals_bounded _ _ _ hspace
        rcases space with ⟨spaceStart, spaceEnd⟩
        simp only at hstop
        subst spaceEnd
        exact (hallows.2 stop rfl).trans
          (Allocations.freeIntervals_end_le _ _ _ hspace)
  case case4 =>
    intro fuel allocations column rest hvalid hnodup hcolumn hlength
      hspaceSafety
    simp only [trySpaces]
    constructor
    · exact
        { valid := hvalid
          preserves := CircuitAllocations.Extends.refl allocations
          sameOutside := by intro candidate hcandidate; rfl
          records := by simp
          fits := by simp }
    · simp
  case case5 =>
    intro fuel allocations column rest spaceStart spaceEnd more hok
      recursiveAllocations row hrecursive inductionHypothesis
      hvalid hnodup hcolumn hlength hspaceSafety
    obtain ⟨hrecursiveLaw, hrecursiveWithin⟩ :=
      inductionHypothesis hvalid hnodup hlength
    rw [hrecursive] at hrecursiveLaw hrecursiveWithin
    have hallows := within_space_of_ok spaceStart spaceEnd length row hok
      (hrecursiveWithin row rfl)
    have hfitsOriginal := hspaceSafety (spaceStart, spaceEnd)
      (by simp) row hallows
    have hcolumnSame := hrecursiveLaw.sameOutside column hcolumn
    have hfitsRecursive :
        (recursiveAllocations.getD column #[]).Fits row length := by
      rw [hcolumnSame]
      exact hfitsOriginal
    let resultAllocations := recursiveAllocations.insert column
      ((recursiveAllocations.getD column #[]).insert row length)
    have hresultValid : CircuitAllocations.Valid resultAllocations :=
      CircuitAllocations.Valid.insertAllocation hrecursiveLaw.valid
        column row length hfitsRecursive hlength
    have hinsertExtends := CircuitAllocations.Extends.insertAllocation
      recursiveAllocations column row length
    simp only [trySpaces, hok, if_true, hrecursive]
    constructor
    · refine
        { valid := hresultValid
          preserves := hrecursiveLaw.preserves.trans hinsertExtends
          sameOutside := ?_
          records := ?_
          fits := ?_ }
      · intro candidate hcandidate
        have hinsertSame :=
          CircuitAllocations.SameOutside.insertAllocation
            recursiveAllocations column row length candidate
            (by
              intro heq
              apply hcandidate
              simp only [List.mem_cons]
              exact Or.inl (by simpa using heq))
        rw [hinsertSame]
        exact hrecursiveLaw.sameOutside candidate (by
          intro hrest
          apply hcandidate
          simp [hrest])
      · intro foundRow hfound
        have : foundRow = row := Option.some.inj hfound.symm
        subst foundRow
        intro candidate hcandidate
        simp only [List.mem_cons] at hcandidate
        rcases hcandidate with rfl | hrest
        · rw [Std.HashMap.getD_insert, if_pos]
          · exact Allocations.mem_insert _ _ _
          · simp
        · exact hinsertExtends candidate (row, length)
            (hrecursiveLaw.records row rfl candidate hrest)
      · intro foundRow hfound candidate hcandidate
        have : foundRow = row := Option.some.inj hfound.symm
        subst foundRow
        simp only [List.mem_cons] at hcandidate
        rcases hcandidate with rfl | hrest
        · exact hfitsOriginal
        · exact hrecursiveLaw.fits row rfl candidate hrest
    · intro foundRow hfound
      have : foundRow = row := Option.some.inj hfound.symm
      subst foundRow
      exact ⟨(spaceStart, spaceEnd), by simp, hallows⟩
  case case6 =>
    intro fuel allocations column rest spaceStart spaceEnd more hok
      recursiveAllocations hrecursive firstInduction spacesInduction
      hvalid hnodup hcolumn hlength hspaceSafety
    obtain ⟨hrecursiveLaw, hrecursiveWithin⟩ :=
      firstInduction hvalid hnodup hlength
    rw [hrecursive] at hrecursiveLaw hrecursiveWithin
    have hcolumnSame := hrecursiveLaw.sameOutside column hcolumn
    have hremainingSafety :
        ∀ space ∈ more, ∀ row,
          Allocations.SpaceAllows space row length →
            (recursiveAllocations.getD column #[]).Fits row length := by
      intro space hspace row hallows
      rw [hcolumnSame]
      exact hspaceSafety space (by simp [hspace]) row hallows
    obtain ⟨hremainingLaw, hremainingWitness⟩ :=
      spacesInduction hrecursiveLaw.valid hnodup hcolumn hlength
        hremainingSafety
    simp only [trySpaces, hok, if_true, hrecursive]
    constructor
    · refine
        { valid := hremainingLaw.valid
          preserves := hrecursiveLaw.preserves.trans
            hremainingLaw.preserves
          sameOutside := ?_
          records := hremainingLaw.records
          fits := ?_ }
      · intro candidate hcandidate
        rw [hremainingLaw.sameOutside candidate hcandidate]
        apply hrecursiveLaw.sameOutside candidate
        intro hrest
        apply hcandidate
        simp [hrest]
      · intro row hrow candidate hcandidate
        have hfits := hremainingLaw.fits row hrow candidate hcandidate
        intro interval hinterval
        exact hfits interval
          (hrecursiveLaw.preserves candidate interval hinterval)
    · intro row hrow
      obtain ⟨space, hspace, hallows⟩ :=
        hremainingWitness row hrow
      exact ⟨space, by simp [hspace], hallows⟩
  case case7 =>
    intro fuel allocations column rest spaceStart spaceEnd more hok
      inductionHypothesis hvalid hnodup hcolumn hlength hspaceSafety
    obtain ⟨hlaw, hwitness⟩ := inductionHypothesis
      hvalid hnodup hcolumn hlength (by
        intro space hspace row hallows
        exact hspaceSafety space (by simp [hspace]) row hallows)
    simp only [trySpaces, hok]
    exact ⟨hlaw, by
      intro row hrow
      obtain ⟨space, hspace, hallows⟩ := hwitness row hrow
      exact ⟨space, by simp [hspace], hallows⟩⟩

/-- A first-fit search changes a participating column by exactly one insertion on
success, and leaves every observable allocation unchanged on failure. -/
def PlacementEffect
    (before : CircuitAllocations) (columns : List RegionColumn)
    (length : ℕ) (result : Option ℕ × CircuitAllocations) : Prop :=
  ∀ column,
    result.2.getD column #[] =
      match result.1 with
      | none => before.getD column #[]
      | some row =>
          if column ∈ columns then
            (before.getD column #[]).insert row length
          else before.getD column #[]

theorem PlacementEffect.equivalent_before_of_none
    {before : CircuitAllocations} {columns : List RegionColumn}
    {length : ℕ} {result : Option ℕ × CircuitAllocations}
    (heffect : PlacementEffect before columns length result)
    (hresult : result.1 = none) : result.2.Equivalent before := by
  intro column
  rw [heffect column, hresult]

private def FirstFitEffect
    (fuel : ℕ) (allocations : CircuitAllocations)
    (columns : List RegionColumn) (length start : ℕ)
    (slack : Option ℕ) : Prop :=
  allocations.Valid → columns.Nodup → 0 < length →
    PlacementEffect allocations columns length
      (firstFit fuel allocations columns length start slack)

private def TrySpacesEffect
    (fuel : ℕ) (allocations : CircuitAllocations)
    (column : RegionColumn) (rest : List RegionColumn)
    (length : ℕ) (spaces : List (ℕ × Option ℕ)) : Prop :=
  allocations.Valid → rest.Nodup → column ∉ rest → 0 < length →
    PlacementEffect allocations (column :: rest) length
      (trySpaces fuel allocations column rest length spaces)

/-- Exact first-fit allocation effect. This proposition is intentionally separate
from `PlacementLaw`: consumers that only need safety do not pay to normalize the
algorithm's exact update. -/
theorem firstFit_effect
    (fuel : ℕ) (allocations : CircuitAllocations)
    (columns : List RegionColumn) (length start : ℕ)
    (slack : Option ℕ) :
    FirstFitEffect fuel allocations columns length start slack := by
  apply firstFit.induct (regionLen := length)
    (motive1 := fun fuel allocations columns start slack =>
      FirstFitEffect fuel allocations columns length start slack)
    (motive2 := fun fuel allocations column rest spaces =>
      TrySpacesEffect fuel allocations column rest length spaces)
  all_goals simp only [FirstFitEffect, TrySpacesEffect]
  case case1 =>
    intro fuel allocations start slack _ _ _ column
    simp [firstFit]
  case case2 =>
    intro allocations start slack head tail _ _ _ column
    simp [firstFit]
  case case3 =>
    intro allocations start slack fuel column rest inductionHypothesis
      hvalid hnodup hlength
    have hrestNodup := List.nodup_cons.mp hnodup |>.2
    have hcolumnRest := List.nodup_cons.mp hnodup |>.1
    let initialized :=
      allocations.insert column (allocations.getD column #[])
    have hinitializedValid : CircuitAllocations.Valid initialized :=
      CircuitAllocations.Valid.insertSame hvalid column
    have heffect := inductionHypothesis hinitializedValid hrestNodup
      hcolumnRest hlength
    simp only [firstFit]
    intro candidate
    have hinitialized :
        initialized.getD candidate #[] = allocations.getD candidate #[] := by
      simp only [initialized, Std.HashMap.getD_insert]
      split <;> rename_i heq
      · exact congrArg (fun found => allocations.getD found #[])
          (beq_iff_eq.mp heq)
      · rfl
    specialize heffect candidate
    rw [heffect, hinitialized]
  case case4 =>
    intro fuel allocations column rest _ _ _ _ candidate
    simp [trySpaces]
  case case5 =>
    intro fuel allocations column rest spaceStart spaceEnd more hok
      recursiveAllocations row hrecursive inductionHypothesis
      hvalid hnodup hcolumn hlength
    have hrecursiveEffect := inductionHypothesis hvalid hnodup hlength
    rw [hrecursive] at hrecursiveEffect
    simp only [trySpaces, hok, if_true, hrecursive]
    intro candidate
    simp only [PlacementEffect] at hrecursiveEffect ⊢
    rw [Std.HashMap.getD_insert]
    split <;> rename_i heq
    · have hcandidate : column = candidate := beq_iff_eq.mp heq
      subst candidate
      rw [if_pos (by simp)]
      rw [hrecursiveEffect]
      simp [hcolumn]
    · have hcandidate : column ≠ candidate := by
        intro h
        subst candidate
        simp at heq
      rw [hrecursiveEffect]
      by_cases hrest : candidate ∈ rest
      · simp [hrest]
      · simp [hrest, hcandidate.symm]
  case case6 =>
    intro fuel allocations column rest spaceStart spaceEnd more hok
      recursiveAllocations hrecursive firstInduction spacesInduction
      hvalid hnodup hcolumn hlength
    have hrecursiveEffect := firstInduction hvalid hnodup hlength
    rw [hrecursive] at hrecursiveEffect
    have hrecursiveValid :=
      (firstFit_law fuel allocations rest length spaceStart
        ((spaceEnd.map fun endRow =>
          (endRow : ℤ) - spaceStart - length).map Int.toNat)
        hvalid hnodup hlength).1.valid
    rw [hrecursive] at hrecursiveValid
    have hremainingEffect := spacesInduction hrecursiveValid hnodup
      hcolumn hlength
    simp only [trySpaces, hok, if_true, hrecursive]
    intro candidate
    simp only [PlacementEffect] at hrecursiveEffect hremainingEffect ⊢
    specialize hrecursiveEffect candidate
    specialize hremainingEffect candidate
    rw [hremainingEffect, hrecursiveEffect]
  case case7 =>
    intro fuel allocations column rest spaceStart spaceEnd more hok
      inductionHypothesis hvalid hnodup hcolumn hlength
    simpa only [trySpaces, hok] using
      inductionHypothesis hvalid hnodup hcolumn hlength

/-- If the requested row fits every column, first-fit accepts it immediately. -/
theorem firstFit_row_eq_start_of_fits
    (fuel : ℕ) (allocations : CircuitAllocations)
    (columns : List RegionColumn) (length start : ℕ)
    (slack : Option ℕ)
    (hvalid : allocations.Valid) (hnodup : columns.Nodup)
    (hlength : 0 < length) (hfuel : columns.length ≤ fuel)
    (hfits : ∀ column ∈ columns,
      (allocations.getD column #[]).Fits start length)
    (hbound : ∀ available, slack = some available →
      start + length ≤ start + length + available) :
    (firstFit fuel allocations columns length start slack).1 = some start := by
  induction columns generalizing fuel allocations slack with
  | nil =>
      simp [firstFit]
  | cons column rest inductionHypothesis =>
      cases fuel with
      | zero => simp at hfuel
      | succ fuel =>
          have hrestNodup := List.nodup_cons.mp hnodup |>.2
          have hcolumnRest := List.nodup_cons.mp hnodup |>.1
          have hrestFuel : rest.length ≤ fuel := by
            simpa using hfuel
          let initialized :=
            allocations.insert column (allocations.getD column #[])
          have hinitializedValid : CircuitAllocations.Valid initialized :=
            CircuitAllocations.Valid.insertSame hvalid column
          have hinitialized : ∀ candidate,
              initialized.getD candidate #[] =
                allocations.getD candidate #[] := by
            intro candidate
            simp only [initialized, Std.HashMap.getD_insert]
            split <;> rename_i heq
            · exact congrArg (fun found => allocations.getD found #[])
                (beq_iff_eq.mp heq)
            · rfl
          have hrestFits : ∀ candidate ∈ rest,
              (initialized.getD candidate #[]).Fits start length := by
            intro candidate hcandidate
            rw [hinitialized]
            exact hfits candidate (by simp [hcandidate])
          obtain ⟨stop, more, hspaces, hallows⟩ :=
            Allocations.freeIntervals_starts_with_of_fits
              (allocations.getD column #[]) start length
              (slack.map fun available => start + length + available)
              (hvalid column) (hfits column (by simp)) hlength (by
                intro stop hstop
                obtain ⟨available, havailable, rfl⟩ :=
                  Option.map_eq_some_iff.mp hstop
                exact hbound available havailable)
          cases stop with
          | none =>
              have hrest := inductionHypothesis fuel initialized none
                hinitializedValid hrestNodup hrestFuel hrestFits (by simp)
              dsimp only [initialized] at hrest
              simp [firstFit, hspaces, trySpaces]
              rw [hrest]
          | some stop =>
              have hstop : start + length ≤ stop := hallows.2 stop rfl
              have hrest := inductionHypothesis fuel initialized
                (some ((stop : ℤ) - start - length).toNat)
                hinitializedValid hrestNodup hrestFuel hrestFits (by
                  intro available havailable
                  simp only [Option.some.injEq] at havailable
                  subst available
                  omega)
              dsimp only [initialized] at hrest
              have hslack :
                  ((stop : ℤ) - start - length).toNat =
                    stop - start - length := by
                omega
              rw [hslack] at hrest
              have hwidth : (length : ℤ) ≤ stop - start := by omega
              simp [firstFit, hspaces, trySpaces, hwidth]
              rw [hrest]

/-- First-fit is complete below any fitting candidate: with sufficient fuel it
returns a row no later than that candidate. Together with `firstFit_law`, this
characterizes the selected row as the least common fit. -/
theorem firstFit_row_le_fitting_candidate
    (fuel : ℕ) (allocations : CircuitAllocations)
    (columns : List RegionColumn) (length start : ℕ)
    (slack : Option ℕ) (candidate : ℕ)
    (hvalid : allocations.Valid) (hnodup : columns.Nodup)
    (hlength : 0 < length) (hfuel : columns.length ≤ fuel)
    (hstart : start ≤ candidate)
    (hbound : ∀ available, slack = some available →
      candidate + length ≤ start + length + available)
    (hfits : ∀ column ∈ columns,
      (allocations.getD column #[]).Fits candidate length) :
    ∃ row updated,
      firstFit fuel allocations columns length start slack =
        (some row, updated) ∧ row ≤ candidate := by
  induction columns generalizing fuel allocations start slack with
  | nil =>
      exact ⟨start, allocations, by simp [firstFit], hstart⟩
  | cons column rest inductionHypothesis =>
      cases fuel with
      | zero => simp at hfuel
      | succ fuel =>
          have hrestNodup := List.nodup_cons.mp hnodup |>.2
          have hcolumnRest := List.nodup_cons.mp hnodup |>.1
          have hrestFuel : rest.length ≤ fuel := by
            simpa using hfuel
          let initialized :=
            allocations.insert column (allocations.getD column #[])
          have hinitializedValid : CircuitAllocations.Valid initialized :=
            CircuitAllocations.Valid.insertSame hvalid column
          have hinitializedEquivalent :
              CircuitAllocations.Equivalent initialized allocations := by
            intro current
            simp only [initialized, Std.HashMap.getD_insert]
            split <;> rename_i heq
            · exact congrArg (fun found => allocations.getD found #[])
                (beq_iff_eq.mp heq)
            · rfl
          have hrestFits : ∀ current ∈ rest,
              (initialized.getD current #[]).Fits candidate length := by
            intro current hcurrent
            rw [hinitializedEquivalent current]
            exact hfits current (by simp [hcurrent])
          let endBound := slack.map fun available =>
            start + length + available
          let spaces := (allocations.getD column #[]).freeIntervals
            start endBound
          have hcandidateBound : ∀ stop, endBound = some stop →
              candidate + length ≤ stop := by
            intro stop hstop
            obtain ⟨available, havailable, rfl⟩ :=
              Option.map_eq_some_iff.mp hstop
            exact hbound available havailable
          obtain ⟨candidateSpace, hcandidateSpace, hcandidateAllows⟩ :=
            Allocations.exists_freeInterval_of_fits
              (allocations.getD column #[]) start candidate length endBound
              (hvalid column) hstart hlength (hfits column (by simp))
              hcandidateBound
          have hspacesPairwise : spaces.Pairwise Allocations.SpaceBefore := by
            exact Allocations.freeIntervals_pairwise _ _ _
          have tryComplete : ∀ (remaining : List (ℕ × Option ℕ))
              (current : CircuitAllocations),
              current.Valid →
              (∀ item ∈ rest,
                (current.getD item #[]).Fits candidate length) →
              remaining.Pairwise Allocations.SpaceBefore →
              candidateSpace ∈ remaining →
              ∃ row updated,
                trySpaces fuel current column rest length remaining =
                  (some row, updated) ∧ row ≤ candidate := by
            intro remaining
            induction remaining with
            | nil => simp
            | cons space more spacesInduction =>
                intro current hcurrentValid hcurrentFits hpairwise hwitness
                rw [List.pairwise_cons] at hpairwise
                simp only [List.mem_cons] at hwitness
                rcases space with ⟨spaceStart, spaceEnd⟩
                let available : Option ℤ := spaceEnd.map fun stop =>
                  (stop : ℤ) - spaceStart - length
                let ok : Bool := match available with
                  | some value => decide (value ≥ 0)
                  | none => true
                by_cases hok : ok = true
                · have hrecursiveLaw := firstFit_law fuel current rest length
                    spaceStart (available.map Int.toNat) hcurrentValid
                    hrestNodup hlength
                  generalize hrecursive : firstFit fuel current rest length
                    spaceStart (available.map Int.toNat) = recursive
                      at hrecursiveLaw
                  rcases recursive with ⟨rowOption, recursiveAllocations⟩
                  cases rowOption with
                  | some row =>
                      have hrow : row ≤ candidate := by
                        rcases hwitness with hwitnessHead | hwitnessTail
                        · have : (spaceStart, spaceEnd) = candidateSpace :=
                            hwitnessHead.symm
                          subst candidateSpace
                          have hrecursiveComplete := inductionHypothesis fuel
                            current spaceStart
                            (available.map Int.toNat) hcurrentValid
                            hrestNodup hrestFuel hcandidateAllows.1
                            (by
                              intro bounded hbounded
                              cases spaceEnd with
                              | none => simp [available] at hbounded
                              | some stop =>
                                  change some
                                    (((stop : ℤ) - spaceStart - length).toNat) =
                                      some bounded at hbounded
                                  simp only [Option.some.injEq] at hbounded
                                  have hok' :
                                      (0 : ℤ) ≤ (stop : ℤ) - spaceStart - length := by
                                    simpa [ok, available] using hok
                                  have hcandidateEnd :=
                                    hcandidateAllows.2 stop rfl
                                  have htoNat :
                                      ((stop : ℤ) - spaceStart - length).toNat =
                                        stop - spaceStart - length := by omega
                                  rw [htoNat] at hbounded
                                  omega)
                            hcurrentFits
                          obtain ⟨found, updated, hfound, hfoundLe⟩ :=
                            hrecursiveComplete
                          rw [hrecursive] at hfound
                          simp only [Prod.mk.injEq, Option.some.injEq] at hfound
                          omega
                        · have hbefore := hpairwise.1 candidateSpace
                            hwitnessTail
                          obtain ⟨stop, hspaceEnd, hstopLe⟩ := hbefore
                          have hwithin := hrecursiveLaw.2 row rfl
                          have hallows := within_space_of_ok spaceStart
                            spaceEnd length row (by simpa [ok, available] using hok)
                            hwithin
                          have hcandidateStart := hcandidateAllows.1
                          have hrowEnd := hallows.2 stop hspaceEnd
                          omega
                      refine ⟨row, recursiveAllocations.insert column
                        ((recursiveAllocations.getD column #[]).insert row length),
                        ?_, hrow⟩
                      have hok' :
                          (match spaceEnd.map fun stop =>
                              (stop : ℤ) - spaceStart - length with
                            | some value => decide (value ≥ 0)
                            | none => true) = true := by
                        simpa only [ok, available] using hok
                      simp only [trySpaces, hok', if_true]
                      change (match (firstFit fuel current rest length
                        spaceStart (available.map Int.toNat)).1 with
                        | some found =>
                          (some found, (firstFit fuel current rest length
                            spaceStart (available.map Int.toNat)).2.insert
                              column (((firstFit fuel current rest length
                                spaceStart (available.map Int.toNat)).2.getD
                                  column #[]).insert found length))
                        | none => trySpaces fuel
                          (firstFit fuel current rest length spaceStart
                            (available.map Int.toNat)).2 column rest length more) = _
                      rw [hrecursive]
                  | none =>
                      have hrecursiveEffect := firstFit_effect fuel current rest
                        length spaceStart (available.map Int.toNat)
                        hcurrentValid hrestNodup hlength
                      rw [hrecursive] at hrecursiveEffect
                      have hequivalent :=
                        hrecursiveEffect.equivalent_before_of_none rfl
                      have hnextFits : ∀ item ∈ rest,
                          (recursiveAllocations.getD item #[]).Fits
                            candidate length := by
                        intro item hitem
                        rw [hequivalent item]
                        exact hcurrentFits item hitem
                      have hwitnessTail : candidateSpace ∈ more := by
                        rcases hwitness with hwitnessHead | hwitnessTail
                        · have : (spaceStart, spaceEnd) = candidateSpace :=
                            hwitnessHead.symm
                          subst candidateSpace
                          have hrecursiveComplete := inductionHypothesis fuel
                            current spaceStart
                            (available.map Int.toNat) hcurrentValid
                            hrestNodup hrestFuel hcandidateAllows.1
                            (by
                              intro bounded hbounded
                              cases spaceEnd with
                              | none => simp [available] at hbounded
                              | some stop =>
                                  change some
                                    (((stop : ℤ) - spaceStart - length).toNat) =
                                      some bounded at hbounded
                                  simp only [Option.some.injEq] at hbounded
                                  have hok' :
                                      (0 : ℤ) ≤ (stop : ℤ) - spaceStart - length := by
                                    simpa [ok, available] using hok
                                  have hcandidateEnd :=
                                    hcandidateAllows.2 stop rfl
                                  have htoNat :
                                      ((stop : ℤ) - spaceStart - length).toNat =
                                        stop - spaceStart - length := by omega
                                  rw [htoNat] at hbounded
                                  omega)
                            hcurrentFits
                          obtain ⟨found, updated, hfound, _⟩ :=
                            hrecursiveComplete
                          rw [hrecursive] at hfound
                          cases hfound
                        · exact hwitnessTail
                      obtain ⟨row, updated, hresult, hrow⟩ :=
                        spacesInduction recursiveAllocations
                          hrecursiveLaw.1.valid hnextFits hpairwise.2 hwitnessTail
                      have hok' :
                          (match spaceEnd.map fun stop =>
                              (stop : ℤ) - spaceStart - length with
                            | some value => decide (value ≥ 0)
                            | none => true) = true := by
                        simpa only [ok, available] using hok
                      exact ⟨row, updated, by
                        simp only [trySpaces, hok', if_true]
                        change (match (firstFit fuel current rest length
                          spaceStart (available.map Int.toNat)).1 with
                          | some found => _
                          | none => trySpaces fuel
                            (firstFit fuel current rest length spaceStart
                              (available.map Int.toNat)).2 column rest length more) = _
                        rw [hrecursive, hresult], hrow⟩
                · have hwitnessTail : candidateSpace ∈ more := by
                    rcases hwitness with hwitnessHead | hwitnessTail
                    · have : (spaceStart, spaceEnd) = candidateSpace :=
                        hwitnessHead.symm
                      subst candidateSpace
                      cases spaceEnd with
                      | none => simp [ok, available] at hok
                      | some stop =>
                          have hwidth := hcandidateAllows.2 stop rfl
                          have hstartCandidate := hcandidateAllows.1
                          apply False.elim
                          apply hok
                          change decide
                            ((0 : ℤ) ≤ (stop : ℤ) - spaceStart - length) = true
                          rw [decide_eq_true_eq]
                          omega
                    · exact hwitnessTail
                  obtain ⟨row, updated, hresult, hrow⟩ :=
                    spacesInduction current hcurrentValid hcurrentFits
                      hpairwise.2 hwitnessTail
                  have hok' :
                      ¬(match spaceEnd.map fun stop =>
                          (stop : ℤ) - spaceStart - length with
                        | some value => decide (value ≥ 0)
                        | none => true) = true := by
                    simpa only [ok, available] using hok
                  exact ⟨row, updated, by
                    simp only [trySpaces, if_neg hok', hresult], hrow⟩
          obtain ⟨row, updated, hresult, hrow⟩ := tryComplete spaces
            initialized hinitializedValid hrestFits hspacesPairwise
            hcandidateSpace
          refine ⟨row, updated, ?_, hrow⟩
          simp only [firstFit]
          simpa only [initialized, spaces, endBound] using hresult
/-- Every column in a footprint admits the candidate interval. -/
def FitsColumns (allocations : CircuitAllocations)
    (columns : List RegionColumn) (start length : ℕ) : Prop :=
  ∀ column ∈ columns,
    (allocations.getD column #[]).Fits start length

/-- A row is the first common fit for a footprint. This is the declarative
counterpart of V1's operational first-fit search. -/
def LeastFit (allocations : CircuitAllocations)
    (columns : List RegionColumn) (length row : ℕ) : Prop :=
  FitsColumns allocations columns row length ∧
    ∀ candidate, FitsColumns allocations columns candidate length →
      row ≤ candidate

/-- The operational allocator chooses a declaratively least fitting row. -/
theorem firstFit_eq_of_leastFit
    (fuel : ℕ) (allocations : CircuitAllocations)
    (columns : List RegionColumn) (length start row : ℕ)
    (slack : Option ℕ)
    (hvalid : allocations.Valid) (hnodup : columns.Nodup)
    (hlength : 0 < length) (hfuel : columns.length ≤ fuel)
    (hstart : start ≤ row)
    (hbound : ∀ available, slack = some available →
      row + length ≤ start + length + available)
    (hleast : LeastFit allocations columns length row) :
    ∃ updated,
      firstFit fuel allocations columns length start slack =
        (some row, updated) := by
  obtain ⟨found, updated, hresult, hfoundLe⟩ :=
    firstFit_row_le_fitting_candidate fuel allocations columns length
      start slack row hvalid hnodup hlength hfuel hstart hbound hleast.1
  have hlaw := firstFit_law fuel allocations columns length start slack
    hvalid hnodup hlength
  rw [hresult] at hlaw
  have hrowLe : row ≤ found := hleast.2 found (hlaw.1.fits found rfl)
  have : found = row := Nat.le_antisymm hfoundLe hrowLe
  subst found
  exact ⟨updated, hresult⟩

theorem FitsColumns.congruent
    {left right : CircuitAllocations} {columns : List RegionColumn}
    {start length : ℕ} (hequivalent : left.Equivalent right)
    (hfits : FitsColumns left columns start length) :
    FitsColumns right columns start length := by
  intro column hcolumn
  rw [← hequivalent column]
  exact hfits column hcolumn

theorem FitsColumns.append
    {allocations : CircuitAllocations} {left right : List RegionColumn}
    {start length : ℕ}
    (hleft : FitsColumns allocations left start length)
    (hright : FitsColumns allocations right start length) :
    FitsColumns allocations (left ++ right) start length := by
  intro column hcolumn
  rw [List.mem_append] at hcolumn
  exact hcolumn.elim (hleft column) (hright column)

theorem FitsColumns.mono
    {allocations : CircuitAllocations} {inner outer : List RegionColumn}
    {start length : ℕ} (hfits : FitsColumns allocations outer start length)
    (hsubset : inner ⊆ outer) : FitsColumns allocations inner start length := by
  intro column hcolumn
  exact hfits column (hsubset hcolumn)

/-- The already-processed prefix fits every row still inside a recursive search
window. -/
def SearchPrefixFits (allocations : CircuitAllocations)
    (processed : List RegionColumn) (length start : ℕ)
    (slack : Option ℕ) : Prop :=
  ∀ row, Within start slack length row →
    FitsColumns allocations processed row length

/-- The retained columns dominate a suffix when fitting all retained columns always
implies fitting the suffix. -/
def ColumnsDominate (allocations : CircuitAllocations)
    (retained suffix : List RegionColumn) (length : ℕ) : Prop :=
  ∀ row, FitsColumns allocations retained row length →
    FitsColumns allocations suffix row length

/-- Removing a suffix whose allocation constraints are already implied by retained
columns preserves first-fit's selected row. -/
theorem firstFit_drop_dominated_suffix
    (fuel : ℕ) (left right : CircuitAllocations)
    (processed retained suffix : List RegionColumn)
    (length start : ℕ) (slack : Option ℕ)
    (hvalidLeft : left.Valid) (hvalidRight : right.Valid)
    (hequivalent : left.Equivalent right)
    (hnodup : (retained ++ suffix).Nodup)
    (hlength : 0 < length)
    (hfuel : (retained ++ suffix).length ≤ fuel)
    (hsearch : SearchPrefixFits left processed length start slack)
    (hdominate : ColumnsDominate left (processed ++ retained) suffix length) :
    (firstFit fuel left (retained ++ suffix) length start slack).1 =
      (firstFit fuel right retained length start slack).1 := by
  induction retained generalizing fuel left right processed start slack with
  | nil =>
      have hsuffixNodup : suffix.Nodup := by simpa using hnodup
      have hsuffixFuel : suffix.length ≤ fuel := by simpa using hfuel
      have hwithin : Within start slack length start := by
        exact ⟨le_rfl, by intro available _; omega⟩
      have hprocessed := hsearch start hwithin
      have hsuffixFits : FitsColumns left suffix start length := by
        apply hdominate start
        simpa using hprocessed
      have hfull := firstFit_row_eq_start_of_fits fuel left suffix
        length start slack hvalidLeft hsuffixNodup hlength hsuffixFuel
        hsuffixFits (by intro available _; omega)
      simpa [firstFit] using hfull
  | cons head rest inductionHypothesis =>
      cases fuel with
      | zero => simp at hfuel
      | succ fuel =>
          have hfullNodup : (head :: (rest ++ suffix)).Nodup := by
            simpa only [List.cons_append] using hnodup
          have hrestSuffixNodup : (rest ++ suffix).Nodup :=
            List.nodup_cons.mp hfullNodup |>.2
          have hheadRestSuffix : head ∉ rest ++ suffix :=
            List.nodup_cons.mp hfullNodup |>.1
          have hrestFuel : (rest ++ suffix).length ≤ fuel := by
            simpa only [List.length_cons] using
              Nat.le_of_succ_le_succ hfuel
          let leftInitialized :=
            left.insert head (left.getD head #[])
          let rightInitialized :=
            right.insert head (right.getD head #[])
          have hleftInitializedValid :
              CircuitAllocations.Valid leftInitialized :=
            CircuitAllocations.Valid.insertSame hvalidLeft head
          have hrightInitializedValid :
              CircuitAllocations.Valid rightInitialized :=
            CircuitAllocations.Valid.insertSame hvalidRight head
          have hinitializedEquivalent :
              CircuitAllocations.Equivalent leftInitialized
                rightInitialized := by
            intro column
            simp only [leftInitialized, rightInitialized,
              Std.HashMap.getD_insert]
            split <;> rename_i heq
            · have : head = column := beq_iff_eq.mp heq
              subst column
              exact congrArg (fun values => values) (hequivalent head)
            · exact hequivalent column
          have hleftInitialized :
              CircuitAllocations.Equivalent leftInitialized left := by
            intro column
            simp only [leftInitialized, Std.HashMap.getD_insert]
            split <;> rename_i heq
            · exact congrArg (fun found => left.getD found #[])
                (beq_iff_eq.mp heq)
            · rfl
          have hrightInitialized :
              CircuitAllocations.Equivalent rightInitialized right := by
            intro column
            simp only [rightInitialized, Std.HashMap.getD_insert]
            split <;> rename_i heq
            · exact congrArg (fun found => right.getD found #[])
                (beq_iff_eq.mp heq)
            · rfl
          have hspaces :
              (left.getD head #[]).freeIntervals start
                  (slack.map fun available => start + length + available) =
                (right.getD head #[]).freeIntervals start
                  (slack.map fun available => start + length + available) := by
            rw [hequivalent head]
          let spaces := (left.getD head #[]).freeIntervals start
            (slack.map fun available => start + length + available)
          have hspaceSafety : ∀ space ∈ spaces, ∀ row,
              Allocations.SpaceAllows space row length →
                (leftInitialized.getD head #[]).Fits row length := by
            intro space hspace row hallows
            have hfits := Allocations.freeIntervals_fits
              (left.getD head #[]) start
              (slack.map fun available => start + length + available)
              (hvalidLeft head) hspace hallows
            rw [hleftInitialized head]
            exact hfits
          have hspaceWithin : ∀ space ∈ spaces, ∀ row,
              Allocations.SpaceAllows space row length →
                Within start slack length row := by
            intro space hspace row hallows
            constructor
            · exact (Allocations.freeIntervals_start_le _ _ _ hspace).trans
                hallows.1
            · intro available havailable
              subst slack
              obtain ⟨stop, hstop⟩ :=
                Allocations.freeIntervals_bounded _ _ _ hspace
              rcases space with ⟨spaceStart, spaceEnd⟩
              simp only at hstop
              subst spaceEnd
              exact (hallows.2 stop rfl).trans
                (Allocations.freeIntervals_end_le _ _ _ hspace)
          have compareSpaces : ∀ (remaining : List (ℕ × Option ℕ))
              (currentLeft currentRight : CircuitAllocations),
              currentLeft.Valid → currentRight.Valid →
              currentLeft.Equivalent currentRight →
              currentLeft.Equivalent leftInitialized →
              currentRight.Equivalent rightInitialized →
              (∀ space ∈ remaining, ∀ row,
                Allocations.SpaceAllows space row length →
                  (currentLeft.getD head #[]).Fits row length) →
              (∀ space ∈ remaining, ∀ row,
                Allocations.SpaceAllows space row length →
                  Within start slack length row) →
              (trySpaces fuel currentLeft head (rest ++ suffix)
                  length remaining).1 =
                (trySpaces fuel currentRight head rest length remaining).1 := by
            intro remaining
            induction remaining with
            | nil =>
                intro currentLeft currentRight _ _ _ _ _ _ _
                simp [trySpaces]
            | cons space more spacesInduction =>
                rcases space with ⟨spaceStart, spaceEnd⟩
                intro currentLeft currentRight hcurrentLeftValid
                  hcurrentRightValid hcurrentEquivalent hcurrentLeft
                  hcurrentRight hremainingSafety hremainingWithin
                let available : Option ℤ := spaceEnd.map fun stop =>
                  (stop : ℤ) - spaceStart - length
                let ok : Bool := match available with
                  | some value => decide (value ≥ 0)
                  | none => true
                have havailable :
                    (spaceEnd.map fun stop =>
                      (stop : ℤ) - spaceStart - length) = available := rfl
                by_cases hok : ok = true
                · have hallowsOfWithin : ∀ row,
                      Within spaceStart (available.map Int.toNat) length row →
                        Allocations.SpaceAllows
                          (spaceStart, spaceEnd) row length := by
                    intro row hwithin
                    apply within_space_of_ok spaceStart spaceEnd length row
                      (by simpa only [ok, available] using hok)
                    exact hwithin
                  have hrecursiveSearch : SearchPrefixFits currentLeft
                      (processed ++ [head]) length spaceStart
                      (available.map Int.toNat) := by
                    intro row hwithin
                    have hallows := hallowsOfWithin row hwithin
                    have houterWithin := hremainingWithin
                      (spaceStart, spaceEnd) (by simp) row hallows
                    have hprocessedFits := hsearch row houterWithin
                    have hprocessedCurrent := hprocessedFits.congruent
                      (hcurrentLeft.trans hleftInitialized).symm
                    have hheadFits := hremainingSafety
                      (spaceStart, spaceEnd) (by simp) row hallows
                    exact hprocessedCurrent.append (by
                      intro column hcolumn
                      simp only [List.mem_singleton] at hcolumn
                      subst column
                      exact hheadFits)
                  have hrecursiveDominate : ColumnsDominate currentLeft
                      ((processed ++ [head]) ++ rest) suffix length := by
                    intro row hfits
                    have hcurrent : FitsColumns currentLeft
                        (processed ++ head :: rest) row length := by
                      simpa only [List.append_assoc,
                        List.singleton_append] using hfits
                    have horiginal := hcurrent.congruent
                      (hcurrentLeft.trans hleftInitialized)
                    have hsuffixFits := hdominate row horiginal
                    exact hsuffixFits.congruent
                      (hcurrentLeft.trans hleftInitialized).symm
                  have hrecursiveRows := inductionHypothesis fuel
                    currentLeft currentRight (processed ++ [head])
                    spaceStart (available.map Int.toNat)
                    hcurrentLeftValid hcurrentRightValid hcurrentEquivalent
                    hrestSuffixNodup hrestFuel hrecursiveSearch
                    hrecursiveDominate
                  generalize hfull : firstFit fuel currentLeft
                    (rest ++ suffix) length spaceStart
                      (available.map Int.toNat) = fullResult at hrecursiveRows
                  rcases fullResult with ⟨fullRow, fullAllocations⟩
                  generalize hcore : firstFit fuel currentRight rest length
                    spaceStart (available.map Int.toNat) = coreResult
                      at hrecursiveRows
                  rcases coreResult with ⟨coreRow, coreAllocations⟩
                  dsimp only at hrecursiveRows
                  cases fullRow with
                  | some row =>
                      have hcoreRow : coreRow = some row := hrecursiveRows.symm
                      subst coreRow
                      simp only [trySpaces]
                      change ((if ok = true then _ else _) :
                          Option ℕ × CircuitAllocations).1 =
                        ((if ok = true then _ else _) :
                          Option ℕ × CircuitAllocations).1
                      simp only [if_pos hok]
                      rw [havailable, hfull, hcore]
                  | none =>
                      have hcoreRow : coreRow = none := hrecursiveRows.symm
                      subst coreRow
                      have hfullEffect := firstFit_effect fuel currentLeft
                        (rest ++ suffix) length spaceStart
                        (available.map Int.toNat) hcurrentLeftValid
                        hrestSuffixNodup hlength
                      rw [hfull] at hfullEffect
                      have hcoreEffect := firstFit_effect fuel currentRight
                        rest length spaceStart (available.map Int.toNat)
                        hcurrentRightValid
                        hrestSuffixNodup.of_append_left hlength
                      rw [hcore] at hcoreEffect
                      have hfullEquivalent :=
                        hfullEffect.equivalent_before_of_none rfl
                      have hcoreEquivalent :=
                        hcoreEffect.equivalent_before_of_none rfl
                      have hnextEquivalent :
                          fullAllocations.Equivalent coreAllocations :=
                        hfullEquivalent.trans
                          (hcurrentEquivalent.trans hcoreEquivalent.symm)
                      have hnextSafety : ∀ next ∈ more, ∀ candidate,
                          Allocations.SpaceAllows next candidate length →
                            (fullAllocations.getD head #[]).Fits
                              candidate length := by
                        intro next hnext candidate hallows
                        rw [hfullEquivalent head]
                        exact hremainingSafety next (by simp [hnext])
                          candidate hallows
                      have hfullValid :=
                        (firstFit_law fuel currentLeft (rest ++ suffix)
                          length spaceStart (available.map Int.toNat)
                          hcurrentLeftValid hrestSuffixNodup hlength).1.valid
                      rw [hfull] at hfullValid
                      have hcoreValid :=
                        (firstFit_law fuel currentRight rest length spaceStart
                          (available.map Int.toNat) hcurrentRightValid
                          hrestSuffixNodup.of_append_left hlength).1.valid
                      rw [hcore] at hcoreValid
                      have hnext := spacesInduction fullAllocations
                        coreAllocations hfullValid hcoreValid
                        hnextEquivalent
                        (hfullEquivalent.trans hcurrentLeft)
                        (hcoreEquivalent.trans hcurrentRight) hnextSafety
                        (by
                          intro next hnext candidate hallows
                          exact hremainingWithin next (by simp [hnext])
                            candidate hallows)
                      simp only [trySpaces]
                      change ((if ok = true then _ else _) :
                          Option ℕ × CircuitAllocations).1 =
                        ((if ok = true then _ else _) :
                          Option ℕ × CircuitAllocations).1
                      simp only [if_pos hok]
                      rw [havailable, hfull, hcore]
                      exact hnext
                · have hnextSafety : ∀ next ∈ more, ∀ candidate,
                      Allocations.SpaceAllows next candidate length →
                        (currentLeft.getD head #[]).Fits candidate length := by
                    intro next hnext candidate hallows
                    exact hremainingSafety next (by simp [hnext]) candidate hallows
                  have hnext := spacesInduction currentLeft currentRight
                    hcurrentLeftValid hcurrentRightValid hcurrentEquivalent
                    hcurrentLeft hcurrentRight hnextSafety
                    (by
                      intro next hnext candidate hallows
                      exact hremainingWithin next (by simp [hnext])
                        candidate hallows)
                  simp only [trySpaces]
                  change ((if ok = true then _ else _) :
                      Option ℕ × CircuitAllocations).1 =
                    ((if ok = true then _ else _) :
                      Option ℕ × CircuitAllocations).1
                  simpa only [if_neg hok] using hnext
          have hresult := compareSpaces spaces leftInitialized rightInitialized
            hleftInitializedValid hrightInitializedValid hinitializedEquivalent
            (CircuitAllocations.Equivalent.refl leftInitialized)
            (CircuitAllocations.Equivalent.refl rightInitialized) hspaceSafety
            hspaceWithin
          simp only [List.cons_append, firstFit]
          rw [← hspaces]
          simpa only [leftInitialized, rightInitialized, spaces] using hresult


private def FirstFitCongruent
    (fuel : ℕ) (allocations : CircuitAllocations)
    (columns : List RegionColumn) (length start : ℕ)
    (slack : Option ℕ) : Prop :=
  ∀ other, allocations.Valid → other.Valid → columns.Nodup →
    0 < length → allocations.AgreesOn other columns →
    let left := firstFit fuel allocations columns length start slack
    let right := firstFit fuel other columns length start slack
    left.1 = right.1 ∧ left.2.AgreesOn right.2 columns

private def TrySpacesCongruent
    (fuel : ℕ) (allocations : CircuitAllocations)
    (column : RegionColumn) (rest : List RegionColumn)
    (length : ℕ) (spaces : List (ℕ × Option ℕ)) : Prop :=
  ∀ other, allocations.Valid → other.Valid → rest.Nodup →
    column ∉ rest → 0 < length →
    allocations.AgreesOn other (column :: rest) →
    let left := trySpaces fuel allocations column rest length spaces
    let right := trySpaces fuel other column rest length spaces
    left.1 = right.1 ∧ left.2.AgreesOn right.2 (column :: rest)

/-- First-fit's result on a region depends only on that region's columns. -/
theorem firstFit_congruent
    (fuel : ℕ) (allocations : CircuitAllocations)
    (columns : List RegionColumn) (length start : ℕ)
    (slack : Option ℕ) :
    FirstFitCongruent fuel allocations columns length start slack := by
  apply firstFit.induct (regionLen := length)
    (motive1 := fun fuel allocations columns start slack =>
      FirstFitCongruent fuel allocations columns length start slack)
    (motive2 := fun fuel allocations column rest spaces =>
      TrySpacesCongruent fuel allocations column rest length spaces)
  all_goals simp only [FirstFitCongruent, TrySpacesCongruent]
  case case1 =>
    intro fuel allocations start slack other _ _ _ _ _
    simp only [firstFit]
    exact ⟨True.intro, by intro column hcolumn; simp at hcolumn⟩
  case case2 =>
    intro allocations start slack head tail other _ _ hnodup _ hagree
    simp only [firstFit]
    exact ⟨True.intro, hagree⟩
  case case3 =>
    intro allocations start slack fuel column rest inductionHypothesis
      other hvalidLeft hvalidRight hnodup hlength hagree
    have hrestNodup := List.nodup_cons.mp hnodup |>.2
    have hcolumnRest := List.nodup_cons.mp hnodup |>.1
    have hcolumn := hagree column (by simp)
    let leftInitialized :=
      allocations.insert column (allocations.getD column #[])
    let rightInitialized :=
      other.insert column (other.getD column #[])
    have hinitializedAgree :
        CircuitAllocations.AgreesOn leftInitialized rightInitialized
          (column :: rest) := by
      apply CircuitAllocations.AgreesOn.insert hagree
      exact hcolumn
    have hinitializedValidLeft : CircuitAllocations.Valid leftInitialized :=
      CircuitAllocations.Valid.insertSame hvalidLeft column
    have hinitializedValidRight : CircuitAllocations.Valid rightInitialized :=
      CircuitAllocations.Valid.insertSame hvalidRight column
    have hresult := inductionHypothesis rightInitialized
      hinitializedValidLeft hinitializedValidRight hrestNodup
      hcolumnRest hlength hinitializedAgree
    simpa only [firstFit, leftInitialized, rightInitialized,
      hcolumn] using hresult
  case case4 =>
    intro fuel allocations column rest other _ _ _ _ _ hagree
    simp only [trySpaces]
    exact ⟨True.intro, hagree⟩
  case case5 =>
    intro fuel allocations column rest spaceStart spaceEnd more hok
      leftRecursive row hleftRecursive firstInduction
      other hvalidLeft hvalidRight hrestNodup hcolumnRest hlength hagree
    have hrestAgree := CircuitAllocations.AgreesOn.mono hagree (by
      intro candidate hcandidate
      exact List.mem_cons_of_mem column hcandidate)
    have hfirst := firstInduction other hvalidLeft hvalidRight
      hrestNodup hlength hrestAgree
    simp only [trySpaces, hok, if_true, hleftRecursive] at hfirst ⊢
    generalize hrightRecursive :
      firstFit fuel other rest length spaceStart
        ((spaceEnd.map fun endRow =>
          (endRow : ℤ) - spaceStart - length).map Int.toNat) = rightResult
    rcases rightResult with ⟨rightRow, rightRecursive⟩
    rw [hrightRecursive] at hfirst
    dsimp only at hfirst
    have hrow : rightRow = some row := hfirst.1.symm
    rw [hrow]
    constructor
    · rfl
    · have hrecursiveAgree :
          leftRecursive.AgreesOn rightRecursive (column :: rest) := by
        intro candidate hcandidate
        simp only [List.mem_cons] at hcandidate
        rcases hcandidate with rfl | hcandidate
        · have hleftLaw := firstFit_law fuel allocations rest length
            spaceStart
            ((spaceEnd.map fun endRow =>
              (endRow : ℤ) - spaceStart - length).map Int.toNat)
            hvalidLeft hrestNodup hlength
          have hrightLaw := firstFit_law fuel other rest length
            spaceStart
            ((spaceEnd.map fun endRow =>
              (endRow : ℤ) - spaceStart - length).map Int.toNat)
            hvalidRight hrestNodup hlength
          rw [hleftRecursive] at hleftLaw
          rw [hrightRecursive, hrow] at hrightLaw
          have hleftColumn :
              leftRecursive.getD candidate #[] =
                allocations.getD candidate #[] :=
            hleftLaw.1.sameOutside candidate hcolumnRest
          have hrightColumn :
              rightRecursive.getD candidate #[] = other.getD candidate #[] :=
            hrightLaw.1.sameOutside candidate hcolumnRest
          rw [hleftColumn, hrightColumn]
          exact hagree candidate (by simp)
        · exact hfirst.2 candidate hcandidate
      apply CircuitAllocations.AgreesOn.insert hrecursiveAgree
      exact congrArg (fun values => values.insert row length)
        (hrecursiveAgree column (by simp))
  case case6 =>
    intro fuel allocations column rest spaceStart spaceEnd more hok
      leftRecursive hleftRecursive firstInduction spacesInduction
      other hvalidLeft hvalidRight hrestNodup hcolumnRest hlength hagree
    have hrestAgree := CircuitAllocations.AgreesOn.mono hagree (by
      intro candidate hcandidate
      exact List.mem_cons_of_mem column hcandidate)
    have hfirst := firstInduction other hvalidLeft hvalidRight
      hrestNodup hlength hrestAgree
    generalize hrightRecursive :
      firstFit fuel other rest length spaceStart
        ((spaceEnd.map fun endRow =>
          (endRow : ℤ) - spaceStart - length).map Int.toNat) = rightResult
    rcases rightResult with ⟨rightRow, rightRecursive⟩
    rw [hleftRecursive, hrightRecursive] at hfirst
    dsimp only at hfirst
    have hrightRow : rightRow = none := hfirst.1.symm
    have hleftLaw := firstFit_law fuel allocations rest length
      spaceStart
      ((spaceEnd.map fun endRow =>
        (endRow : ℤ) - spaceStart - length).map Int.toNat)
      hvalidLeft hrestNodup hlength
    have hrightLaw := firstFit_law fuel other rest length
      spaceStart
      ((spaceEnd.map fun endRow =>
        (endRow : ℤ) - spaceStart - length).map Int.toNat)
      hvalidRight hrestNodup hlength
    rw [hleftRecursive] at hleftLaw
    rw [hrightRecursive, hrightRow] at hrightLaw
    have hrecursiveAgree :
        leftRecursive.AgreesOn rightRecursive (column :: rest) := by
      intro candidate hcandidate
      simp only [List.mem_cons] at hcandidate
      rcases hcandidate with rfl | hcandidate
      · have hleftColumn :
            leftRecursive.getD candidate #[] =
              allocations.getD candidate #[] :=
          hleftLaw.1.sameOutside candidate hcolumnRest
        have hrightColumn :
            rightRecursive.getD candidate #[] = other.getD candidate #[] :=
          hrightLaw.1.sameOutside candidate hcolumnRest
        rw [hleftColumn, hrightColumn]
        exact hagree candidate (by simp)
      · exact hfirst.2 candidate hcandidate
    have hremaining := spacesInduction rightRecursive
      hleftLaw.1.valid hrightLaw.1.valid hrestNodup hcolumnRest
      hlength hrecursiveAgree
    simpa only [trySpaces, hok, if_true, hleftRecursive,
      hrightRecursive, hrightRow] using hremaining
  case case7 =>
    intro fuel allocations column rest spaceStart spaceEnd more hok
      inductionHypothesis other hvalidLeft hvalidRight hrestNodup
      hcolumnRest hlength hagree
    have hresult := inductionHypothesis other hvalidLeft hvalidRight
      hrestNodup hcolumnRest hlength hagree
    simpa only [trySpaces, hok] using hresult

/-- Extensionally equal allocation maps remain equal after the same first-fit
placement, and produce the same start row. -/
theorem firstFit_equivalent
    (fuel : ℕ) (left right : CircuitAllocations)
    (columns : List RegionColumn) (length start : ℕ)
    (slack : Option ℕ)
    (hvalidLeft : left.Valid) (hvalidRight : right.Valid)
    (hnodup : columns.Nodup) (hlength : 0 < length)
    (hequivalent : left.Equivalent right) :
    let leftResult := firstFit fuel left columns length start slack
    let rightResult := firstFit fuel right columns length start slack
    leftResult.1 = rightResult.1 ∧
      leftResult.2.Equivalent rightResult.2 := by
  have hlocal := firstFit_congruent fuel left columns length start slack
    right hvalidLeft hvalidRight hnodup hlength
      (hequivalent.agreesOn columns)
  have hleftLaw := firstFit_law fuel left columns length start slack
    hvalidLeft hnodup hlength
  have hrightLaw := firstFit_law fuel right columns length start slack
    hvalidRight hnodup hlength
  constructor
  · exact hlocal.1
  · intro column
    by_cases hcolumn : column ∈ columns
    · exact hlocal.2 column hcolumn
    · rw [hleftLaw.1.sameOutside column hcolumn,
          hrightLaw.1.sameOutside column hcolumn]
      exact hequivalent column

private theorem trySpaces_success_of_final_unbounded
    (initialSpaces : List (ℕ × Option ℕ))
    (fuel : ℕ) (allocations : CircuitAllocations)
    (column : RegionColumn) (rest : List RegionColumn)
    (length finalStart : ℕ)
    (hvalid : allocations.Valid)
    (hnodup : rest.Nodup) (hlength : 0 < length)
    (hrecursiveSuccess :
      ∀ current, current.Valid →
        ∃ row updated,
          firstFit fuel current rest length finalStart none =
            (some row, updated)) :
    ∃ row updated,
      trySpaces fuel allocations column rest length
        (initialSpaces ++ [(finalStart, none)]) = (some row, updated) := by
  induction initialSpaces generalizing allocations with
  | nil =>
      obtain ⟨row, updated, hresult⟩ :=
        hrecursiveSuccess allocations hvalid
      exact ⟨row,
        updated.insert column
          ((updated.getD column #[]).insert row length), by
          simp [trySpaces, hresult]⟩
  | cons space more inductionHypothesis =>
      rcases space with ⟨spaceStart, spaceEnd⟩
      cases spaceEnd with
      | none =>
        cases hresult : firstFit fuel allocations rest length spaceStart
            none with
        | mk rowOption updated =>
          cases rowOption with
          | some row =>
              exact ⟨row,
                updated.insert column
                  ((updated.getD column #[]).insert row length), by
                    simp [trySpaces, hresult]⟩
          | none =>
              have hfirstLaw := firstFit_law fuel allocations rest
                length spaceStart none hvalid hnodup hlength
              rw [hresult] at hfirstLaw
              obtain ⟨row, final, hfinal⟩ :=
                inductionHypothesis updated hfirstLaw.1.valid
              exact ⟨row, final, by simp [trySpaces, hresult, hfinal]⟩
      | some spaceEnd =>
          by_cases hfits :
              (0 : ℤ) ≤ (spaceEnd : ℤ) - spaceStart - length
          · have hcondition :
                (length : ℤ) ≤ (spaceEnd : ℤ) - spaceStart := by
              omega
            cases hresult : firstFit fuel allocations rest length spaceStart
                (some (spaceEnd - spaceStart - length)) with
            | mk rowOption updated =>
              cases rowOption with
              | some row =>
                  exact ⟨row,
                    updated.insert column
                      ((updated.getD column #[]).insert row length), by
                        simp [trySpaces, hcondition, hresult]⟩
              | none =>
                  have hfirstLaw := firstFit_law fuel allocations rest
                    length spaceStart
                    (some (spaceEnd - spaceStart - length))
                    hvalid hnodup hlength
                  rw [hresult] at hfirstLaw
                  obtain ⟨row, final, hfinal⟩ :=
                    inductionHypothesis updated hfirstLaw.1.valid
                  exact ⟨row, final, by
                    simp [trySpaces, hcondition, hresult, hfinal]⟩
          · obtain ⟨row, updated, hresult⟩ :=
              inductionHypothesis allocations hvalid
            exact ⟨row, updated, by
              have hcondition :
                  ¬(length : ℤ) ≤ (spaceEnd : ℤ) - spaceStart := by
                omega
              simp [trySpaces, hcondition, hresult]⟩

/-- With unbounded outer slack, sufficient fuel always yields a placement. -/
theorem firstFit_success_unbounded
    (columns : List RegionColumn) (allocations : CircuitAllocations)
    (length start : ℕ)
    (hvalid : allocations.Valid) (hnodup : columns.Nodup)
    (hlength : 0 < length) :
    ∃ row updated,
      firstFit columns.length allocations columns length start none =
        (some row, updated) := by
  induction columns generalizing allocations start with
  | nil => exact ⟨start, allocations, by simp [firstFit]⟩
  | cons column rest inductionHypothesis =>
      have hrestNodup := List.nodup_cons.mp hnodup |>.2
      let initialized :=
        allocations.insert column (allocations.getD column #[])
      let scanResult := Allocations.scanFreeIntervals none
        (allocations.getD column #[]).toList start
      have hinitializedValid : CircuitAllocations.Valid initialized :=
        CircuitAllocations.Valid.insertSame hvalid column
      have hrecursiveSuccess :
          ∀ current, current.Valid →
            ∃ row updated,
              firstFit rest.length current rest length
                scanResult.2 none =
                (some row, updated) := by
        intro current hcurrent
        exact inductionHypothesis current _ hcurrent hrestNodup
      obtain ⟨row, updated, hresult⟩ :=
        trySpaces_success_of_final_unbounded scanResult.1
          rest.length initialized column rest length scanResult.2
          hinitializedValid hrestNodup hlength hrecursiveSuccess
      exact ⟨row, updated, by
        simpa [firstFit, initialized, Allocations.freeIntervals] using hresult⟩

/-- `slot_in` (`strategy.rs:165-195`): place each shape (in the given order) at the earliest
free common row via `first_fit_region`, threading the allocations. Returns the
`(regionIndex, start)` pairs in the input order plus the final allocations. -/
def slotInFrom (shapes : List RegionShape)
    (colAllocs : CircuitAllocations) :
    List (ℕ × ℕ) × CircuitAllocations :=
  match shapes with
  | [] => ([], colAllocs)
  | shape :: rest =>
    let cols := sortRegionColumns shape.columns
    let (row?, colAllocs') := firstFit cols.length colAllocs cols shape.rowCount 0 none
    let (pairs, finalAllocations) := slotInFrom rest colAllocs'
    ((shape.index, row?.getD 0) :: pairs, finalAllocations)

/-- `slot_in` (`strategy.rs:165-195`) from an initially empty allocation map. -/
def slotIn (shapes : List RegionShape) :
    List (ℕ × ℕ) × CircuitAllocations :=
  slotInFrom shapes ∅

/-- Slotting preserves the input region-index sequence in its result pairs. -/
theorem slotInFrom_indices (shapes : List RegionShape)
    (allocations : CircuitAllocations) :
    (slotInFrom shapes allocations).1.map (·.1) =
      shapes.map RegionShape.index := by
  induction shapes generalizing allocations with
  | nil => rfl
  | cons shape rest inductionHypothesis =>
      simp only [slotInFrom, List.map_cons]
      rw [inductionHypothesis]

/-- Slotting from an empty allocation map preserves region indices. -/
theorem slotIn_indices (shapes : List RegionShape) :
    (slotIn shapes).1.map (·.1) = shapes.map RegionShape.index := by
  exact slotInFrom_indices shapes ∅

/-- Slot two shape blocks without flattening their compositional boundary. -/
theorem slotInFrom_append (left right : List RegionShape)
    (allocations : CircuitAllocations) :
    slotInFrom (left ++ right) allocations =
      let leftResult := slotInFrom left allocations
      let rightResult := slotInFrom right leftResult.2
      (leftResult.1 ++ rightResult.1, rightResult.2) := by
  induction left generalizing allocations with
  | nil => rfl
  | cons shape rest inductionHypothesis =>
      simp only [List.cons_append, slotInFrom]
      rw [inductionHypothesis]

/-- Repeatedly slot one already-reduced block, retaining the repetition count rather
than requiring callers to expand a `List.replicate`. -/
def slotInRepeated (count : ℕ) (shapes : List RegionShape)
    (allocations : CircuitAllocations) :
    List (ℕ × ℕ) × CircuitAllocations :=
  match count with
  | 0 => ([], allocations)
  | count + 1 =>
      let first := slotInFrom shapes allocations
      let rest := slotInRepeated count shapes first.2
      (first.1 ++ rest.1, rest.2)

/-- Slotting a replicated reduced block is exactly `slotInRepeated`; the proof keeps
`List.replicate` intact and inducts only over its compact repetition count. -/
theorem slotInFrom_flatten_replicate
    (count : ℕ) (shapes : List RegionShape)
    (allocations : CircuitAllocations) :
    slotInFrom (List.replicate count shapes).flatten allocations =
      slotInRepeated count shapes allocations := by
  induction count generalizing allocations with
  | zero => rfl
  | succ count inductionHypothesis =>
      rw [List.replicate_succ, List.flatten_cons, slotInFrom_append]
      simp only [slotInRepeated]
      rw [inductionHypothesis]

/-- Place one index-free reduced region summary. -/
def placeSummary (summary : RegionShapeSummary)
    (allocations : CircuitAllocations) :
    Option ℕ × CircuitAllocations :=
  let columns := sortRegionColumns summary.columns
  firstFit columns.length allocations columns summary.rowCount 0 none

/-- A declaratively least fitting row determines the exact row selected when a
reduced summary is placed. -/
theorem placeSummary_row_eq_of_leastFit
    (summary : RegionShapeSummary) (allocations : CircuitAllocations)
    (row : ℕ) (hvalid : allocations.Valid)
    (hnodup : summary.columns.Nodup) (hlength : 0 < summary.rowCount)
    (hleast : LeastFit allocations (sortRegionColumns summary.columns)
      summary.rowCount row) :
    (placeSummary summary allocations).1 = some row := by
  obtain ⟨updated, hresult⟩ := firstFit_eq_of_leastFit
    (sortRegionColumns summary.columns).length allocations
    (sortRegionColumns summary.columns) summary.rowCount 0 row none
    hvalid ((sortRegionColumns_perm summary.columns).nodup_iff.mpr hnodup)
    hlength le_rfl (Nat.zero_le row) (by simp) hleast
  simp only [placeSummary, hresult]

/-- Two reduced summaries are placement-equivalent when the floor planner sees
the same sorted column footprint and height. This deliberately ignores the stored
order of the column set. -/
def RegionShapeSummary.PlacementEquivalent
    (left right : RegionShapeSummary) : Prop :=
  sortRegionColumns left.columns = sortRegionColumns right.columns ∧
    left.rowCount = right.rowCount

/-- Canonical representative of a reduced physical shape, quotienting the
incidental first-seen order of its columns. -/
def RegionShapeSummary.normalized
    (summary : RegionShapeSummary) : RegionShapeSummary :=
  { summary with columns := sortRegionColumns summary.columns }

theorem RegionShapeSummary.placementEquivalent_iff_normalized_eq
    {left right : RegionShapeSummary} :
    left.PlacementEquivalent right ↔ left.normalized = right.normalized := by
  simp only [PlacementEquivalent, normalized]
  constructor
  · rintro ⟨hcolumns, hrows⟩
    cases left
    cases right
    simp_all
  · intro heq
    injection heq with hcolumns hrows
    exact ⟨hcolumns, hrows⟩

theorem RegionShapeSummary.normalized_key_eq
    (summary : RegionShapeSummary) :
    summary.normalized.key = summary.key := by
  unfold normalized RegionShapeSummary.key RegionShapeSummary.adviceCols
  have hlength := ((sortRegionColumns_perm summary.columns).filter
    RegionColumn.isAdvice).length_eq
  exact congrArg (fun count => count * summary.rowCount) hlength

theorem RegionShapeSummary.PlacementEquivalent.symm
    {left right : RegionShapeSummary}
    (hequivalent : left.PlacementEquivalent right) :
    right.PlacementEquivalent left :=
  ⟨hequivalent.1.symm, hequivalent.2.symm⟩

theorem placeSummary_eq_of_placementEquivalent
    {left right : RegionShapeSummary}
    (hequivalent : left.PlacementEquivalent right)
    (allocations : CircuitAllocations) :
    placeSummary left allocations = placeSummary right allocations := by
  simp only [placeSummary]
  rw [hequivalent.1, hequivalent.2]

/-- The generic first-fit law, specialized to one reduced region summary. -/
theorem placeSummary_law
    (summary : RegionShapeSummary) (allocations : CircuitAllocations)
    (hvalid : allocations.Valid) (hnodup : summary.columns.Nodup)
    (hlength : 0 < summary.rowCount) :
    PlacementLaw allocations (sortRegionColumns summary.columns)
      summary.rowCount (placeSummary summary allocations) ∧
      ∀ row, (placeSummary summary allocations).1 = some row →
        Within 0 none summary.rowCount row := by
  exact firstFit_law (sortRegionColumns summary.columns).length allocations
    (sortRegionColumns summary.columns) summary.rowCount 0 none hvalid
    ((sortRegionColumns_perm summary.columns).nodup_iff.mpr hnodup)
    hlength

/-- Placing a well-formed reduced summary preserves allocation validity, including
the empty-column case where first-fit is a no-op. -/
theorem placeSummary_valid
    (summary : RegionShapeSummary) (allocations : CircuitAllocations)
    (hvalid : allocations.Valid) (hwellFormed : summary.WellFormed) :
    (placeSummary summary allocations).2.Valid := by
  by_cases hcolumns : summary.columns = []
  · simp [placeSummary, hcolumns, sortRegionColumns, firstFit]
    exact hvalid
  · exact (placeSummary_law summary allocations hvalid hwellFormed.1
      (hwellFormed.2 hcolumns)).1.valid

/-- Index-free slotting of the reduced region summaries. This is the exact V1
allocator with only the bookkeeping region index removed. -/
def slotShapeSummariesFrom (summaries : List RegionShapeSummary)
    (allocations : CircuitAllocations) :
    List ℕ × CircuitAllocations :=
  match summaries with
  | [] => ([], allocations)
  | summary :: rest =>
      let (row?, updated) := placeSummary summary allocations
      let (starts, finalAllocations) :=
        slotShapeSummariesFrom rest updated
      (row?.getD 0 :: starts, finalAllocations)

/-- Forgetting all region indices before slotting preserves starts and allocation
state. -/
theorem slotInFrom_forgetIndices
    (shapes : List RegionShape) (allocations : CircuitAllocations) :
    ((slotInFrom shapes allocations).1.map (·.2),
      (slotInFrom shapes allocations).2) =
      slotShapeSummariesFrom (shapes.map RegionShape.toSummary) allocations := by
  induction shapes generalizing allocations with
  | nil => rfl
  | cons shape rest inductionHypothesis =>
      let columns := sortRegionColumns shape.columns
      generalize hfirst : firstFit columns.length allocations columns
        shape.rowCount 0 none = first
      rcases first with ⟨row?, updated⟩
      simp only [slotInFrom, slotShapeSummariesFrom, List.map_cons,
        RegionShape.toSummary, placeSummary, columns, hfirst]
      have ih := inductionHypothesis updated
      have ihStarts :
          (slotInFrom rest updated).1.map (·.2) =
            (slotShapeSummariesFrom
              (rest.map RegionShape.toSummary) updated).1 := by
        simpa using congrArg Prod.fst ih
      have ihAllocations :
          (slotInFrom rest updated).2 =
            (slotShapeSummariesFrom
              (rest.map RegionShape.toSummary) updated).2 := by
        simpa using congrArg Prod.snd ih
      rw [ihStarts, ihAllocations]

/-- Removing region indices before slotting changes only the index component of
the returned pairs, never starts or allocation state. -/
theorem slotInFrom_indexRegionSummaries
    (initial : ℕ) (summaries : List RegionShapeSummary)
    (allocations : CircuitAllocations) :
    ((slotInFrom (indexRegionSummaries initial summaries) allocations).1.map
        (·.2),
      (slotInFrom (indexRegionSummaries initial summaries) allocations).2) =
      slotShapeSummariesFrom summaries allocations := by
  induction summaries generalizing initial allocations with
  | nil => rfl
  | cons summary rest inductionHypothesis =>
      let columns := sortRegionColumns summary.columns
      generalize hfirst : firstFit columns.length allocations columns
        summary.rowCount 0 none = first
      rcases first with ⟨row?, updated⟩
      simp only [indexRegionSummaries, slotInFrom, measureRegionSummary,
        List.map_cons, columns, hfirst, slotShapeSummariesFrom,
        placeSummary]
      have ih := inductionHypothesis (initial + 1) updated
      have ihStarts :
          (slotInFrom (indexRegionSummaries (initial + 1) rest)
            updated).1.map (·.2) =
            (slotShapeSummariesFrom rest updated).1 := by
        simpa using congrArg Prod.fst ih
      have ihAllocations :
          (slotInFrom (indexRegionSummaries (initial + 1) rest)
            updated).2 =
            (slotShapeSummariesFrom rest updated).2 := by
        simpa using congrArg Prod.snd ih
      rw [ihStarts, ihAllocations]

/-- Index-free slotting composes over summary concatenation. -/
theorem slotShapeSummariesFrom_append
    (left right : List RegionShapeSummary)
    (allocations : CircuitAllocations) :
    slotShapeSummariesFrom (left ++ right) allocations =
      let leftResult := slotShapeSummariesFrom left allocations
      let rightResult := slotShapeSummariesFrom right leftResult.2
      (leftResult.1 ++ rightResult.1, rightResult.2) := by
  induction left generalizing allocations with
  | nil => rfl
  | cons summary rest inductionHypothesis =>
      generalize hfirst : placeSummary summary allocations = first
      rcases first with ⟨row?, updated⟩
      simp only [List.cons_append, slotShapeSummariesFrom, hfirst]
      rw [inductionHypothesis]

/-- Replacing every reduced region shape by a placement-equivalent shape preserves
the complete index-free planner result. This is the compositional boundary used by
concrete circuits to publish canonical physical summaries without preserving the
incidental first-seen order of their column sets. -/
theorem slotShapeSummariesFrom_eq_of_forall₂_placementEquivalent
    {left right : List RegionShapeSummary}
    (hequivalent : List.Forall₂ RegionShapeSummary.PlacementEquivalent
      left right)
    (allocations : CircuitAllocations) :
    slotShapeSummariesFrom left allocations =
      slotShapeSummariesFrom right allocations := by
  induction hequivalent generalizing allocations with
  | nil => rfl
  | cons hhead _ inductionHypothesis =>
      simp only [slotShapeSummariesFrom]
      rw [placeSummary_eq_of_placementEquivalent hhead,
        inductionHypothesis]

/-- Repeated index-free slotting of one already-reduced summary block. -/
def slotShapeSummariesRepeated (count : ℕ)
    (summaries : List RegionShapeSummary)
    (allocations : CircuitAllocations) :
    List ℕ × CircuitAllocations :=
  match count with
  | 0 => ([], allocations)
  | count + 1 =>
      let first := slotShapeSummariesFrom summaries allocations
      let rest := slotShapeSummariesRepeated count summaries first.2
      (first.1 ++ rest.1, rest.2)

/-- Evaluate a compact `List.replicate` summary by induction over its count. -/
theorem slotShapeSummariesFrom_flatten_replicate
    (count : ℕ) (summaries : List RegionShapeSummary)
    (allocations : CircuitAllocations) :
    slotShapeSummariesFrom
        (List.replicate count summaries).flatten allocations =
      slotShapeSummariesRepeated count summaries allocations := by
  induction count generalizing allocations with
  | zero => rfl
  | succ count inductionHypothesis =>
      rw [List.replicate_succ, List.flatten_cons,
        slotShapeSummariesFrom_append]
      simp only [slotShapeSummariesRepeated]
      rw [inductionHypothesis]

/-- Extensionally equal allocation states produce the same starts and remain
extensionally equal after slotting any well-formed summary sequence. -/
theorem slotShapeSummariesFrom_equivalent
    (summaries : List RegionShapeSummary)
    (left right : CircuitAllocations)
    (hwellFormed : summaries.Forall RegionShapeSummary.WellFormed)
    (hvalidLeft : left.Valid) (hvalidRight : right.Valid)
    (hequivalent : left.Equivalent right) :
    let leftResult := slotShapeSummariesFrom summaries left
    let rightResult := slotShapeSummariesFrom summaries right
    leftResult.1 = rightResult.1 ∧
      leftResult.2.Equivalent rightResult.2 := by
  induction summaries generalizing left right with
  | nil => exact ⟨rfl, hequivalent⟩
  | cons summary rest inductionHypothesis =>
      rw [List.forall_cons] at hwellFormed
      have hhead := hwellFormed.1
      have htail := hwellFormed.2
      let columns := sortRegionColumns summary.columns
      have hcolumnsNodup : columns.Nodup :=
        (sortRegionColumns_perm summary.columns).nodup_iff.mpr hhead.1
      by_cases hcolumns : summary.columns = []
      · have hsorted : columns = [] := by
          simp [columns, hcolumns, sortRegionColumns]
        simp only [slotShapeSummariesFrom, placeSummary, columns,
          hsorted, firstFit]
        have hrest := inductionHypothesis left right htail hvalidLeft
          hvalidRight hequivalent
        exact ⟨congrArg (List.cons 0) hrest.1, hrest.2⟩
      · have hlength : 0 < summary.rowCount := hhead.2 hcolumns
        have hfirst := firstFit_equivalent columns.length left right
          columns summary.rowCount 0 none hvalidLeft hvalidRight
          hcolumnsNodup hlength hequivalent
        have hleftLaw := firstFit_law columns.length left columns
          summary.rowCount 0 none hvalidLeft hcolumnsNodup hlength
        have hrightLaw := firstFit_law columns.length right columns
          summary.rowCount 0 none hvalidRight hcolumnsNodup hlength
        generalize hleft :
          firstFit columns.length left columns summary.rowCount 0 none =
            leftFirst at hfirst hleftLaw ⊢
        generalize hright :
          firstFit columns.length right columns summary.rowCount 0 none =
            rightFirst at hfirst hrightLaw ⊢
        rcases leftFirst with ⟨leftRow, leftUpdated⟩
        rcases rightFirst with ⟨rightRow, rightUpdated⟩
        dsimp only at hfirst
        have hrest := inductionHypothesis leftUpdated rightUpdated htail
          hleftLaw.1.valid hrightLaw.1.valid hfirst.2
        simp only [slotShapeSummariesFrom, placeSummary, columns,
          hleft, hright]
        rw [hfirst.1]
        exact
          ⟨congrArg (List.cons (rightRow.getD 0)) hrest.1, hrest.2⟩

/-- Placing regions with disjoint column footprints commutes: each receives the
same row, and both orders leave the same observable allocation state. -/
theorem placeSummary_commute
    (left right : RegionShapeSummary)
    (allocations : CircuitAllocations)
    (hvalid : allocations.Valid)
    (hleftNodup : left.columns.Nodup)
    (hrightNodup : right.columns.Nodup)
    (hleftLength : 0 < left.rowCount)
    (hrightLength : 0 < right.rowCount)
    (hdisjoint : List.Disjoint left.columns right.columns) :
    let leftFirst := placeSummary left allocations
    let leftThenRight := placeSummary right leftFirst.2
    let rightFirst := placeSummary right allocations
    let rightThenLeft := placeSummary left rightFirst.2
    leftFirst.1 = rightThenLeft.1 ∧
      rightFirst.1 = leftThenRight.1 ∧
      leftThenRight.2.Equivalent rightThenLeft.2 := by
  let leftColumns := sortRegionColumns left.columns
  let rightColumns := sortRegionColumns right.columns
  have hleftColumnsNodup : leftColumns.Nodup :=
    (sortRegionColumns_perm left.columns).nodup_iff.mpr hleftNodup
  have hrightColumnsNodup : rightColumns.Nodup :=
    (sortRegionColumns_perm right.columns).nodup_iff.mpr hrightNodup
  have hsortedDisjoint : List.Disjoint leftColumns rightColumns := by
    intro column hleftColumn hrightColumn
    exact hdisjoint
      ((sortRegionColumns_perm left.columns).mem_iff.mp hleftColumn)
      ((sortRegionColumns_perm right.columns).mem_iff.mp hrightColumn)
  simp only [placeSummary]
  generalize hleftFirst :
    firstFit leftColumns.length allocations leftColumns
      left.rowCount 0 none = leftFirst
  rcases leftFirst with ⟨leftRow, leftAllocations⟩
  generalize hrightFirst :
    firstFit rightColumns.length allocations rightColumns
      right.rowCount 0 none = rightFirst
  rcases rightFirst with ⟨rightRow, rightAllocations⟩
  generalize hleftThenRight :
    firstFit rightColumns.length leftAllocations rightColumns
      right.rowCount 0 none = leftThenRight
  rcases leftThenRight with
    ⟨rightRowAfterLeft, leftThenRightAllocations⟩
  generalize hrightThenLeft :
    firstFit leftColumns.length rightAllocations leftColumns
      left.rowCount 0 none = rightThenLeft
  rcases rightThenLeft with
    ⟨leftRowAfterRight, rightThenLeftAllocations⟩
  have hleftLaw := firstFit_law leftColumns.length allocations
    leftColumns left.rowCount 0 none hvalid hleftColumnsNodup hleftLength
  have hrightLaw := firstFit_law rightColumns.length allocations
    rightColumns right.rowCount 0 none hvalid hrightColumnsNodup
      hrightLength
  rw [hleftFirst] at hleftLaw
  rw [hrightFirst] at hrightLaw
  have hrightAgreement :
      allocations.AgreesOn leftAllocations rightColumns := by
    intro column hcolumn
    symm
    exact hleftLaw.1.sameOutside column (by
      intro hleftColumn
      exact hsortedDisjoint hleftColumn hcolumn)
  have hleftAgreement :
      allocations.AgreesOn rightAllocations leftColumns := by
    intro column hcolumn
    symm
    exact hrightLaw.1.sameOutside column (by
      intro hrightColumn
      exact hsortedDisjoint hcolumn hrightColumn)
  have hrightCongruent := firstFit_congruent rightColumns.length
    allocations rightColumns right.rowCount 0 none leftAllocations
    hvalid hleftLaw.1.valid hrightColumnsNodup hrightLength
    hrightAgreement
  have hleftCongruent := firstFit_congruent leftColumns.length
    allocations leftColumns left.rowCount 0 none rightAllocations
    hvalid hrightLaw.1.valid hleftColumnsNodup hleftLength hleftAgreement
  rw [hrightFirst, hleftThenRight] at hrightCongruent
  rw [hleftFirst, hrightThenLeft] at hleftCongruent
  have hleftThenRightLaw := firstFit_law rightColumns.length
    leftAllocations rightColumns right.rowCount 0 none
    hleftLaw.1.valid hrightColumnsNodup hrightLength
  have hrightThenLeftLaw := firstFit_law leftColumns.length
    rightAllocations leftColumns left.rowCount 0 none
    hrightLaw.1.valid hleftColumnsNodup hleftLength
  rw [hleftThenRight] at hleftThenRightLaw
  rw [hrightThenLeft] at hrightThenLeftLaw
  dsimp only at hrightCongruent hleftCongruent ⊢
  constructor
  · exact hleftCongruent.1
  constructor
  · exact hrightCongruent.1
  · intro column
    by_cases hleftColumn : column ∈ leftColumns
    · rw [hleftThenRightLaw.1.sameOutside column (by
            intro hrightColumn
            exact hsortedDisjoint hleftColumn hrightColumn)]
      exact hleftCongruent.2 column hleftColumn
    · by_cases hrightColumn : column ∈ rightColumns
      · rw [← hrightCongruent.2 column hrightColumn,
            hrightThenLeftLaw.1.sameOutside column hleftColumn]
      · rw [hleftThenRightLaw.1.sameOutside column hrightColumn,
            hleftLaw.1.sameOutside column hleftColumn,
            hrightThenLeftLaw.1.sameOutside column hleftColumn,
            hrightLaw.1.sameOutside column hrightColumn]

/-- Pair shapes with the starts returned in the same slotting order. -/
def placedShapes (shapes : List RegionShape)
    (pairs : List (ℕ × ℕ)) : List (RegionShape × ℕ) :=
  shapes.zip (pairs.map (·.2))

private def PlacedRecords (allocations : CircuitAllocations)
    (placed : List (RegionShape × ℕ)) : Prop :=
  ∀ item ∈ placed, ∀ column ∈ item.1.columns,
    (item.2, item.1.rowCount) ∈
      (allocations.getD column #[]).toList

private def PlacedFits (allocations : CircuitAllocations)
    (placed : List (RegionShape × ℕ)) : Prop :=
  ∀ item ∈ placed, ∀ column ∈ item.1.columns,
    (allocations.getD column #[]).Fits item.2 item.1.rowCount

/-- Pairwise row disjointness for shapes that share a planner column. -/
def PlacedDisjoint (placed : List (RegionShape × ℕ)) : Prop :=
  placed.Pairwise fun left right =>
    ∀ column, column ∈ left.1.columns → column ∈ right.1.columns →
      RowIntervalsDisjoint
        left.2 left.1.rowCount right.2 right.1.rowCount

/-- The compositional correctness interface of `slotInFrom`. -/
structure SlotInLaw
    (before : CircuitAllocations) (shapes : List RegionShape)
    (result : List (ℕ × ℕ) × CircuitAllocations) : Prop where
  valid : result.2.Valid
  preserves : before.Extends result.2
  indices : result.1.map (·.1) = shapes.map RegionShape.index
  records : PlacedRecords result.2 (placedShapes shapes result.1)
  fitsBefore : PlacedFits before (placedShapes shapes result.1)
  disjoint : PlacedDisjoint (placedShapes shapes result.1)

/-- Recursive slotting preserves allocation validity and separates shared columns. -/
theorem slotInFrom_law
    (shapes : List RegionShape) (allocations : CircuitAllocations)
    (hvalid : allocations.Valid)
    (hshapes : shapes.Forall RegionShape.WellFormed) :
    SlotInLaw allocations shapes (slotInFrom shapes allocations) := by
  induction shapes generalizing allocations with
  | nil =>
      exact
        { valid := hvalid
          preserves := CircuitAllocations.Extends.refl allocations
          indices := rfl
          records := by simp [PlacedRecords, placedShapes]
          fitsBefore := by simp [PlacedFits, placedShapes]
          disjoint := by simp [PlacedDisjoint, placedShapes] }
  | cons shape rest inductionHypothesis =>
      rw [List.forall_cons] at hshapes
      have hcolumnsNodup : (sortRegionColumns shape.columns).Nodup :=
        (sortRegionColumns_perm shape.columns).nodup_iff.mpr
          hshapes.1.1
      by_cases hcolumns : shape.columns = []
      · have hsorted : sortRegionColumns shape.columns = [] := by
          exact List.eq_nil_iff_forall_not_mem.mpr fun column hcolumn =>
            (by simpa [hcolumns] using
              (sortRegionColumns_perm shape.columns).mem_iff.mp hcolumn)
        have hrecursive := inductionHypothesis allocations hvalid hshapes.2
        simp only [slotInFrom, hsorted, firstFit]
        refine
          { valid := hrecursive.valid
            preserves := hrecursive.preserves
            indices := by simp [hrecursive.indices]
            records := ?_
            fitsBefore := ?_
            disjoint := ?_ }
        · intro item hitem column hcolumn
          simp only [placedShapes, List.map_cons, List.zip_cons_cons,
            List.mem_cons] at hitem
          rcases hitem with rfl | hrest
          · simp [hcolumns] at hcolumn
          · exact hrecursive.records item (by
              simpa [placedShapes] using hrest) column hcolumn
        · intro item hitem column hcolumn
          simp only [placedShapes, List.map_cons, List.zip_cons_cons,
            List.mem_cons] at hitem
          rcases hitem with rfl | hrest
          · simp [hcolumns] at hcolumn
          · exact hrecursive.fitsBefore item (by
              simpa [placedShapes] using hrest) column hcolumn
        · unfold placedShapes PlacedDisjoint
          rw [List.map_cons, List.zip_cons_cons, List.pairwise_cons]
          exact ⟨by
            intro item hitem column hcolumn
            simp [hcolumns] at hcolumn,
            hrecursive.disjoint⟩
      · have hrowCount : 0 < shape.rowCount := hshapes.1.2 hcolumns
        obtain ⟨row, nextAllocations, hplacement⟩ :=
          firstFit_success_unbounded (sortRegionColumns shape.columns)
            allocations shape.rowCount 0 hvalid hcolumnsNodup hrowCount
        have hplacementLaw := firstFit_law
          (sortRegionColumns shape.columns).length allocations
          (sortRegionColumns shape.columns) shape.rowCount 0 none
          hvalid hcolumnsNodup hrowCount
        rw [hplacement] at hplacementLaw
        have hrecursive := inductionHypothesis nextAllocations
          hplacementLaw.1.valid hshapes.2
        simp only [slotInFrom, hplacement]
        refine
          { valid := hrecursive.valid
            preserves := hplacementLaw.1.preserves.trans
              hrecursive.preserves
            indices := by simp [hrecursive.indices]
            records := ?_
            fitsBefore := ?_
            disjoint := ?_ }
        · intro item hitem column hcolumn
          simp only [placedShapes, List.map_cons, List.zip_cons_cons,
            List.mem_cons] at hitem
          rcases hitem with rfl | hrest
          · exact hrecursive.preserves column (row, shape.rowCount)
              (hplacementLaw.1.records row rfl column
                ((sortRegionColumns_perm shape.columns).mem_iff.mpr hcolumn))
          · exact hrecursive.records item (by
              simpa [placedShapes] using hrest) column hcolumn
        · intro item hitem column hcolumn
          simp only [placedShapes, List.map_cons, List.zip_cons_cons,
            List.mem_cons] at hitem
          rcases hitem with rfl | hrest
          · exact hplacementLaw.1.fits row rfl column
              ((sortRegionColumns_perm shape.columns).mem_iff.mpr hcolumn)
          · intro interval hinterval
            exact hrecursive.fitsBefore item (by
                simpa [placedShapes] using hrest) column hcolumn
              interval
              (hplacementLaw.1.preserves column interval hinterval)
        · unfold placedShapes PlacedDisjoint
          rw [List.map_cons, List.zip_cons_cons, List.pairwise_cons]
          constructor
          · intro item hitem column hshapeColumn hitemColumn
            have hitemFit := hrecursive.fitsBefore item (by
              simpa [placedShapes] using hitem) column hitemColumn
            have hshapeRecord := hplacementLaw.1.records row rfl column
              ((sortRegionColumns_perm shape.columns).mem_iff.mpr
                hshapeColumn)
            exact (hitemFit (row, shape.rowCount) hshapeRecord).elim
              Or.inr Or.inl
          · exact hrecursive.disjoint

private theorem placedShapes_exists_of_mem
    (shapes : List RegionShape) (pairs : List (ℕ × ℕ))
    (hindices : pairs.map (·.1) = shapes.map RegionShape.index)
    {shape : RegionShape} (hshape : shape ∈ shapes) :
    ∃ start, (shape, start) ∈ placedShapes shapes pairs := by
  induction shapes generalizing pairs with
  | nil => simp at hshape
  | cons head rest inductionHypothesis =>
      cases pairs with
      | nil => simp at hindices
      | cons pair remaining =>
          simp only [List.map_cons, List.cons.injEq] at hindices
          simp only [List.mem_cons] at hshape
          rcases hshape with rfl | hrest
          · exact ⟨pair.2, by simp [placedShapes]⟩
          · obtain ⟨start, hplaced⟩ :=
              inductionHypothesis remaining hindices.2 hrest
            exact ⟨start, by
              simp only [placedShapes, List.map_cons, List.zip_cons_cons,
                List.mem_cons]
              exact Or.inr hplaced⟩

private theorem pair_mem_of_mem_placedShapes
    (shapes : List RegionShape) (pairs : List (ℕ × ℕ))
    (hindices : pairs.map (·.1) = shapes.map RegionShape.index)
    {shape : RegionShape} {start : ℕ}
    (hplaced : (shape, start) ∈ placedShapes shapes pairs) :
    (shape.index, start) ∈ pairs := by
  induction shapes generalizing pairs with
  | nil => simp [placedShapes] at hplaced
  | cons head rest inductionHypothesis =>
      cases pairs with
      | nil => simp [placedShapes] at hplaced
      | cons pair remaining =>
          simp only [List.map_cons, List.cons.injEq] at hindices
          simp only [placedShapes, List.map_cons, List.zip_cons_cons,
            List.mem_cons] at hplaced
          rcases hplaced with hhead | htail
          · have hshape : shape = head := congrArg Prod.fst hhead
            have hstart : start = pair.2 := congrArg Prod.snd hhead
            subst shape
            subst start
            rw [List.mem_cons]
            apply Or.inl
            exact Prod.ext hindices.1.symm rfl
          · exact List.mem_cons_of_mem _
              (inductionHypothesis remaining hindices.2 htail)

/-- Distinct regions sharing any measured column occupy disjoint row intervals. -/
def SharedColumnIntervalsDisjoint
    (shapes : List RegionShape) (starts : List ℕ) : Prop :=
  ∀ ⦃left right : RegionShape⦄,
    left ∈ shapes →
    right ∈ shapes →
    left.index ≠ right.index →
    ∀ ⦃column : RegionColumn⦄,
      column ∈ left.columns →
      column ∈ right.columns →
      RowIntervalsDisjoint
        (starts.getD left.index 0) left.rowCount
        (starts.getD right.index 0) right.rowCount

/--
The semantic selector-placement invariant: distinct regions that share a virtual
selector column occupy disjoint row intervals.
-/
def SharedSelectorIntervalsDisjoint
    (shapes : List RegionShape) (starts : List ℕ) : Prop :=
  ∀ ⦃left right : RegionShape⦄,
    left ∈ shapes →
    right ∈ shapes →
    left.index ≠ right.index →
    ∀ ⦃selector : ℕ⦄,
      RegionColumn.selector selector ∈ left.columns →
      RegionColumn.selector selector ∈ right.columns →
      RowIntervalsDisjoint
        (starts.getD left.index 0) left.rowCount
        (starts.getD right.index 0) right.rowCount

private theorem rel_or_reverse_of_pairwise_of_mem
    {α : Type} {relation : α → α → Prop}
    {items : List α} (hpairs : items.Pairwise relation)
    {left right : α} (hleft : left ∈ items)
    (hright : right ∈ items) (hne : left ≠ right) :
    relation left right ∨ relation right left := by
  induction items with
  | nil =>
      simp at hleft
  | cons head tail ih =>
      rw [List.pairwise_cons] at hpairs
      simp only [List.mem_cons] at hleft hright
      rcases hleft with rfl | hleft
      · rcases hright with rfl | hright
        · contradiction
        · exact Or.inl (hpairs.1 right hright)
      · rcases hright with rfl | hright
        · exact Or.inr (hpairs.1 left hleft)
        · exact ih hpairs.2 hleft hright

/-- An operation activates selector `selector` at region-local `row`. -/
def activatesSelectorAt (selector row : ℕ) : RegionOperation F → Prop
  | operation => operation.ActivatesSelectorAt selector row

private theorem mem_addCol_self
    (columns : List RegionColumn) (column : RegionColumn) :
    column ∈ addCol columns column := by
  by_cases hcolumn : column ∈ columns <;>
    simp [addCol, addColumn, hcolumn]

private theorem mem_addCol_of_mem
    (columns : List RegionColumn) (added column : RegionColumn)
    (hcolumn : column ∈ columns) :
    column ∈ addCol columns added := by
  by_cases hadded : added ∈ columns <;>
    simp [addCol, addColumn, hadded, hcolumn]

private theorem mem_foldl_addCol_of_initial_mem
    (added : List RegionColumn) (columns : List RegionColumn)
    {column : RegionColumn} (hcolumn : column ∈ columns) :
    column ∈ added.foldl addCol columns := by
  induction added generalizing columns with
  | nil =>
      exact hcolumn
  | cons head tail ih =>
      simp only [List.foldl_cons]
      exact ih _ (mem_addCol_of_mem columns head column hcolumn)

private theorem mem_foldl_addCol_of_mem
    (added : List RegionColumn) (columns : List RegionColumn)
    {column : RegionColumn} (hcolumn : column ∈ added) :
    column ∈ added.foldl addCol columns := by
  induction added generalizing columns with
  | nil =>
      simp at hcolumn
  | cons head tail ih =>
      simp only [List.mem_cons] at hcolumn
      simp only [List.foldl_cons]
      rcases hcolumn with rfl | htail
      · exact mem_foldl_addCol_of_initial_mem tail _
          (mem_addCol_self columns column)
      · exact ih (addCol columns head) htail

private theorem mem_addOperationColumns_of_mem
    (columns : List RegionColumn) (operation : RegionOperation F)
    {column : RegionColumn} (hcolumn : column ∈ columns) :
    column ∈ addOperationColumns columns operation := by
  exact mem_foldl_addCol_of_initial_mem
    (regionOperationShapeColumns operation) columns hcolumn

private theorem mem_foldl_addOperationColumns_of_initial_mem
    (body : RegionOperations F) (columns : List RegionColumn)
    {column : RegionColumn} (hcolumn : column ∈ columns) :
    column ∈ body.foldl addOperationColumns columns := by
  induction body generalizing columns with
  | nil =>
      exact hcolumn
  | cons head tail ih =>
      simp only [List.foldl_cons]
      exact ih _ (mem_addOperationColumns_of_mem columns head hcolumn)

private theorem selector_mem_foldl_addOperationColumns_of_activation
    (body : RegionOperations F) (columns : List RegionColumn)
    {operation : RegionOperation F} (hoperation : operation ∈ body)
    {selector row : ℕ}
    (hactivation : activatesSelectorAt selector row operation) :
    RegionColumn.selector selector ∈
      body.foldl addOperationColumns columns := by
  induction body generalizing columns operation with
  | nil =>
      simp at hoperation
  | cons head tail ih =>
      simp only [List.mem_cons] at hoperation
      simp only [List.foldl_cons]
      rcases hoperation with rfl | htail
      · apply mem_foldl_addOperationColumns_of_initial_mem
        apply mem_foldl_addCol_of_mem
        cases operation with
        | enableGate gate operationRow =>
            rcases hactivation with ⟨rfl, rfl⟩
            simp [regionOperationShapeColumns]
        | enableLookup argument enabled operationRow =>
            rcases hactivation with ⟨⟨selected, hselected, rfl⟩, rfl⟩
            exact List.mem_map.mpr ⟨selected, hselected, rfl⟩
        | assignAdvice | assignFixed | constrainEqual | constrainConstant |
            constrainInstance =>
            contradiction
      · exact ih (addOperationColumns columns head) htail hactivation

/-- Every activated selector is a virtual column measured for its region. -/
theorem selector_mem_measureRegion_of_activatesSelectorAt
    (idx : ℕ) (body : RegionOperations F)
    {operation : RegionOperation F} (hoperation : operation ∈ body)
    {selector row : ℕ}
    (hactivation : activatesSelectorAt selector row operation) :
    RegionColumn.selector selector ∈ (measureRegion idx body).columns := by
  have hcolumn : RegionColumn.selector selector ∈
      (regionSynthesisSummary body).columns := by
    apply mem_regionSynthesisSummary_columns_of_mem body operation hoperation
    cases operation with
    | enableGate gate operationRow =>
        rcases hactivation with ⟨rfl, rfl⟩
        simp [regionOperationShapeColumns]
    | enableLookup argument enabled operationRow =>
        rcases hactivation with ⟨⟨selected, hselected, rfl⟩, rfl⟩
        exact List.mem_map.mpr ⟨selected, hselected, rfl⟩
    | assignAdvice | assignFixed | constrainEqual | constrainConstant |
        constrainInstance => contradiction
  exact hcolumn

/-- Every selector activation row lies in its measured region interval. -/
theorem row_lt_measureRegion_of_activatesSelectorAt
    (idx : ℕ) (body : RegionOperations F)
    {operation : RegionOperation F} (hoperation : operation ∈ body)
    {selector row : ℕ}
    (hactivation : activatesSelectorAt selector row operation) :
    row < (measureRegion idx body).rowCount := by
  cases operation with
  | enableGate gate operationRow =>
      rcases hactivation with ⟨_, rfl⟩
      rw [Nat.lt_iff_add_one_le]
      exact regionOperationRowExtent_le_synthesisSummary_of_mem body
        (.enableGate gate operationRow) hoperation
  | enableLookup argument enabled operationRow =>
      rcases hactivation with ⟨_, rfl⟩
      exact row_lt_measureRegion_of_enableLookup_mem
        idx body argument enabled operationRow hoperation
  | assignAdvice | assignFixed | constrainEqual | constrainConstant |
      constrainInstance =>
      contradiction

/--
Distinct regions whose selector intervals are disjoint cannot activate the same
selector at the same absolute row.
-/
theorem activation_rows_ne_of_sharedSelectorIntervalsDisjoint
    {shapes : List RegionShape} {starts : List ℕ}
    (hplanner : SharedSelectorIntervalsDisjoint shapes starts)
    {leftIndex rightIndex : ℕ}
    {leftBody rightBody : RegionOperations F}
    (hleftShape : measureRegion leftIndex leftBody ∈ shapes)
    (hrightShape : measureRegion rightIndex rightBody ∈ shapes)
    (hindices : leftIndex ≠ rightIndex)
    {leftOperation rightOperation : RegionOperation F}
    (hleftOperation : leftOperation ∈ leftBody)
    (hrightOperation : rightOperation ∈ rightBody)
    {selector leftRow rightRow : ℕ}
    (hleftActivation :
      activatesSelectorAt selector leftRow leftOperation)
    (hrightActivation :
      activatesSelectorAt selector rightRow rightOperation) :
    starts.getD leftIndex 0 + leftRow ≠
      starts.getD rightIndex 0 + rightRow := by
  have hleftColumn :=
    selector_mem_measureRegion_of_activatesSelectorAt
      leftIndex leftBody hleftOperation hleftActivation
  have hrightColumn :=
    selector_mem_measureRegion_of_activatesSelectorAt
      rightIndex rightBody hrightOperation hrightActivation
  have hleftRow :=
    row_lt_measureRegion_of_activatesSelectorAt
      leftIndex leftBody hleftOperation hleftActivation
  have hrightRow :=
    row_lt_measureRegion_of_activatesSelectorAt
      rightIndex rightBody hrightOperation hrightActivation
  have hdisjoint :=
    hplanner hleftShape hrightShape hindices
      hleftColumn hrightColumn
  change
    RowIntervalsDisjoint
      (starts.getD leftIndex 0)
      (measureRegion leftIndex leftBody).rowCount
      (starts.getD rightIndex 0)
      (measureRegion rightIndex rightBody).rowCount at hdisjoint
  intro hequal
  rcases hdisjoint with hleftBefore | hrightBefore
  · have habsLt :
        starts.getD leftIndex 0 + leftRow <
          starts.getD leftIndex 0 +
            (measureRegion leftIndex leftBody).rowCount :=
      Nat.add_lt_add_left hleftRow _
    rw [hequal] at habsLt
    exact (Nat.not_lt_of_ge
      (hleftBefore.trans
        (Nat.le_add_right (starts.getD rightIndex 0) rightRow))) habsLt
  · have habsLt :
        starts.getD rightIndex 0 + rightRow <
          starts.getD rightIndex 0 +
            (measureRegion rightIndex rightBody).rowCount :=
      Nat.add_lt_add_left hrightRow _
    rw [← hequal] at habsLt
    exact (Nat.not_lt_of_ge
      (hrightBefore.trans
        (Nat.le_add_right (starts.getD leftIndex 0) leftRow))) habsLt

/--
Under selector-interval disjointness, an absolute selector activation has a unique
source region index. Multiple source operations within that region remain harmless.
-/
theorem activation_origin_regionIndex_unique
    {regions : List (ℕ × RegionOperations F)} {starts : List ℕ}
    (hplanner :
      SharedSelectorIntervalsDisjoint
        (regions.map fun region =>
          measureRegion region.1 region.2)
        starts)
    {selector absoluteRow : ℕ}
    {leftIndex rightIndex : ℕ}
    {leftBody rightBody : RegionOperations F}
    {leftOperation rightOperation : RegionOperation F}
    {leftRow rightRow : ℕ}
    (hleftRegion : (leftIndex, leftBody) ∈ regions)
    (hrightRegion : (rightIndex, rightBody) ∈ regions)
    (hleftOperation : leftOperation ∈ leftBody)
    (hrightOperation : rightOperation ∈ rightBody)
    (hleftActivation :
      activatesSelectorAt selector leftRow leftOperation)
    (hrightActivation :
      activatesSelectorAt selector rightRow rightOperation)
    (hleftAbsolute :
      absoluteRow = starts.getD leftIndex 0 + leftRow)
    (hrightAbsolute :
      absoluteRow = starts.getD rightIndex 0 + rightRow) :
    leftIndex = rightIndex := by
  by_contra hindices
  apply activation_rows_ne_of_sharedSelectorIntervalsDisjoint
    hplanner
    (List.mem_map.mpr
      ⟨(leftIndex, leftBody), hleftRegion, rfl⟩)
    (List.mem_map.mpr
      ⟨(rightIndex, rightBody), hrightRegion, rfl⟩)
    hindices hleftOperation hrightOperation
    hleftActivation hrightActivation
  rw [← hleftAbsolute, ← hrightAbsolute]

/-! ## Selector-free V1 placement -/

namespace V1

open Halo2 FloorPlanner

theorem selector_mem_selectorColumns_iff
    (selector : ℕ) (columns : List RegionColumn) :
    RegionColumn.selector selector ∈ selectorColumns columns ↔
      RegionColumn.selector selector ∈ columns := by
  simp [selectorColumns]

theorem column_mem_physicalColumns_iff
    (kind : ColumnKind) (index : ℕ) (columns : List RegionColumn) :
    RegionColumn.column kind index ∈ physicalColumns columns ↔
      RegionColumn.column kind index ∈ columns := by
  simp [physicalColumns]

theorem exists_selector_of_mem_selectorColumns
    {column : RegionColumn} {columns : List RegionColumn}
    (hcolumn : column ∈ selectorColumns columns) :
    ∃ selector, column = .selector selector := by
  rw [selectorColumns, List.mem_filter] at hcolumn
  rcases column with ⟨kind, index⟩ | selector
  · simp at hcolumn
  · exact ⟨selector, rfl⟩

theorem exists_column_of_mem_physicalColumns
    {column : RegionColumn} {columns : List RegionColumn}
    (hcolumn : column ∈ physicalColumns columns) :
    ∃ kind index, column = .column kind index := by
  rw [physicalColumns, List.mem_filter] at hcolumn
  rcases column with ⟨kind, index⟩ | selector
  · exact ⟨kind, index, rfl⟩
  · simp at hcolumn

/-- Every interval allocated to `dominated` is also allocated to `dominant`. -/
def ColumnAllocationsDominate (allocations : CircuitAllocations)
    (dominant dominated : RegionColumn) : Prop :=
  ∀ interval,
    interval ∈ (allocations.getD dominated #[]).toList →
      interval ∈ (allocations.getD dominant #[]).toList

theorem ColumnAllocationsDominate.fits
    {allocations : CircuitAllocations} {dominant dominated : RegionColumn}
    (hdominate : ColumnAllocationsDominate allocations dominant dominated)
    {start length : ℕ}
    (hfits : (allocations.getD dominant #[]).Fits start length) :
    (allocations.getD dominated #[]).Fits start length := by
  intro interval hinterval
  exact hfits interval (hdominate interval hinterval)

/-- A fixed physical anchor column participates whenever one summary uses a
selector. -/
def SummarySelectorsAnchoredBy
    (summary : RegionShapeSummary) (anchor : ℕ → RegionColumn) : Prop :=
  ∀ selector,
    RegionColumn.selector selector ∈ summary.columns →
      anchor selector ∈ physicalColumns summary.columns

/-- Every summary in a reduced synthesis footprint satisfies the selector-anchor
law. -/
def SelectorAnchoredBy (summaries : List RegionShapeSummary)
    (anchor : ℕ → RegionColumn) : Prop :=
  summaries.Forall (fun summary => SummarySelectorsAnchoredBy summary anchor)

theorem SummarySelectorsAnchoredBy.ofColumns
    {columns : List RegionColumn} {rowCount constantSiteCount : ℕ}
    {anchor : ℕ → RegionColumn}
    (hanchor : ∀ selector, .selector selector ∈ columns →
      anchor selector ∈ physicalColumns columns) :
    SummarySelectorsAnchoredBy
      (RegionSynthesisSummary.ofColumns columns rowCount constantSiteCount
        |>.toRegionShapeSummary)
      anchor := by
  intro selector hselector
  rw [RegionSynthesisSummary.toRegionShapeSummary_columns,
    RegionSynthesisSummary.ofColumns_columns]
  rw [RegionSynthesisSummary.toRegionShapeSummary_columns,
    RegionSynthesisSummary.ofColumns_columns,
    mem_unionColumns_iff] at hselector
  have hsource := hanchor selector (by simpa using hselector)
  obtain ⟨kind, index, heq⟩ := exists_column_of_mem_physicalColumns hsource
  have hphysical : .column kind index ∈ physicalColumns columns := by
    simpa only [← heq] using hsource
  rw [heq, column_mem_physicalColumns_iff, mem_unionColumns_iff]
  exact Or.inr ((column_mem_physicalColumns_iff kind index columns).mp hphysical)

theorem SummarySelectorsAnchoredBy.combine
    {left right : RegionSynthesisSummary} {anchor : ℕ → RegionColumn}
    (hleft : SummarySelectorsAnchoredBy left.toRegionShapeSummary anchor)
    (hright : SummarySelectorsAnchoredBy right.toRegionShapeSummary anchor) :
    SummarySelectorsAnchoredBy (left.combine right).toRegionShapeSummary anchor := by
  intro selector hselector
  rw [RegionSynthesisSummary.toRegionShapeSummary_columns,
    RegionSynthesisSummary.combine_columns, mem_unionColumns_iff] at hselector
  rcases hselector with hselector | hselector
  · have hanchor := hleft selector (by simpa using hselector)
    have hanchor' : anchor selector ∈ physicalColumns left.columns := by
      simpa only [RegionSynthesisSummary.toRegionShapeSummary_columns] using hanchor
    obtain ⟨kind, index, heq⟩ := exists_column_of_mem_physicalColumns hanchor
    have hphysical : .column kind index ∈ physicalColumns left.columns := by
      simpa only [← heq] using hanchor'
    rw [heq, RegionSynthesisSummary.toRegionShapeSummary_columns,
      RegionSynthesisSummary.combine_columns, column_mem_physicalColumns_iff,
      mem_unionColumns_iff]
    exact Or.inl
      ((column_mem_physicalColumns_iff kind index left.columns).mp hphysical)
  · have hanchor := hright selector (by simpa using hselector)
    have hanchor' : anchor selector ∈ physicalColumns right.columns := by
      simpa only [RegionSynthesisSummary.toRegionShapeSummary_columns] using hanchor
    obtain ⟨kind, index, heq⟩ := exists_column_of_mem_physicalColumns hanchor
    have hphysical : .column kind index ∈ physicalColumns right.columns := by
      simpa only [← heq] using hanchor'
    rw [heq, RegionSynthesisSummary.toRegionShapeSummary_columns,
      RegionSynthesisSummary.combine_columns, column_mem_physicalColumns_iff,
      mem_unionColumns_iff]
    exact Or.inr
      ((column_mem_physicalColumns_iff kind index right.columns).mp hphysical)

theorem SummarySelectorsAnchoredBy.empty (anchor : ℕ → RegionColumn) :
    SummarySelectorsAnchoredBy
      ({} : RegionSynthesisSummary).toRegionShapeSummary anchor := by
  intro selector hselector
  simp only [RegionSynthesisSummary.toRegionShapeSummary_columns] at hselector
  simp at hselector

theorem SummarySelectorsAnchoredBy.foldr_combine
    {summaries : List RegionSynthesisSummary} {anchor : ℕ → RegionColumn}
    (hsummaries : summaries.Forall fun summary =>
      SummarySelectorsAnchoredBy summary.toRegionShapeSummary anchor) :
    SummarySelectorsAnchoredBy
      (summaries.foldr RegionSynthesisSummary.combine {}
        |>.toRegionShapeSummary)
      anchor := by
  induction summaries with
  | nil => exact SummarySelectorsAnchoredBy.empty anchor
  | cons summary rest inductionHypothesis =>
      rw [List.forall_cons] at hsummaries
      exact hsummaries.1.combine (inductionHypothesis hsummaries.2)

theorem SelectorAnchoredBy.ofRegion
    {summary : RegionSynthesisSummary} {anchor : ℕ → RegionColumn}
    (hsummary : SummarySelectorsAnchoredBy summary.toRegionShapeSummary anchor) :
    SelectorAnchoredBy (SynthesisSummary.ofRegion summary).regionShapes anchor := by
  simpa [SelectorAnchoredBy] using hsummary

theorem SelectorAnchoredBy.combine
    {left right : SynthesisSummary} {anchor : ℕ → RegionColumn}
    (hleft : SelectorAnchoredBy left.regionShapes anchor)
    (hright : SelectorAnchoredBy right.regionShapes anchor) :
    SelectorAnchoredBy (left.combine right).regionShapes anchor := by
  simpa only [SelectorAnchoredBy, SynthesisSummary.combine_regionShapes,
    List.forall_append] using And.intro hleft hright

theorem SelectorAnchoredBy.replicate
    {summary : SynthesisSummary} {anchor : ℕ → RegionColumn}
    (hsummary : SelectorAnchoredBy summary.regionShapes anchor)
    (count : ℕ) :
    SelectorAnchoredBy (SynthesisSummary.replicate count summary).regionShapes
      anchor := by
  rw [SelectorAnchoredBy, SynthesisSummary.replicate_regionShapes,
    List.forall_iff_forall_mem]
  intro shape hshape
  rw [List.mem_flatten] at hshape
  obtain ⟨shapes, hshapes, hshape⟩ := hshape
  have : shapes = summary.regionShapes := List.eq_of_mem_replicate hshapes
  subst shapes
  exact List.forall_iff_forall_mem.mp hsummary shape hshape

/-- Current selector allocations are covered by the corresponding physical
anchor allocation. -/
def SelectorAllocationsDominatedBy (allocations : CircuitAllocations)
    (anchor : ℕ → RegionColumn) : Prop :=
  ∀ selector, ColumnAllocationsDominate allocations
    (anchor selector) (.selector selector)

theorem SelectorAllocationsDominatedBy.empty
    (anchor : ℕ → RegionColumn) :
    SelectorAllocationsDominatedBy (∅ : CircuitAllocations) anchor := by
  intro selector interval hinterval
  simp at hinterval

theorem ColumnsDominate.of_selectorAnchors
    {allocations : CircuitAllocations} {columns : List RegionColumn}
    {length : ℕ} {anchor : ℕ → RegionColumn}
    (hallocations : SelectorAllocationsDominatedBy allocations anchor)
    (hanchors : ∀ selector,
      RegionColumn.selector selector ∈ columns →
        anchor selector ∈ physicalColumns columns) :
    ColumnsDominate allocations (physicalColumns columns)
      (selectorColumns columns) length := by
  intro row hphysical column hcolumn
  obtain ⟨selector, rfl⟩ := exists_selector_of_mem_selectorColumns hcolumn
  have hsource := selector_mem_selectorColumns_iff selector columns |>.mp
    hcolumn
  exact (hallocations selector).fits
    (hphysical (anchor selector) (hanchors selector hsource))

theorem PlacementEffect.selectorAllocationsDominatedBy
    {before : CircuitAllocations} {columns : List RegionColumn}
    {length : ℕ} {result : Option ℕ × CircuitAllocations}
    {anchor : ℕ → RegionColumn}
    (heffect : PlacementEffect before columns length result)
    (hbefore : SelectorAllocationsDominatedBy before anchor)
    (hanchors : ∀ selector,
      RegionColumn.selector selector ∈ columns →
        anchor selector ∈ columns) :
    SelectorAllocationsDominatedBy result.2 anchor := by
  cases hrow : result.1 with
  | none =>
      intro selector interval hinterval
      rw [heffect (.selector selector), hrow] at hinterval
      rw [heffect (anchor selector), hrow]
      exact hbefore selector interval hinterval
  | some row =>
      intro selector interval hinterval
      rw [heffect (.selector selector), hrow] at hinterval
      rw [heffect (anchor selector), hrow]
      dsimp only at hinterval ⊢
      by_cases hselector : RegionColumn.selector selector ∈ columns
      · have hanchor := hanchors selector hselector
        rw [if_pos hselector, Allocations.mem_insert_iff] at hinterval
        rw [if_pos hanchor, Allocations.mem_insert_iff]
        exact hinterval.imp_right (hbefore selector interval)
      · rw [if_neg hselector] at hinterval
        by_cases hanchor : anchor selector ∈ columns
        · rw [if_pos hanchor, Allocations.mem_insert_iff]
          exact Or.inr (hbefore selector interval hinterval)
        · rw [if_neg hanchor]
          exact hbefore selector interval hinterval


end V1

/-- Remove the virtual selector portion of one reduced footprint. -/
def RegionShapeSummary.withoutSelectors
    (summary : RegionShapeSummary) : RegionShapeSummary where
  columns := physicalColumns summary.columns
  rowCount := summary.rowCount

@[simp] theorem RegionShapeSummary.withoutSelectors_key
    (summary : RegionShapeSummary) :
    summary.withoutSelectors.key = summary.key := by
  unfold RegionShapeSummary.key RegionShapeSummary.adviceCols
  simp only [RegionShapeSummary.withoutSelectors]
  have hfilter :
      (physicalColumns summary.columns).filter RegionColumn.isAdvice =
        summary.columns.filter RegionColumn.isAdvice := by
    rw [physicalColumns, List.filter_filter]
    apply List.filter_congr
    intro column _
    cases column with
    | selector => simp [RegionColumn.isAdvice]
    | column kind index => cases kind <;> simp [RegionColumn.isAdvice]
  rw [hfilter]

/-- The exact selector-free region stream consumed by physical V1 placement. -/
def SynthesisSummary.physicalRegionShapes
    (summary : SynthesisSummary) : List RegionShapeSummary :=
  summary.regionShapes.map RegionShapeSummary.withoutSelectors

theorem SynthesisSummary.combine_physicalRegionShapes
    (left right : SynthesisSummary) :
    (left.combine right).physicalRegionShapes =
      left.physicalRegionShapes ++ right.physicalRegionShapes := by
  unfold SynthesisSummary.physicalRegionShapes
  rw [SynthesisSummary.combine_regionShapes, List.map_append]

theorem SynthesisSummary.ofRegion_physicalRegionShapes
    (summary : RegionSynthesisSummary) :
    (SynthesisSummary.ofRegion summary).physicalRegionShapes =
      [summary.toRegionShapeSummary.withoutSelectors] := by
  unfold SynthesisSummary.physicalRegionShapes
  rw [SynthesisSummary.ofRegion_regionShapes]
  rfl

theorem SynthesisSummary.replicate_physicalRegionShapes
    (count : ℕ) (summary : SynthesisSummary) :
    (SynthesisSummary.replicate count summary).physicalRegionShapes =
      (List.replicate count summary.physicalRegionShapes).flatten := by
  unfold SynthesisSummary.physicalRegionShapes
  rw [SynthesisSummary.replicate_regionShapes]
  induction count with
  | zero => rfl
  | succ count inductionHypothesis =>
      rw [List.replicate_succ, List.flatten_cons, List.map_append,
        List.replicate_succ, List.flatten_cons, inductionHypothesis]

theorem Multiset.coe_flatten_replicate {α : Type} (count : ℕ)
    (items : List α) :
    ((List.replicate count items).flatten : Multiset α) =
      count • (items : Multiset α) := by
  induction count with
  | zero => rfl
  | succ count inductionHypothesis =>
      rw [List.replicate_succ, List.flatten_cons, ← Multiset.coe_add,
        inductionHypothesis, add_nsmul, one_nsmul, add_comm]

theorem SynthesisSummary.foldr_combine_physicalRegionShapes
    (summaries : List SynthesisSummary) :
    (summaries.foldr SynthesisSummary.combine {}).physicalRegionShapes =
      summaries.flatMap SynthesisSummary.physicalRegionShapes := by
  induction summaries with
  | nil => rfl
  | cons summary rest inductionHypothesis =>
      rw [List.foldr_cons, SynthesisSummary.combine_physicalRegionShapes,
        List.flatMap_cons, inductionHypothesis]


namespace V1

open Halo2 FloorPlanner

/-- Selector columns do not influence the chosen row when their allocations are
covered by physical anchors in the same region. -/
theorem placeSummary_row_eq_withoutSelectors
    (summary : RegionShapeSummary) (allocations : CircuitAllocations)
    (hvalid : allocations.Valid) (hnodup : summary.columns.Nodup)
    (hlength : 0 < summary.rowCount)
    {anchor : ℕ → RegionColumn}
    (hallocations : SelectorAllocationsDominatedBy allocations anchor)
    (hanchors : ∀ selector,
      RegionColumn.selector selector ∈ summary.columns →
        anchor selector ∈ physicalColumns summary.columns) :
    (placeSummary summary allocations).1 =
      (placeSummary summary.withoutSelectors allocations).1 := by
  let physical := sortRegionColumns (physicalColumns summary.columns)
  let selectors := sortRegionColumns (selectorColumns summary.columns)
  have hsplit : sortRegionColumns summary.columns = physical ++ selectors := by
    exact sortRegionColumns_eq_physical_append_selectors summary.columns
  have hsortedNodup : (physical ++ selectors).Nodup := by
    rw [← hsplit]
    exact (sortRegionColumns_perm summary.columns).nodup_iff.mpr hnodup
  have hdominate : ColumnsDominate allocations physical selectors
      summary.rowCount := by
    have hbase : ColumnsDominate allocations
        (physicalColumns summary.columns) (selectorColumns summary.columns)
        summary.rowCount :=
      ColumnsDominate.of_selectorAnchors hallocations hanchors
    intro row hphysical
    have hphysicalSource : FitsColumns allocations
        (physicalColumns summary.columns) row summary.rowCount :=
      hphysical.mono (fun column hcolumn =>
        (sortRegionColumns_perm
          (physicalColumns summary.columns)).mem_iff.mpr hcolumn)
    have hselectorsSource := hbase row hphysicalSource
    exact hselectorsSource.mono (fun column hcolumn =>
      (sortRegionColumns_perm
        (selectorColumns summary.columns)).mem_iff.mp hcolumn)
  have hdrop := firstFit_drop_dominated_suffix
    (physical ++ selectors).length allocations allocations [] physical
      selectors summary.rowCount 0 none hvalid hvalid
      (CircuitAllocations.Equivalent.refl allocations) hsortedNodup
      hlength le_rfl (by
        intro row hwithin column hcolumn
        simp at hcolumn) hdominate
  have hfuel := firstFit_eq_of_sufficient_fuel physical
    (physical ++ selectors).length physical.length allocations
      summary.rowCount 0 none (by simp) le_rfl
  simp only [placeSummary, RegionShapeSummary.withoutSelectors]
  rw [hsplit]
  exact hdrop.trans (congrArg Prod.fst hfuel)

/-- Allocation maps agree on every concrete planner column. -/
def CircuitAllocations.PhysicalEquivalent
    (left right : CircuitAllocations) : Prop :=
  ∀ kind index,
    left.getD (.column kind index) #[] =
      right.getD (.column kind index) #[]

theorem CircuitAllocations.PhysicalEquivalent.refl
    (allocations : CircuitAllocations) :
    CircuitAllocations.PhysicalEquivalent allocations allocations := by
  intro kind index
  rfl

theorem CircuitAllocations.PhysicalEquivalent.agreesOn
    {left right : CircuitAllocations}
    (hequivalent : CircuitAllocations.PhysicalEquivalent left right)
    (columns : List RegionColumn) :
    left.AgreesOn right (physicalColumns columns) := by
  intro column hcolumn
  rw [physicalColumns, List.mem_filter] at hcolumn
  rcases column with ⟨kind, index⟩ | selector
  · exact hequivalent kind index
  · simp at hcolumn

theorem placeSummary_effect
    (summary : RegionShapeSummary) (allocations : CircuitAllocations)
    (hvalid : allocations.Valid) (hnodup : summary.columns.Nodup)
    (hlength : 0 < summary.rowCount) :
    PlacementEffect allocations (sortRegionColumns summary.columns)
      summary.rowCount (placeSummary summary allocations) := by
  exact firstFit_effect (sortRegionColumns summary.columns).length
    allocations (sortRegionColumns summary.columns) summary.rowCount 0 none
    hvalid ((sortRegionColumns_perm summary.columns).nodup_iff.mpr hnodup)
    hlength

/-- A subinterval of a fitting interval also fits. -/
theorem Allocations.Fits.monoInterval
    {allocations : Allocations} {outerStart outerLength start length : ℕ}
    (hfits : allocations.Fits outerStart outerLength)
    (hstart : outerStart ≤ start)
    (hend : start + length ≤ outerStart + outerLength) :
    allocations.Fits start length := by
  intro allocated hallocated
  have hdisjoint := hfits allocated hallocated
  unfold RowIntervalsDisjoint at hdisjoint ⊢
  omega

/-- Fitting after an insertion means fitting before it and avoiding the newly
inserted interval. -/
theorem Allocations.fits_insert_iff
    {allocations : Allocations} {insertStart insertLength start length : ℕ} :
    (allocations.insert insertStart insertLength).Fits start length ↔
      allocations.Fits start length ∧
        RowIntervalsDisjoint start length insertStart insertLength := by
  constructor
  · intro hfits
    constructor
    · intro allocated hallocated
      exact hfits allocated
        (Allocations.mem_insert_of_mem allocations insertStart insertLength
          hallocated)
    · exact hfits (insertStart, insertLength)
        (Allocations.mem_insert allocations insertStart insertLength)
  · rintro ⟨hfits, hinserted⟩ allocated hallocated
    rw [Allocations.mem_insert_iff] at hallocated
    rcases hallocated with rfl | hallocated
    · exact hinserted
    · exact hfits allocated hallocated

/-! ## Extensional allocation views

Concrete planner traces should reason about per-column interval sequences, not the
implementation details of `Std.HashMap`. An `AllocationView` is that extensional
interface; the following transition theorem crosses the implementation boundary once.
-/

abbrev AllocationView := RegionColumn → Allocations

namespace AllocationView

def Represents
    (allocations : CircuitAllocations) (view : AllocationView) : Prop :=
  ∀ column, allocations.getD column #[] = view column

def Valid (view : AllocationView) : Prop :=
  ∀ column, (view column).Valid

def FitsColumns (view : AllocationView) (columns : List RegionColumn)
    (start length : ℕ) : Prop :=
  ∀ column ∈ columns, (view column).Fits start length

theorem FitsColumns.monoInterval
    {view : AllocationView} {columns : List RegionColumn}
    {outerStart outerLength start length : ℕ}
    (hfits : view.FitsColumns columns outerStart outerLength)
    (hstart : outerStart ≤ start)
    (hend : start + length ≤ outerStart + outerLength) :
    view.FitsColumns columns start length := by
  intro column hcolumn
  exact Allocations.Fits.monoInterval (hfits column hcolumn) hstart hend

def LeastFit (view : AllocationView) (columns : List RegionColumn)
    (length row : ℕ) : Prop :=
  FitsColumns view columns row length ∧
    ∀ candidate, FitsColumns view columns candidate length → row ≤ candidate

def insert (view : AllocationView) (columns : List RegionColumn)
    (start length : ℕ) : AllocationView := fun column =>
  if column ∈ columns then
    (view column).insert start length
  else view column

/-- Insert a consecutive run of equal-width intervals into the same columns.
The repetition count remains symbolic, so clients can compose compact planner
summaries without expanding `List.replicate`. -/
def insertRepeated (view : AllocationView) (columns : List RegionColumn)
    (start length : ℕ) : ℕ → AllocationView
  | 0 => view
  | count + 1 =>
      insertRepeated (view.insert columns start length) columns
        (start + length) length count

theorem insert_valid
    {view : AllocationView} {columns : List RegionColumn}
    {start length : ℕ} (hvalid : view.Valid)
    (hfits : view.FitsColumns columns start length)
    (hlength : 0 < length) :
    (view.insert columns start length).Valid := by
  intro column
  by_cases hcolumn : column ∈ columns
  · simp only [insert, hcolumn, ↓reduceIte]
    exact Allocations.Valid.insert (view column) start length
      (hvalid column) (hfits column hcolumn) hlength
  · simpa [insert, hcolumn] using hvalid column

theorem fitsColumns_insert_iff
    {view : AllocationView} {insertColumns columns : List RegionColumn}
    {insertStart insertLength start length : ℕ} :
    (view.insert insertColumns insertStart insertLength).FitsColumns
        columns start length ↔
      view.FitsColumns columns start length ∧
        ∀ column, column ∈ columns → column ∈ insertColumns →
          RowIntervalsDisjoint start length insertStart insertLength := by
  constructor
  · intro hfits
    constructor
    · intro column hcolumn
      by_cases hinsert : column ∈ insertColumns
      · exact Allocations.fits_insert_iff.mp
          (by simpa [insert, hinsert] using hfits column hcolumn) |>.1
      · simpa [insert, hinsert] using hfits column hcolumn
    · intro column hcolumn hinsert
      exact Allocations.fits_insert_iff.mp
        (by simpa [insert, hinsert] using hfits column hcolumn) |>.2
  · rintro ⟨hfits, hinserted⟩ column hcolumn
    by_cases hinsert : column ∈ insertColumns
    · simpa [insert, hinsert, Allocations.fits_insert_iff]
        using And.intro (hfits column hcolumn)
          (hinserted column hcolumn hinsert)
    · simpa [insert, hinsert] using hfits column hcolumn

private theorem rowIntervalsDisjoint_adjacent_iff
    (start length insertStart insertLength tailLength : ℕ)
    (hlength : 0 < length) :
    RowIntervalsDisjoint start length insertStart insertLength ∧
        RowIntervalsDisjoint start length (insertStart + insertLength)
          tailLength ↔
      RowIntervalsDisjoint start length insertStart
        (insertLength + tailLength) := by
  unfold RowIntervalsDisjoint
  omega

/-- For future placement, a nonempty repeated run behaves as its single
contiguous occupied interval. This keeps repetition counts symbolic while
checking later blocks. -/
theorem fitsColumns_insertRepeated_succ_iff
    {view : AllocationView} {insertColumns columns : List RegionColumn}
    {insertStart insertLength start length : ℕ} (count : ℕ)
    (hlength : 0 < length) :
    (view.insertRepeated insertColumns insertStart insertLength
        (count + 1)).FitsColumns columns start length ↔
      view.FitsColumns columns start length ∧
        ∀ column, column ∈ columns → column ∈ insertColumns →
          RowIntervalsDisjoint start length insertStart
            ((count + 1) * insertLength) := by
  induction count generalizing view insertStart with
  | zero =>
      simp only [insertRepeated, fitsColumns_insert_iff, Nat.zero_add,
        Nat.one_mul]
  | succ count inductionHypothesis =>
      change
        ((view.insert insertColumns insertStart insertLength).insertRepeated
          insertColumns (insertStart + insertLength) insertLength
            (count + 1)).FitsColumns columns start length ↔ _
      rw [inductionHypothesis, fitsColumns_insert_iff]
      constructor
      · rintro ⟨⟨hview, hfirst⟩, htail⟩
        refine ⟨hview, ?_⟩
        intro column hcolumn hinsert
        have hcombined :=
          (rowIntervalsDisjoint_adjacent_iff start length insertStart
            insertLength ((count + 1) * insertLength) hlength).mp
              ⟨hfirst column hcolumn hinsert,
                htail column hcolumn hinsert⟩
        simpa [Nat.add_mul, two_mul, Nat.add_comm, Nat.add_left_comm,
          Nat.add_assoc] using hcombined
      · rintro ⟨hview, hall⟩
        constructor
        · refine ⟨hview, ?_⟩
          intro column hcolumn hinsert
          have hwhole := hall column hcolumn hinsert
          have hcombined : RowIntervalsDisjoint start length insertStart
              (insertLength + (count + 1) * insertLength) := by
            simpa [Nat.add_mul, two_mul, Nat.add_comm, Nat.add_left_comm,
              Nat.add_assoc] using hwhole
          exact (rowIntervalsDisjoint_adjacent_iff start length insertStart
            insertLength ((count + 1) * insertLength) hlength).mpr hcombined |>.1
        · intro column hcolumn hinsert
          have hwhole := hall column hcolumn hinsert
          have hcombined : RowIntervalsDisjoint start length insertStart
              (insertLength + (count + 1) * insertLength) := by
            simpa [Nat.add_mul, two_mul, Nat.add_comm, Nat.add_left_comm,
              Nat.add_assoc] using hwhole
          exact (rowIntervalsDisjoint_adjacent_iff start length insertStart
            insertLength ((count + 1) * insertLength) hlength).mpr hcombined |>.2

theorem fitsColumns_insertRepeated_iff_of_pos
    {view : AllocationView} {insertColumns columns : List RegionColumn}
    {insertStart insertLength start length count : ℕ}
    (hcount : 0 < count) (hlength : 0 < length) :
    (view.insertRepeated insertColumns insertStart insertLength count).FitsColumns
        columns start length ↔
      view.FitsColumns columns start length ∧
        ∀ column, column ∈ columns → column ∈ insertColumns →
          RowIntervalsDisjoint start length insertStart
            (count * insertLength) := by
  obtain ⟨preceding, rfl⟩ := Nat.exists_eq_succ_of_ne_zero
    (Nat.ne_of_gt hcount)
  exact fitsColumns_insertRepeated_succ_iff preceding hlength

/-- Once a least fitting interval has been inserted, the adjacent interval is
the next least fit whenever the enclosing run was free beforehand. -/
theorem leastFit_insert_next
    {view : AllocationView} {columns : List RegionColumn}
    {start length remaining : ℕ}
    (hcolumns : columns ≠ []) (hlength : 0 < length)
    (hleast : view.LeastFit columns length start)
    (hfree : view.FitsColumns columns start ((remaining + 2) * length)) :
    (view.insert columns start length).LeastFit columns length
      (start + length) := by
  constructor
  · rw [fitsColumns_insert_iff]
    constructor
    · apply hfree.monoInterval
      · omega
      · simp only [Nat.add_mul]
        omega
    · intro column _ _
      unfold RowIntervalsDisjoint
      omega
  · intro candidate hcandidate
    rw [fitsColumns_insert_iff] at hcandidate
    have hstart : start ≤ candidate := hleast.2 candidate hcandidate.1
    obtain ⟨column, hcolumn⟩ := List.exists_mem_of_ne_nil columns hcolumns
    have hdisjoint := hcandidate.2 column hcolumn hcolumn
    unfold RowIntervalsDisjoint at hdisjoint
    omega

theorem fitsColumns_insert_tail
    {view : AllocationView} {columns : List RegionColumn}
    {start length remaining : ℕ}
    (hfree : view.FitsColumns columns start ((remaining + 2) * length)) :
    (view.insert columns start length).FitsColumns columns
      (start + length) ((remaining + 1) * length) := by
  rw [fitsColumns_insert_iff]
  constructor
  · apply hfree.monoInterval
    · omega
    · simp only [Nat.add_mul]
      omega
  · intro column _ _
    unfold RowIntervalsDisjoint
    omega

theorem insertRepeated_valid
    (count : ℕ) {view : AllocationView} {columns : List RegionColumn}
    {start length : ℕ} (hvalid : view.Valid)
    (hfits : view.FitsColumns columns start ((count + 1) * length))
    (hlength : 0 < length) :
    (view.insertRepeated columns start length (count + 1)).Valid := by
  induction count generalizing view start with
  | zero =>
      simp only [insertRepeated]
      exact AllocationView.insert_valid hvalid
        (hfits.monoInterval (by omega) (by omega)) hlength
  | succ count inductionHypothesis =>
      rw [show count.succ + 1 = (count + 1) + 1 by omega,
        insertRepeated]
      apply inductionHypothesis
      · exact AllocationView.insert_valid hvalid
          (hfits.monoInterval (by omega) (by
            simp only [Nat.add_mul] at hfits ⊢
            omega)) hlength
      · exact view.fitsColumns_insert_tail hfits

theorem Represents.valid
    {allocations : CircuitAllocations} {view : AllocationView}
    (hrepresents : Represents allocations view) (hvalid : view.Valid) :
    allocations.Valid := by
  intro column
  rw [hrepresents column]
  exact hvalid column

theorem Represents.leastFit
    {allocations : CircuitAllocations} {view : AllocationView}
    (hrepresents : Represents allocations view)
    {columns : List RegionColumn} {length row : ℕ}
    (hleast : view.LeastFit columns length row) :
    FloorPlanner.LeastFit allocations columns length row := by
  constructor
  · intro column hcolumn
    rw [hrepresents column]
    exact hleast.1 column hcolumn
  · intro candidate hfits
    apply hleast.2 candidate
    intro column hcolumn
    rw [← hrepresents column]
    exact hfits column hcolumn

/-- Place one summary using only an extensional allocation view. The returned view
is the old view with the chosen interval inserted in every participating column. -/
theorem placeSummary_eq_of_leastFit
    (summary : RegionShapeSummary) (allocations : CircuitAllocations)
    (view : AllocationView) (row : ℕ)
    (hrepresents : Represents allocations view) (hvalid : view.Valid)
    (hnodup : summary.columns.Nodup) (hlength : 0 < summary.rowCount)
    (hleast : view.LeastFit (sortRegionColumns summary.columns)
      summary.rowCount row) :
    ∃ updated,
      placeSummary summary allocations = (some row, updated) ∧
        Represents updated
          (view.insert (sortRegionColumns summary.columns)
            row summary.rowCount) := by
  have hactualValid := hrepresents.valid hvalid
  have hrow := placeSummary_row_eq_of_leastFit summary allocations row
    hactualValid hnodup hlength (hrepresents.leastFit hleast)
  generalize hplaced : placeSummary summary allocations = placed at hrow
  rcases placed with ⟨rowOption, updated⟩
  simp only at hrow
  have : rowOption = some row := hrow
  subst rowOption
  have heffect := placeSummary_effect summary allocations hactualValid
    hnodup hlength
  rw [hplaced] at heffect
  refine ⟨updated, rfl, ?_⟩
  intro column
  rw [heffect column]
  simp only [insert]
  split
  next => rw [hrepresents column]
  next => rw [hrepresents column]

end AllocationView

theorem physical_mem_sorted_full_iff
    (kind : ColumnKind) (index : ℕ) (columns : List RegionColumn) :
    RegionColumn.column kind index ∈ sortRegionColumns columns ↔
      RegionColumn.column kind index ∈
        sortRegionColumns (physicalColumns columns) := by
  rw [(sortRegionColumns_perm columns).mem_iff,
    (sortRegionColumns_perm (physicalColumns columns)).mem_iff,
    column_mem_physicalColumns_iff]

theorem placeSummary_physicalEquivalent
    (summary : RegionShapeSummary) (left right : CircuitAllocations)
    (hvalidLeft : left.Valid) (hvalidRight : right.Valid)
    (hnodup : summary.columns.Nodup) (hlength : 0 < summary.rowCount)
    (hbefore : CircuitAllocations.PhysicalEquivalent left right)
    (hrow : (placeSummary summary left).1 =
      (placeSummary summary.withoutSelectors right).1) :
    CircuitAllocations.PhysicalEquivalent (placeSummary summary left).2
      (placeSummary summary.withoutSelectors right).2 := by
  have hfullEffect := placeSummary_effect summary left hvalidLeft hnodup
    hlength
  have hphysicalNodup :
      (physicalColumns summary.columns).Nodup := by
    exact List.Nodup.filter _ hnodup
  have hphysicalEffect := placeSummary_effect summary.withoutSelectors right
    hvalidRight hphysicalNodup hlength
  intro kind index
  rw [hfullEffect (.column kind index),
    hphysicalEffect (.column kind index), hrow]
  cases hresult : (placeSummary summary.withoutSelectors right).1 with
  | none =>
      simpa only [hresult, RegionShapeSummary.withoutSelectors] using
        hbefore kind index
  | some row =>
      simp only [RegionShapeSummary.withoutSelectors]
      have hmember := physical_mem_sorted_full_iff kind index
        summary.columns
      by_cases hcolumn : RegionColumn.column kind index ∈
          sortRegionColumns summary.columns
      · rw [if_pos hcolumn, if_pos (hmember.mp hcolumn),
          hbefore kind index]
      · rw [if_neg hcolumn, if_neg (mt hmember.mpr hcolumn),
          hbefore kind index]

theorem placeSummary_withoutSelectors_row_congruent
    (summary : RegionShapeSummary) (left right : CircuitAllocations)
    (hvalidLeft : left.Valid) (hvalidRight : right.Valid)
    (hnodup : summary.columns.Nodup) (hlength : 0 < summary.rowCount)
    (hequivalent : CircuitAllocations.PhysicalEquivalent left right) :
    (placeSummary summary.withoutSelectors left).1 =
      (placeSummary summary.withoutSelectors right).1 := by
  let columns := sortRegionColumns (physicalColumns summary.columns)
  have hcolumnsNodup : columns.Nodup :=
    (sortRegionColumns_perm (physicalColumns summary.columns)).nodup_iff.mpr
      (List.Nodup.filter _ hnodup)
  have hagree : left.AgreesOn right columns := by
    intro column hcolumn
    have hsource := (sortRegionColumns_perm
      (physicalColumns summary.columns)).mem_iff.mp hcolumn
    obtain ⟨kind, index, rfl⟩ :=
      exists_column_of_mem_physicalColumns hsource
    exact hequivalent kind index
  have hcongruent := firstFit_congruent columns.length left columns
    summary.rowCount 0 none right hvalidLeft hvalidRight hcolumnsNodup
    hlength hagree
  exact hcongruent.1

theorem RegionShapeSummary.withoutSelectors_wellFormed
    {summary : RegionShapeSummary} (hwellFormed : summary.WellFormed) :
    summary.withoutSelectors.WellFormed := by
  constructor
  · exact List.Nodup.filter _ hwellFormed.1
  · intro hcolumns
    apply hwellFormed.2
    intro hsource
    apply hcolumns
    simp [RegionShapeSummary.withoutSelectors, physicalColumns, hsource]

/-- One full placement and one selector-free placement choose the same row and
preserve the physical-agreement and selector-domination invariants. -/
theorem placeSummary_withoutSelectors_law
    (summary : RegionShapeSummary) (left right : CircuitAllocations)
    (hvalidLeft : left.Valid) (hvalidRight : right.Valid)
    (hwellFormed : summary.WellFormed)
    {anchor : ℕ → RegionColumn}
    (hbeforePhysical : CircuitAllocations.PhysicalEquivalent left right)
    (hbeforeSelectors : SelectorAllocationsDominatedBy left anchor)
    (hanchors : ∀ selector,
      RegionColumn.selector selector ∈ summary.columns →
        anchor selector ∈ physicalColumns summary.columns) :
    let full := placeSummary summary left
    let physical := placeSummary summary.withoutSelectors right
    full.1 = physical.1 ∧
      CircuitAllocations.PhysicalEquivalent full.2 physical.2 ∧
      SelectorAllocationsDominatedBy full.2 anchor := by
  by_cases hcolumns : summary.columns = []
  · simp [placeSummary, hcolumns, RegionShapeSummary.withoutSelectors,
      physicalColumns, sortRegionColumns, firstFit]
    exact ⟨hbeforePhysical, hbeforeSelectors⟩
  · have hlength := hwellFormed.2 hcolumns
    have hleftPhysical := placeSummary_row_eq_withoutSelectors summary left
      hvalidLeft hwellFormed.1 hlength hbeforeSelectors hanchors
    have hphysicalCongruent :=
      placeSummary_withoutSelectors_row_congruent summary left right
        hvalidLeft hvalidRight hwellFormed.1 hlength hbeforePhysical
    have hrow := hleftPhysical.trans hphysicalCongruent
    have hnextPhysical := placeSummary_physicalEquivalent summary left right
      hvalidLeft hvalidRight hwellFormed.1 hlength hbeforePhysical hrow
    have hfullEffect := placeSummary_effect summary left hvalidLeft
      hwellFormed.1 hlength
    have hnextSelectors :=
      PlacementEffect.selectorAllocationsDominatedBy hfullEffect
        hbeforeSelectors (by
        intro selector hselector
        have hsource := (sortRegionColumns_perm summary.columns).mem_iff.mp
          hselector
        have hanchor := hanchors selector hsource
        apply (sortRegionColumns_perm summary.columns).mem_iff.mpr
        rw [physicalColumns, List.mem_filter] at hanchor
        exact hanchor.1)
    exact ⟨hrow, hnextPhysical, hnextSelectors⟩

/-- Selector-free slotting computes exactly the same start rows as full V1 slotting
when selectors have physical anchors. -/
theorem slotShapeSummariesFrom_eq_withoutSelectors
    (summaries : List RegionShapeSummary)
    (left right : CircuitAllocations)
    (hwellFormed : summaries.Forall RegionShapeSummary.WellFormed)
    (hvalidLeft : left.Valid) (hvalidRight : right.Valid)
    {anchor : ℕ → RegionColumn}
    (hphysical : CircuitAllocations.PhysicalEquivalent left right)
    (hselectors : SelectorAllocationsDominatedBy left anchor)
    (hanchors : SelectorAnchoredBy summaries anchor) :
    let full := slotShapeSummariesFrom summaries left
    let physical := slotShapeSummariesFrom
      (summaries.map RegionShapeSummary.withoutSelectors) right
    full.1 = physical.1 ∧
      CircuitAllocations.PhysicalEquivalent full.2 physical.2 ∧
      SelectorAllocationsDominatedBy full.2 anchor := by
  induction summaries generalizing left right with
  | nil => exact ⟨rfl, hphysical, hselectors⟩
  | cons summary rest inductionHypothesis =>
      rw [List.forall_cons] at hwellFormed
      rw [SelectorAnchoredBy, List.forall_cons] at hanchors
      have hhead := placeSummary_withoutSelectors_law summary left right
        hvalidLeft hvalidRight hwellFormed.1 hphysical hselectors
        hanchors.1
      let fullHead := placeSummary summary left
      let physicalHead := placeSummary summary.withoutSelectors right
      have hfullValid := placeSummary_valid summary left hvalidLeft
        hwellFormed.1
      have hphysicalWellFormed :=
        RegionShapeSummary.withoutSelectors_wellFormed hwellFormed.1
      have hphysicalValid := placeSummary_valid summary.withoutSelectors right
        hvalidRight hphysicalWellFormed
      have htail := inductionHypothesis fullHead.2 physicalHead.2
        hwellFormed.2 hfullValid hphysicalValid hhead.2.1 hhead.2.2
        hanchors.2
      simp only [slotShapeSummariesFrom, List.map_cons]
      rw [hhead.1, htail.1]
      exact ⟨rfl, htail.2.1, htail.2.2⟩


end V1

/-! ## The two planners -/

namespace V1

/-- Restore region-index order after largest-region-first slotting. -/
def sortPairsByIndex (pairs : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  pairs.insertionSort fun left right => left.1 ≤ right.1

theorem sortPairsByIndex_perm (pairs : List (ℕ × ℕ)) :
    (sortPairsByIndex pairs).Perm pairs := by
  exact List.perm_insertionSort
    (r := fun left right : ℕ × ℕ => left.1 ≤ right.1) pairs

private theorem sortPairsByIndex_fst_sorted (pairs : List (ℕ × ℕ)) :
    (sortPairsByIndex pairs).map (·.1) |>.SortedLE := by
  have hpairs := List.pairwise_insertionSort
    (r := fun left right : ℕ × ℕ => left.1 ≤ right.1) pairs
  have general : ∀ items : List (ℕ × ℕ),
      items.Pairwise (fun left right => left.1 ≤ right.1) →
        (items.map (·.1)).Pairwise (· ≤ ·) := by
    intro items hitems
    induction items with
    | nil => simp
    | cons head rest inductionHypothesis =>
        rw [List.pairwise_cons] at hitems
        rw [List.map_cons, List.pairwise_cons]
        constructor
        · intro item hitem
          rw [List.mem_map] at hitem
          obtain ⟨pair, hpair, rfl⟩ := hitem
          exact hitems.1 pair hpair
        · exact inductionHypothesis hitems.2
  rw [List.sortedLE_iff_pairwise]
  exact general _ hpairs

private theorem range_sortedLE (count : ℕ) :
    (List.range count).SortedLE := by
  rw [List.sortedLE_iff_pairwise]
  induction count with
  | zero => simp
  | succ count inductionHypothesis =>
      rw [List.range_succ, List.pairwise_append]
      exact ⟨inductionHypothesis, by simp, by
        intro left hleft right hright
        simp only [List.mem_singleton] at hright
        subst right
        exact Nat.le_of_lt (List.mem_range.mp hleft)⟩

private theorem sortPairsByIndex_fst_eq_range
    (pairs : List (ℕ × ℕ)) (count : ℕ)
    (hindices : (pairs.map (·.1)).Perm (List.range count)) :
    (sortPairsByIndex pairs).map (·.1) = List.range count := by
  apply List.Perm.eq_of_sortedLE
    (sortPairsByIndex_fst_sorted pairs)
    (range_sortedLE count)
  exact (sortPairsByIndex_perm pairs).map (·.1) |>.trans hindices

private theorem getD_of_mem_range_zip
    (values : List ℕ) {index value : ℕ}
    (hmember : (index, value) ∈
      (List.range values.length).zip values) :
    values.getD index 0 = value := by
  induction values generalizing index value with
  | nil => simp at hmember
  | cons head rest inductionHypothesis =>
      rw [List.length_cons, List.range_succ_eq_map,
        List.zip_cons_cons, List.mem_cons] at hmember
      rcases hmember with hhead | htail
      · have hindex : index = 0 := congrArg Prod.fst hhead
        have hvalue : value = head := congrArg Prod.snd hhead
        subst index
        subst value
        rfl
      · rw [List.zip_map_left, List.mem_map] at htail
        obtain ⟨pair, hpair, heq⟩ := htail
        rcases pair with ⟨restIndex, restValue⟩
        have hindex : restIndex + 1 = index := congrArg Prod.fst heq
        have hvalue : restValue = value := congrArg Prod.snd heq
        rw [← hindex, ← hvalue]
        exact inductionHypothesis hpair

private theorem starts_getD_of_pair_mem
    (pairs : List (ℕ × ℕ)) (count : ℕ)
    (hindices :
      (sortPairsByIndex pairs).map (·.1) = List.range count)
    {index start : ℕ}
    (hpair : (index, start) ∈ pairs) :
    ((sortPairsByIndex pairs).map (·.2)).getD index 0 = start := by
  let sorted := sortPairsByIndex pairs
  have hsortedPair : (index, start) ∈ sorted :=
    (sortPairsByIndex_perm pairs).mem_iff.mpr hpair
  have hzip : sorted =
      (List.range count).zip (sorted.map (·.2)) := by
    exact List.zip_of_prod hindices rfl
  have hlength : (sorted.map (·.2)).length = count := by
    have := congrArg List.length hindices
    simpa using this
  apply getD_of_mem_range_zip (sorted.map (·.2))
  rw [hlength, ← hzip]
  exact hsortedPair

/-- `slot_in_biggest_advice_first` (`strategy.rs:198-242`) then un-sort: sort the shapes by
`key` (legacy pdqsort), reverse (biggest advice area first), slot them in, and re-order the
resulting starts back to region-index order. Returns `(starts, finalAllocations)`. -/
def planCandidate (shapes : List RegionShape) : List ℕ × CircuitAllocations :=
  let sortedDesc := (Pdqsort.quicksort shapes.toArray (fun a b => a.key < b.key)).reverse
  let (pairs, colAllocs) := slotIn sortedDesc.toList
  let byIndex := sortPairsByIndex pairs
  (byIndex.map (·.2), colAllocs)

/-- V1's actual first-fit candidate separates every pair of shared columns. -/
theorem planCandidate_measureRegions_sharedColumnIntervalsDisjoint
    (operations : Operations F) :
    SharedColumnIntervalsDisjoint
      (measureRegions operations)
      (planCandidate (measureRegions operations)).1 := by
  let shapes := measureRegions operations
  let sortedArray :=
    (Pdqsort.quicksort shapes.toArray
      (fun left right => left.key < right.key)).reverse
  let sortedShapes := sortedArray.toList
  have hsorted : sortedShapes.Perm shapes := by
    have hquick := Pdqsort.quicksort_perm shapes.toArray
      (fun left right => left.key < right.key)
    exact (by
      simpa [sortedShapes, sortedArray] using
        (List.reverse_perm
          (Pdqsort.quicksort shapes.toArray
            (fun left right => left.key < right.key)).toList).trans hquick)
  have hwellFormed : sortedShapes.Forall RegionShape.WellFormed := by
    rw [List.forall_iff_forall_mem]
    intro shape hshape
    have hshape' : shape ∈ measureRegions operations := by
      exact hsorted.mem_iff.mp hshape
    exact (List.forall_iff_forall_mem.mp
      (measureRegions_wellFormed operations)) shape hshape'
  let slotted := slotIn sortedShapes
  let pairs := slotted.1
  have hslot : SlotInLaw (∅ : CircuitAllocations) sortedShapes slotted := by
    exact slotInFrom_law sortedShapes ∅ CircuitAllocations.Valid.empty
      hwellFormed
  have hpairsRange : (pairs.map (·.1)).Perm
      (List.range operations.regionCount) := by
    rw [hslot.indices]
    have hindices := hsorted.map RegionShape.index
    change (sortedShapes.map RegionShape.index).Perm
      ((measureRegions operations).map RegionShape.index) at hindices
    rw [measureRegions_indices_eq_range] at hindices
    exact hindices
  have hsortedIndices :
      (sortPairsByIndex pairs).map (·.1) =
        List.range operations.regionCount :=
    sortPairsByIndex_fst_eq_range pairs operations.regionCount
      hpairsRange
  have hplanStarts :
      (planCandidate (measureRegions operations)).1 =
        (sortPairsByIndex pairs).map (·.2) := by
    rfl
  intro left right hleft hright hindices column
    hleftColumn hrightColumn
  have hleftSorted : left ∈ sortedShapes := hsorted.mem_iff.mpr hleft
  have hrightSorted : right ∈ sortedShapes := hsorted.mem_iff.mpr hright
  obtain ⟨leftStart, hleftPlaced⟩ :=
    placedShapes_exists_of_mem sortedShapes pairs hslot.indices hleftSorted
  obtain ⟨rightStart, hrightPlaced⟩ :=
    placedShapes_exists_of_mem sortedShapes pairs hslot.indices hrightSorted
  have hleftPair : (left.index, leftStart) ∈ pairs :=
    pair_mem_of_mem_placedShapes sortedShapes pairs hslot.indices hleftPlaced
  have hrightPair : (right.index, rightStart) ∈ pairs :=
    pair_mem_of_mem_placedShapes sortedShapes pairs hslot.indices hrightPlaced
  have hleftStart :
      ((sortPairsByIndex pairs).map (·.2)).getD left.index 0 =
        leftStart :=
    starts_getD_of_pair_mem pairs operations.regionCount
      hsortedIndices hleftPair
  have hrightStart :
      ((sortPairsByIndex pairs).map (·.2)).getD right.index 0 =
        rightStart :=
    starts_getD_of_pair_mem pairs operations.regionCount
      hsortedIndices hrightPair
  have hplacedNe : (left, leftStart) ≠ (right, rightStart) := by
    intro heq
    apply hindices
    exact congrArg (fun placed : RegionShape × ℕ => placed.1.index) heq
  rcases rel_or_reverse_of_pairwise_of_mem hslot.disjoint
      hleftPlaced hrightPlaced hplacedNe with hforward | hreverse
  · rw [hplanStarts, hleftStart, hrightStart]
    exact hforward column hleftColumn hrightColumn
  · have hdisjoint := hreverse column hrightColumn hleftColumn
    rw [hplanStarts, hleftStart, hrightStart]
    exact hdisjoint.elim Or.inr Or.inl

/-- Apply the proven-safe V1 planner to the regions measured from an operation stream.
Keep the planner opaque to type-class inference and expose its behavior propositionally. -/
irreducible_def planOperations
    (operations : Operations F) : List ℕ × CircuitAllocations :=
  planCandidate (measureRegions operations)

theorem planOperations_eq
    (operations : Operations F) :
    planOperations operations = planCandidate (measureRegions operations) := by
  rw [planOperations]

/-- The V1 region starts, per `assignRegion` index, from the operation stream. -/
def starts (ops : Operations F) : List ℕ := (planOperations ops).1

def placementEndFrom (shapes : List RegionShape) (regionStarts : List ℕ) : ℕ :=
  shapes.map (fun shape =>
    regionStarts.getD shape.index 0 + shape.rowCount)
    |>.foldl max 0

/-- One past the final row in slotting order. Unlike `placementEndFrom`, this
projection does not restore region-index order and therefore forgets indices entirely. -/
def slottedEndFrom (shapes : List RegionShape)
    (pairs : List (ℕ × ℕ)) : ℕ :=
  (placedShapes shapes pairs).map (fun placed =>
    placed.2 + placed.1.rowCount) |>.foldl max 0

/-- The same endpoint projection directly over the index-free synthesis summary. -/
def slottedSummaryEndFrom (summaries : List RegionShapeSummary)
    (starts : List ℕ) : ℕ :=
  (summaries.zip starts).map (fun placed =>
    placed.2 + placed.1.rowCount) |>.foldl max 0

/-- Erasing selector columns preserves the endpoint projection for any fixed
start-row sequence. -/
theorem slottedSummaryEndFrom_map_withoutSelectors
    (summaries : List RegionShapeSummary) (starts : List ℕ) :
    slottedSummaryEndFrom
        (summaries.map RegionShapeSummary.withoutSelectors) starts =
      slottedSummaryEndFrom summaries starts := by
  unfold slottedSummaryEndFrom
  apply congrArg (List.foldl max 0)
  induction summaries generalizing starts with
  | nil => rfl
  | cons summary rest inductionHypothesis =>
      cases starts with
      | nil => rfl
      | cons start starts =>
          simp only [List.map_cons, List.zip_cons_cons,
            RegionShapeSummary.withoutSelectors]
          rw [inductionHypothesis]

/-- When selector allocations are dominated by physical anchor columns, erasing
selectors preserves the exact endpoint as well as every chosen start row. -/
theorem slotSummaryEndFrom_eq_withoutSelectors
    (summaries : List RegionShapeSummary)
    (left right : CircuitAllocations)
    (hwellFormed : summaries.Forall RegionShapeSummary.WellFormed)
    (hvalidLeft : left.Valid) (hvalidRight : right.Valid)
    {anchor : ℕ → RegionColumn}
    (hphysical : CircuitAllocations.PhysicalEquivalent left right)
    (hselectors : SelectorAllocationsDominatedBy left anchor)
    (hanchors : SelectorAnchoredBy summaries anchor) :
    slottedSummaryEndFrom summaries
        (slotShapeSummariesFrom summaries left).1 =
      slottedSummaryEndFrom
        (summaries.map RegionShapeSummary.withoutSelectors)
        (slotShapeSummariesFrom
          (summaries.map RegionShapeSummary.withoutSelectors) right).1 := by
  have hstarts := (slotShapeSummariesFrom_eq_withoutSelectors summaries
    left right hwellFormed hvalidLeft hvalidRight hphysical hselectors
    hanchors).1
  rw [← hstarts, slottedSummaryEndFrom_map_withoutSelectors]

/-- Exact end row obtained by slotting an index-free reduced summary, folded
from an existing end row. -/
def slotSummaryEndFromWith (initial : ℕ)
    (summaries : List RegionShapeSummary)
    (allocations : CircuitAllocations) : ℕ :=
  (summaries.zip (slotShapeSummariesFrom summaries allocations).1).map
    (fun placed => placed.2 + placed.1.rowCount) |>.foldl max initial

/-- The endpoint and final allocation state produced by a summary sequence. Keeping
the two together makes compact block replacement compositional. -/
def slotSummaryStateFromWith (initial : ℕ)
    (summaries : List RegionShapeSummary)
    (allocations : CircuitAllocations) : ℕ × CircuitAllocations :=
  match summaries with
  | [] => (initial, allocations)
  | summary :: rest =>
      let placed := placeSummary summary allocations
      slotSummaryStateFromWith
        (max initial (placed.1.getD 0 + summary.rowCount)) rest placed.2

theorem slotSummaryStateFromWith_fst
    (initial : ℕ) (summaries : List RegionShapeSummary)
    (allocations : CircuitAllocations) :
    (slotSummaryStateFromWith initial summaries allocations).1 =
      slotSummaryEndFromWith initial summaries allocations := by
  induction summaries generalizing initial allocations with
  | nil => rfl
  | cons summary rest inductionHypothesis =>
      generalize hplaced : placeSummary summary allocations = placed
      rcases placed with ⟨row, updated⟩
      have hcons :
          slotSummaryEndFromWith initial (summary :: rest) allocations =
            slotSummaryEndFromWith
              (max initial (row.getD 0 + summary.rowCount)) rest updated := by
        unfold slotSummaryEndFromWith
        simp only [slotShapeSummariesFrom, hplaced, List.zip_cons_cons,
          List.map_cons, List.foldl_cons]
      rw [hcons]
      simp only [slotSummaryStateFromWith, hplaced]
      exact inductionHypothesis _ _

theorem slotSummaryStateFromWith_snd
    (initial : ℕ) (summaries : List RegionShapeSummary)
    (allocations : CircuitAllocations) :
    (slotSummaryStateFromWith initial summaries allocations).2 =
      (slotShapeSummariesFrom summaries allocations).2 := by
  induction summaries generalizing initial allocations with
  | nil => rfl
  | cons summary rest inductionHypothesis =>
      generalize hplaced : placeSummary summary allocations = placed
      rcases placed with ⟨row, updated⟩
      simp only [slotSummaryStateFromWith, slotShapeSummariesFrom, hplaced]
      exact inductionHypothesis _ _

theorem slotSummaryStateFromWith_append
    (initial : ℕ) (left right : List RegionShapeSummary)
    (allocations : CircuitAllocations) :
    slotSummaryStateFromWith initial (left ++ right) allocations =
      let leftResult :=
        slotSummaryStateFromWith initial left allocations
      slotSummaryStateFromWith leftResult.1 right leftResult.2 := by
  induction left generalizing initial allocations with
  | nil => rfl
  | cons summary rest inductionHypothesis =>
      generalize hplaced : placeSummary summary allocations = placed
      rcases placed with ⟨row, updated⟩
      simp only [List.cons_append, slotSummaryStateFromWith, hplaced]
      exact inductionHypothesis _ _

/-- Repeatedly place one compact summary block while retaining its repetition
count. -/
def slotSummaryStateRepeated (count : ℕ)
    (summaries : List RegionShapeSummary) (initial : ℕ)
    (allocations : CircuitAllocations) : ℕ × CircuitAllocations :=
  match count with
  | 0 => (initial, allocations)
  | count + 1 =>
      let first := slotSummaryStateFromWith initial summaries allocations
      slotSummaryStateRepeated count summaries first.1 first.2

theorem slotSummaryStateFromWith_flatten_replicate
    (count : ℕ) (summaries : List RegionShapeSummary)
    (initial : ℕ) (allocations : CircuitAllocations) :
    slotSummaryStateFromWith initial
        (List.replicate count summaries).flatten allocations =
      slotSummaryStateRepeated count summaries initial allocations := by
  induction count generalizing initial allocations with
  | zero => rfl
  | succ count inductionHypothesis =>
      rw [List.replicate_succ, List.flatten_cons,
        slotSummaryStateFromWith_append]
      simp only [slotSummaryStateRepeated]
      rw [inductionHypothesis]

/-- Evaluate a sequence of repeated singleton-summary blocks without expanding
any block into a concrete list. -/
def slotSummaryBlocksState (blocks : List (ℕ × RegionShapeSummary))
    (initial : ℕ) (allocations : CircuitAllocations) :
    ℕ × CircuitAllocations :=
  match blocks with
  | [] => (initial, allocations)
  | (count, summary) :: rest =>
      let first := slotSummaryStateRepeated count [summary]
        initial allocations
      slotSummaryBlocksState rest first.1 first.2

theorem slotSummaryStateFromWith_flatMap_replicate
    (blocks : List (ℕ × RegionShapeSummary))
    (initial : ℕ) (allocations : CircuitAllocations) :
    slotSummaryStateFromWith initial
        (blocks.flatMap fun block =>
          List.replicate block.1 block.2) allocations =
      slotSummaryBlocksState blocks initial allocations := by
  induction blocks generalizing initial allocations with
  | nil => rfl
  | cons block rest inductionHypothesis =>
      rcases block with ⟨count, summary⟩
      rw [List.flatMap_cons, slotSummaryStateFromWith_append,
        ← List.flatten_replicate_singleton,
        slotSummaryStateFromWith_flatten_replicate]
      simp only [slotSummaryBlocksState]
      exact inductionHypothesis _ _

/-- If a free run begins at the current least fit, repeated copies of one
summary occupy that run consecutively. Besides the endpoint, expose an
extensional view of the resulting allocation state so consecutive compact
blocks can be composed without expanding the repetition. -/
theorem slotSummaryStateRepeated_single_eq
    (count : ℕ) (summary : RegionShapeSummary)
    (initial : ℕ) (allocations : CircuitAllocations)
    (view : AllocationView) (start : ℕ)
    (hrepresents : view.Represents allocations)
    (hvalid : view.Valid)
    (hnodup : summary.columns.Nodup)
    (hcolumns : summary.columns ≠ [])
    (hlength : 0 < summary.rowCount)
    (hleast : view.LeastFit (sortRegionColumns summary.columns)
      summary.rowCount start)
    (hfree : view.FitsColumns (sortRegionColumns summary.columns) start
      ((count + 1) * summary.rowCount)) :
    let result := slotSummaryStateRepeated (count + 1) [summary]
      initial allocations
    result.1 = max initial (start + (count + 1) * summary.rowCount) ∧
      (view.insertRepeated (sortRegionColumns summary.columns) start
        summary.rowCount (count + 1)).Represents result.2 := by
  induction count generalizing initial allocations view start with
  | zero =>
      obtain ⟨updated, hplaced, hupdatedRepresents⟩ :=
        view.placeSummary_eq_of_leastFit summary allocations start
          hrepresents hvalid hnodup hlength hleast
      simp only [slotSummaryStateRepeated, slotSummaryStateFromWith, hplaced,
        Option.getD_some, AllocationView.insertRepeated]
      exact ⟨by omega, hupdatedRepresents⟩
  | succ count inductionHypothesis =>
      let columns := sortRegionColumns summary.columns
      have hsortedColumns : columns ≠ [] := by
        intro hempty
        have hlengths := (sortRegionColumns_perm summary.columns).length_eq
        have : summary.columns.length = 0 := by
          simpa [columns, hempty] using hlengths.symm
        exact hcolumns (List.eq_nil_of_length_eq_zero this)
      obtain ⟨updated, hplaced, hupdatedRepresents⟩ :=
        view.placeSummary_eq_of_leastFit summary allocations start
          hrepresents hvalid hnodup hlength hleast
      have hactualValid : allocations.Valid := hrepresents.valid hvalid
      have hsummaryWellFormed : summary.WellFormed :=
        ⟨hnodup, fun _ => hlength⟩
      have hupdatedValidActual : updated.Valid := by
        have hresult := placeSummary_valid summary allocations hactualValid
          hsummaryWellFormed
        rw [hplaced] at hresult
        exact hresult
      have hupdatedValid :
          (view.insert columns start summary.rowCount).Valid := by
        intro column
        rw [← hupdatedRepresents column]
        exact hupdatedValidActual column
      have hnextLeast := view.leastFit_insert_next hsortedColumns hlength
        hleast hfree
      have htailFree := view.fitsColumns_insert_tail hfree
      have hrecursive := inductionHypothesis
        (max initial (start + summary.rowCount)) updated
        (view.insert columns start summary.rowCount)
        (start + summary.rowCount) hupdatedRepresents hupdatedValid
        hnextLeast htailFree
      rw [show count.succ + 1 = (count + 1) + 1 by omega,
        slotSummaryStateRepeated]
      simp only [slotSummaryStateFromWith, hplaced, Option.getD_some,
        AllocationView.insertRepeated]
      exact ⟨by
          simp only [Nat.add_mul] at hrecursive ⊢
          omega,
        hrecursive.2⟩

/-- Endpoint-only form of `slotSummaryStateRepeated_single_eq`. -/
theorem slotSummaryStateRepeated_single_fst_eq
    (count : ℕ) (summary : RegionShapeSummary)
    (initial : ℕ) (allocations : CircuitAllocations)
    (view : AllocationView) (start : ℕ)
    (hrepresents : view.Represents allocations)
    (hvalid : view.Valid)
    (hnodup : summary.columns.Nodup)
    (hcolumns : summary.columns ≠ [])
    (hlength : 0 < summary.rowCount)
    (hleast : view.LeastFit (sortRegionColumns summary.columns)
      summary.rowCount start)
    (hfree : view.FitsColumns (sortRegionColumns summary.columns) start
      ((count + 1) * summary.rowCount))
    (hinitial : initial ≤ start + summary.rowCount) :
    (slotSummaryStateRepeated (count + 1) [summary]
      initial allocations).1 = start + (count + 1) * summary.rowCount :=
  (slotSummaryStateRepeated_single_eq count summary initial allocations
    view start hrepresents hvalid hnodup hcolumns hlength hleast hfree).1.trans
      (max_eq_right (hinitial.trans (by
        exact Nat.add_le_add_left
          (Nat.le_mul_of_pos_left summary.rowCount (Nat.succ_pos count))
          start)))

/-- One compact, already-planned run of equal region summaries. -/
structure PlannedSummaryBlock where
  count : ℕ
  summary : RegionShapeSummary
  start : ℕ

namespace PlannedSummaryBlock

def blocks (trace : List PlannedSummaryBlock) :
    List (ℕ × RegionShapeSummary) :=
  trace.map fun block => (block.count, block.summary)

def endpointFrom (initial : ℕ) : List PlannedSummaryBlock → ℕ
  | [] => initial
  | block :: rest =>
      endpointFrom
        (max initial (block.start + block.count * block.summary.rowCount))
        rest

def finalView (initial : AllocationView) :
    List PlannedSummaryBlock → AllocationView
  | [] => initial
  | block :: rest =>
      finalView
        (initial.insertRepeated (sortRegionColumns block.summary.columns)
          block.start block.summary.rowCount block.count)
        rest

def Lawful (initial : AllocationView) :
    List PlannedSummaryBlock → Prop
  | [] => True
  | block :: rest =>
      0 < block.count ∧
      block.summary.WellFormed ∧
      block.summary.columns ≠ [] ∧
      initial.LeastFit (sortRegionColumns block.summary.columns)
        block.summary.rowCount block.start ∧
      initial.FitsColumns (sortRegionColumns block.summary.columns)
        block.start (block.count * block.summary.rowCount) ∧
      Lawful
        (initial.insertRepeated (sortRegionColumns block.summary.columns)
          block.start block.summary.rowCount block.count)
        rest

theorem slotSummaryBlocksState_eq
    (trace : List PlannedSummaryBlock)
    (initial : ℕ) (allocations : CircuitAllocations)
    (view : AllocationView)
    (hrepresents : view.Represents allocations)
    (hvalid : view.Valid) (hlawful : Lawful view trace) :
    let result := slotSummaryBlocksState (blocks trace) initial allocations
    result.1 = endpointFrom initial trace ∧
      (finalView view trace).Represents result.2 := by
  induction trace generalizing initial allocations view with
  | nil => exact ⟨rfl, hrepresents⟩
  | cons block rest inductionHypothesis =>
      rcases block with ⟨blockCount, summary, start⟩
      rcases hlawful with
        ⟨hcount, hwellFormed, hcolumns, hleast, hfits, hrest⟩
      obtain ⟨count, rfl⟩ := Nat.exists_eq_succ_of_ne_zero
        (Nat.ne_of_gt hcount)
      let first := slotSummaryStateRepeated (count + 1) [summary]
        initial allocations
      have hfirst := slotSummaryStateRepeated_single_eq count summary
        initial allocations view start hrepresents hvalid
        hwellFormed.1 hcolumns (hwellFormed.2 hcolumns) hleast hfits
      have hnextValid := view.insertRepeated_valid count hvalid hfits
        (hwellFormed.2 hcolumns)
      have htail := inductionHypothesis first.1 first.2
        (view.insertRepeated (sortRegionColumns summary.columns)
          start summary.rowCount (count + 1))
        hfirst.2 hnextValid hrest
      simp only [blocks, List.map_cons, slotSummaryBlocksState,
        endpointFrom, finalView]
      exact ⟨by rw [← hfirst.1]; exact htail.1, htail.2⟩

end PlannedSummaryBlock

theorem slotSummaryEndFromWith_cons
    (initial : ℕ) (head : RegionShapeSummary)
    (tail : List RegionShapeSummary)
    (allocations : CircuitAllocations) :
    slotSummaryEndFromWith initial (head :: tail) allocations =
      let placed := placeSummary head allocations
      slotSummaryEndFromWith
        (max initial (placed.1.getD 0 + head.rowCount)) tail placed.2 := by
  generalize hplaced : placeSummary head allocations = placed
  rcases placed with ⟨row, updated⟩
  unfold slotSummaryEndFromWith
  simp only [slotShapeSummariesFrom, hplaced, List.zip_cons_cons,
    List.map_cons, List.foldl_cons]

/-- Exact end row obtained by slotting an index-free reduced summary. -/
def slotSummaryEndFrom (summaries : List RegionShapeSummary)
    (allocations : CircuitAllocations) : ℕ :=
  slotSummaryEndFromWith 0 summaries allocations

/-- Placement-equivalent summaries may be exchanged without changing either the
endpoint or the allocator state seen by the suffix. -/
theorem slotSummaryEndFromWith_swap_of_placementEquivalent
    (initial : ℕ) (left right : RegionShapeSummary)
    (tail : List RegionShapeSummary) (allocations : CircuitAllocations)
    (hequivalent : left.PlacementEquivalent right) :
    slotSummaryEndFromWith initial (left :: right :: tail) allocations =
      slotSummaryEndFromWith initial (right :: left :: tail) allocations := by
  have hplace : ∀ current,
      placeSummary left current = placeSummary right current :=
    placeSummary_eq_of_placementEquivalent hequivalent
  simp only [slotSummaryEndFromWith_cons, hplace, hequivalent.2]

/-- Swapping two disjoint regions changes neither their individual placements nor
the final endpoint, including the placement of every following region. -/
theorem slotSummaryEndFromWith_swap
    (initial : ℕ)
    (left right : RegionShapeSummary)
    (tail : List RegionShapeSummary)
    (allocations : CircuitAllocations)
    (hvalid : allocations.Valid)
    (hleftNodup : left.columns.Nodup)
    (hrightNodup : right.columns.Nodup)
    (hleftLength : 0 < left.rowCount)
    (hrightLength : 0 < right.rowCount)
    (hdisjoint : List.Disjoint left.columns right.columns)
    (htail : tail.Forall RegionShapeSummary.WellFormed) :
    slotSummaryEndFromWith initial (left :: right :: tail) allocations =
      slotSummaryEndFromWith initial (right :: left :: tail) allocations := by
  have hcommute := placeSummary_commute left right allocations hvalid
    hleftNodup hrightNodup hleftLength hrightLength hdisjoint
  generalize hleftFirst : placeSummary left allocations = leftFirst
    at hcommute
  rcases leftFirst with ⟨leftRow, leftAllocations⟩
  generalize hrightFirst : placeSummary right allocations = rightFirst
    at hcommute
  rcases rightFirst with ⟨rightRow, rightAllocations⟩
  generalize hleftThenRight :
    placeSummary right leftAllocations = leftThenRight at hcommute
  rcases leftThenRight with
    ⟨rightRowAfterLeft, leftThenRightAllocations⟩
  generalize hrightThenLeft :
    placeSummary left rightAllocations = rightThenLeft at hcommute
  rcases rightThenLeft with
    ⟨leftRowAfterRight, rightThenLeftAllocations⟩
  simp only [hleftThenRight, hrightThenLeft] at hcommute
  have hleftLaw := placeSummary_law left allocations hvalid
    hleftNodup hleftLength
  have hrightLaw := placeSummary_law right allocations hvalid
    hrightNodup hrightLength
  rw [hleftFirst] at hleftLaw
  rw [hrightFirst] at hrightLaw
  have hleftThenRightLaw := placeSummary_law right leftAllocations
    hleftLaw.1.valid hrightNodup hrightLength
  have hrightThenLeftLaw := placeSummary_law left rightAllocations
    hrightLaw.1.valid hleftNodup hleftLength
  rw [hleftThenRight] at hleftThenRightLaw
  rw [hrightThenLeft] at hrightThenLeftLaw
  have hsuffix := slotShapeSummariesFrom_equivalent tail
    leftThenRightAllocations rightThenLeftAllocations htail
    hleftThenRightLaw.1.valid hrightThenLeftLaw.1.valid hcommute.2.2
  unfold slotSummaryEndFromWith
  simp only [slotShapeSummariesFrom, hleftFirst, hrightFirst,
    hleftThenRight, hrightThenLeft]
  rw [hcommute.1, hcommute.2.1, hsuffix.1]
  simp only [List.zip_cons_cons, List.map_cons, List.foldl_cons]
  congr 1
  rw [Nat.max_assoc, Nat.max_assoc,
    Nat.max_comm (leftRowAfterRight.getD 0 + left.rowCount)
      (rightRowAfterLeft.getD 0 + right.rowCount)]

/-- The zero-based endpoint specialization of disjoint-region commutation. -/
theorem slotSummaryEndFrom_swap
    (left right : RegionShapeSummary)
    (tail : List RegionShapeSummary)
    (allocations : CircuitAllocations)
    (hvalid : allocations.Valid)
    (hleftNodup : left.columns.Nodup)
    (hrightNodup : right.columns.Nodup)
    (hleftLength : 0 < left.rowCount)
    (hrightLength : 0 < right.rowCount)
    (hdisjoint : List.Disjoint left.columns right.columns)
    (htail : tail.Forall RegionShapeSummary.WellFormed) :
    slotSummaryEndFrom (left :: right :: tail) allocations =
      slotSummaryEndFrom (right :: left :: tail) allocations := by
  exact slotSummaryEndFromWith_swap 0 left right tail allocations hvalid
    hleftNodup hrightNodup hleftLength hrightLength hdisjoint htail

/-- The disjoint swap theorem with the empty-region case derived from summary
well-formedness. -/
theorem slotSummaryEndFromWith_swap_of_wellFormed
    (initial : ℕ) (left right : RegionShapeSummary)
    (tail : List RegionShapeSummary)
    (allocations : CircuitAllocations)
    (hvalid : allocations.Valid)
    (hleft : left.WellFormed) (hright : right.WellFormed)
    (hdisjoint : List.Disjoint left.columns right.columns)
    (htail : tail.Forall RegionShapeSummary.WellFormed) :
    slotSummaryEndFromWith initial (left :: right :: tail) allocations =
      slotSummaryEndFromWith initial (right :: left :: tail) allocations := by
  by_cases hleftColumns : left.columns = []
  · have hleftPlace : ∀ current,
        placeSummary left current = (some 0, current) := by
      intro current
      simp [placeSummary, hleftColumns, sortRegionColumns, firstFit]
    generalize hrightPlace : placeSummary right allocations = rightResult
    rcases rightResult with ⟨rightRow, updated⟩
    unfold slotSummaryEndFromWith
    simp only [slotShapeSummariesFrom, hleftPlace, hrightPlace,
      List.zip_cons_cons, List.map_cons, List.foldl_cons]
    congr 1
    rw [Nat.max_assoc, Nat.max_assoc,
      Nat.max_comm ((some 0).getD 0 + left.rowCount)
        (rightRow.getD 0 + right.rowCount)]
  · by_cases hrightColumns : right.columns = []
    · have hrightPlace : ∀ current,
          placeSummary right current = (some 0, current) := by
        intro current
        simp [placeSummary, hrightColumns, sortRegionColumns, firstFit]
      generalize hleftPlace : placeSummary left allocations = leftResult
      rcases leftResult with ⟨leftRow, updated⟩
      unfold slotSummaryEndFromWith
      simp only [slotShapeSummariesFrom, hrightPlace, hleftPlace,
        List.zip_cons_cons, List.map_cons, List.foldl_cons]
      congr 1
      rw [Nat.max_assoc, Nat.max_assoc,
        Nat.max_comm (leftRow.getD 0 + left.rowCount)
          ((some 0).getD 0 + right.rowCount)]
    · exact slotSummaryEndFromWith_swap initial left right tail
        allocations hvalid hleft.1 hright.1 (hleft.2 hleftColumns)
        (hright.2 hrightColumns) hdisjoint htail

/-- Every pair of summaries may be reordered without changing V1 placement: equal
summaries trivially commute, while distinct summaries use disjoint columns. -/
def PairwisePlacementCommutative
    (summaries : List RegionShapeSummary) : Prop :=
  ∀ left, left ∈ summaries → ∀ right, right ∈ summaries →
    left = right ∨ List.Disjoint left.columns right.columns

/-- Any permutation of a pairwise-commutative summary block has the same exact
endpoint, even when followed by an arbitrary well-formed suffix. -/
theorem slotSummaryEndFromWith_perm
    {left right : List RegionShapeSummary} (hperm : left.Perm right)
    (hwellFormed : left.Forall RegionShapeSummary.WellFormed)
    (hcommutative : PairwisePlacementCommutative left)
    (initial : ℕ) (allocations : CircuitAllocations)
    (hvalid : allocations.Valid) (tail : List RegionShapeSummary)
    (htail : tail.Forall RegionShapeSummary.WellFormed) :
    slotSummaryEndFromWith initial (left ++ tail) allocations =
      slotSummaryEndFromWith initial (right ++ tail) allocations := by
  induction hperm generalizing initial allocations tail with
  | nil => rfl
  | cons head hperm inductionHypothesis =>
      rw [List.forall_cons] at hwellFormed
      generalize hplaced : placeSummary head allocations = placed
      rcases placed with ⟨row, updated⟩
      have hupdatedValid : updated.Valid := by
        have hresult := placeSummary_valid head allocations hvalid
          hwellFormed.1
        rw [hplaced] at hresult
        exact hresult
      have hrest := inductionHypothesis hwellFormed.2 (by
        intro first hfirst second hsecond
        exact hcommutative first (by simp [hfirst]) second (by simp [hsecond]))
        (max initial (row.getD 0 + head.rowCount)) updated hupdatedValid
        tail htail
      simpa only [List.cons_append, slotSummaryEndFromWith_cons,
        hplaced] using hrest
  | swap first second rest =>
      rw [List.forall_cons, List.forall_cons] at hwellFormed
      have hpair := hcommutative first (by simp) second (by simp)
      rcases hpair with rfl | hdisjoint
      · rfl
      · symm
        simpa only [List.cons_append] using
          slotSummaryEndFromWith_swap_of_wellFormed initial first second
            (rest ++ tail) allocations hvalid hwellFormed.2.1
            hwellFormed.1 hdisjoint (by
              rw [List.forall_append]
              exact ⟨hwellFormed.2.2, htail⟩)
  | trans hleft hright leftInduction rightInduction =>
      exact (leftInduction hwellFormed hcommutative initial allocations
        hvalid tail htail).trans
          (rightInduction (by
              rw [List.forall_iff_forall_mem]
              intro summary hsummary
              exact List.forall_iff_forall_mem.mp hwellFormed summary
                (hleft.mem_iff.mpr hsummary)) (by
              intro first hfirst second hsecond
              exact hcommutative first (hleft.mem_iff.mpr hfirst)
                second (hleft.mem_iff.mpr hsecond)) initial allocations
            hvalid tail htail)

/-- Move one summary across a prefix of summaries that commute with it. -/
theorem slotSummaryEndFromWith_bubble
    (pivot : RegionShapeSummary)
    (before suffix tail : List RegionShapeSummary)
    (hwellBefore : before.Forall RegionShapeSummary.WellFormed)
    (hwellPivot : pivot.WellFormed)
    (hcommutes : ∀ item, item ∈ before →
      item.PlacementEquivalent pivot ∨
        List.Disjoint item.columns pivot.columns)
    (initial : ℕ) (allocations : CircuitAllocations)
    (hvalid : allocations.Valid)
    (hwellSuffix : suffix.Forall RegionShapeSummary.WellFormed)
    (hwellTail : tail.Forall RegionShapeSummary.WellFormed) :
    slotSummaryEndFromWith initial
        ((before ++ pivot :: suffix) ++ tail) allocations =
      slotSummaryEndFromWith initial
        ((pivot :: before ++ suffix) ++ tail) allocations := by
  induction before generalizing initial allocations with
  | nil => rfl
  | cons head rest inductionHypothesis =>
      rw [List.forall_cons] at hwellBefore
      generalize hplaced : placeSummary head allocations = placed
      rcases placed with ⟨row, updated⟩
      have hupdatedValid : updated.Valid := by
        have hresult := placeSummary_valid head allocations hvalid
          hwellBefore.1
        rw [hplaced] at hresult
        exact hresult
      have hrest := inductionHypothesis hwellBefore.2 (by
          intro item hitem
          exact hcommutes item (by simp [hitem]))
        (max initial (row.getD 0 + head.rowCount)) updated hupdatedValid
      have hbubbled :
          slotSummaryEndFromWith initial
              ((head :: rest ++ pivot :: suffix) ++ tail) allocations =
            slotSummaryEndFromWith initial
              ((head :: pivot :: rest ++ suffix) ++ tail) allocations := by
        simpa only [List.cons_append, slotSummaryEndFromWith_cons,
          hplaced] using hrest
      have hpair := hcommutes head (by simp)
      rcases hpair with hequivalent | hdisjoint
      · exact hbubbled.trans (by
          simpa only [List.cons_append] using
            slotSummaryEndFromWith_swap_of_placementEquivalent initial head
              pivot ((rest ++ suffix) ++ tail) allocations hequivalent)
      · exact hbubbled.trans (by
          simpa only [List.cons_append] using
            slotSummaryEndFromWith_swap_of_wellFormed initial head pivot
              ((rest ++ suffix) ++ tail) allocations hvalid hwellBefore.1
              hwellPivot hdisjoint (by
                rw [List.forall_append, List.forall_append]
                exact ⟨⟨hwellBefore.2, hwellSuffix⟩, hwellTail⟩))

theorem perm_bubble (pivot : RegionShapeSummary)
    (before suffix : List RegionShapeSummary) :
    (before ++ pivot :: suffix).Perm (pivot :: before ++ suffix) := by
  induction before with
  | nil => rfl
  | cons head rest inductionHypothesis =>
      exact (inductionHypothesis.cons head).trans
        (List.Perm.swap pivot head (rest ++ suffix))

/-- For two key-sorted permutations, V1's endpoint is insensitive to the order
within tied-key runs whenever tied summaries are placement-equivalent or
column-disjoint. -/
theorem slotSummaryEndFromWith_eq_of_sorted_perm_interchangeable
    {K : Type} [LinearOrder K] (key : RegionShapeSummary → K)
    {left right : List RegionShapeSummary}
    (hperm : left.Perm right)
    (hsortedLeft : (left.map key).SortedLE)
    (hsortedRight : (right.map key).SortedLE)
    (hwellFormed : left.Forall RegionShapeSummary.WellFormed)
    (hties : ∀ first, first ∈ left → ∀ second, second ∈ left →
      key first = key second →
        first.PlacementEquivalent second ∨
          List.Disjoint first.columns second.columns)
    (initial : ℕ) (allocations : CircuitAllocations)
    (hvalid : allocations.Valid) (tail : List RegionShapeSummary)
    (hwellTail : tail.Forall RegionShapeSummary.WellFormed) :
    slotSummaryEndFromWith initial (left ++ tail) allocations =
      slotSummaryEndFromWith initial (right ++ tail) allocations := by
  induction left generalizing right initial allocations tail with
  | nil =>
      have : right = [] := hperm.symm.eq_nil
      subst right
      rfl
  | cons pivot rest inductionHypothesis =>
      have hpivotRight : pivot ∈ right := hperm.subset (by simp)
      obtain ⟨before, suffix, hright⟩ := List.mem_iff_append.mp hpivotRight
      subst right
      rw [List.forall_cons] at hwellFormed
      have hsortedLeftCons := hsortedLeft
      rw [List.sortedLE_iff_pairwise, List.map_cons,
        List.pairwise_cons] at hsortedLeftCons
      have hsortedRightAppend := hsortedRight
      rw [List.sortedLE_iff_pairwise, List.map_append, List.map_cons,
        List.pairwise_append] at hsortedRightAppend
      have hkeysEqual :
          (key pivot :: rest.map key) =
            before.map key ++ key pivot :: suffix.map key :=
        List.Perm.eq_of_sortedLE hsortedLeft (by
          simpa only [List.map_append, List.map_cons] using hsortedRight)
          (by simpa only [List.map_append, List.map_cons] using hperm.map key)
      have hlower : ∀ item,
          item ∈ before ++ pivot :: suffix → key pivot ≤ key item := by
        intro item hitem
        cases before with
        | nil =>
            simp only [List.nil_append] at hitem
            rw [List.mem_cons] at hitem
            rcases hitem with rfl | hitem
            · exact le_rfl
            · exact List.pairwise_cons.mp hsortedRightAppend.2.1 |>.1
                (key item) (List.mem_map.mpr ⟨item, hitem, rfl⟩)
        | cons head beforeRest =>
            simp only [List.map_cons, List.cons_append, List.cons.injEq]
              at hkeysEqual
            simp only [List.cons_append] at hitem
            rw [List.mem_cons] at hitem
            rcases hitem with rfl | hitem
            · exact hkeysEqual.1.le
            · have hrightCons :
                  (key head :: (beforeRest ++ pivot :: suffix).map key).Pairwise
                    (· ≤ ·) := by
                simpa only [List.sortedLE_iff_pairwise, List.map_cons] using
                  hsortedRight
              rw [List.pairwise_cons] at hrightCons
              exact hkeysEqual.1.le.trans
                (hrightCons.1 (key item)
                  (List.mem_map.mpr ⟨item, hitem, rfl⟩))
      have hbeforeKeys : ∀ item, item ∈ before →
          key item = key pivot := by
        intro item hitem
        apply le_antisymm
        · exact hsortedRightAppend.2.2 (key item)
            (List.mem_map.mpr ⟨item, hitem, rfl⟩) (key pivot) (by simp)
        · exact hlower item (by simp [hitem])
      have hwellRight :
          (before ++ pivot :: suffix).Forall
            RegionShapeSummary.WellFormed := by
        rw [List.forall_iff_forall_mem]
        intro summary hsummary
        exact List.forall_iff_forall_mem.mp
          (by rw [List.forall_cons]; exact hwellFormed) summary
          (hperm.mem_iff.mpr hsummary)
      rw [List.forall_append, List.forall_cons] at hwellRight
      have hbubble := slotSummaryEndFromWith_bubble pivot before suffix tail
        hwellRight.1 hwellFormed.1 (by
          intro item hitem
          have hpair := hties pivot (by simp) item
            (hperm.mem_iff.mpr (by simp [hitem]))
            (hbeforeKeys item hitem).symm
          rcases hpair with heq | hdisjoint
          · exact Or.inl heq.symm
          · exact Or.inr hdisjoint.symm)
        initial allocations hvalid hwellRight.2.2 hwellTail
      have htailPerm : rest.Perm (before ++ suffix) := by
        apply List.Perm.cons_inv
        exact hperm.trans (perm_bubble pivot before suffix)
      have htailSorted : ((before ++ suffix).map key).SortedLE := by
        rw [List.sortedLE_iff_pairwise, List.map_append,
          List.pairwise_append]
        exact ⟨hsortedRightAppend.1,
          (List.pairwise_cons.mp hsortedRightAppend.2.1).2, by
            intro leftKey hleftKey rightKey hrightKey
            exact hsortedRightAppend.2.2 leftKey hleftKey rightKey
              (by simp [hrightKey])⟩
      generalize hplaced : placeSummary pivot allocations = placed
      rcases placed with ⟨row, updated⟩
      have hupdatedValid : updated.Valid := by
        have hresult := placeSummary_valid pivot allocations hvalid
          hwellFormed.1
        rw [hplaced] at hresult
        exact hresult
      have hrest := inductionHypothesis htailPerm (by
          rw [List.sortedLE_iff_pairwise]
          exact hsortedLeftCons.2)
        htailSorted hwellFormed.2 (by
          intro first hfirst second hsecond hkey
          exact hties first (by simp [hfirst]) second (by simp [hsecond]) hkey)
        (max initial (row.getD 0 + pivot.rowCount)) updated
        hupdatedValid tail hwellTail
      have hconsRest :
          slotSummaryEndFromWith initial
              ((pivot :: rest) ++ tail) allocations =
            slotSummaryEndFromWith initial
              ((pivot :: before ++ suffix) ++ tail) allocations := by
        simpa only [List.cons_append, slotSummaryEndFromWith_cons,
          hplaced] using hrest
      exact hconsRest.trans hbubble.symm

/-- The common special case where tied summaries are definitionally the same or
column-disjoint. -/
theorem slotSummaryEndFromWith_eq_of_sorted_perm
    {K : Type} [LinearOrder K] (key : RegionShapeSummary → K)
    {left right : List RegionShapeSummary}
    (hperm : left.Perm right)
    (hsortedLeft : (left.map key).SortedLE)
    (hsortedRight : (right.map key).SortedLE)
    (hwellFormed : left.Forall RegionShapeSummary.WellFormed)
    (hties : ∀ first, first ∈ left → ∀ second, second ∈ left →
      key first = key second →
        first = second ∨ List.Disjoint first.columns second.columns)
    (initial : ℕ) (allocations : CircuitAllocations)
    (hvalid : allocations.Valid) (tail : List RegionShapeSummary)
    (hwellTail : tail.Forall RegionShapeSummary.WellFormed) :
    slotSummaryEndFromWith initial (left ++ tail) allocations =
      slotSummaryEndFromWith initial (right ++ tail) allocations := by
  exact slotSummaryEndFromWith_eq_of_sorted_perm_interchangeable key hperm
    hsortedLeft hsortedRight hwellFormed (by
      intro first hfirst second hsecond hkey
      rcases hties first hfirst second hsecond hkey with rfl | hdisjoint
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr hdisjoint)
    initial allocations hvalid tail hwellTail

/-- Forgetting shape indices changes no slotted endpoint, for any pair sequence. -/
theorem slottedEndFrom_forgetIndices_eq
    (shapes : List RegionShape) (pairs : List (ℕ × ℕ)) :
    slottedEndFrom shapes pairs =
      slottedSummaryEndFrom (shapes.map RegionShape.toSummary)
        (pairs.map (·.2)) := by
  unfold slottedEndFrom placedShapes slottedSummaryEndFrom
  apply congrArg (List.foldl max 0)
  induction shapes generalizing pairs with
  | nil => rfl
  | cons shape rest inductionHypothesis =>
      cases pairs with
      | nil => rfl
      | cons pair pairs =>
          simp only [List.map_cons, List.zip_cons_cons,
            RegionShape.toSummary]
          rw [inductionHypothesis]

/-- The exact endpoint of slotting can be computed entirely in the reduced,
index-free summary language. -/
theorem slottedEndFrom_eq_slottedSummaryEndFrom
    (shapes : List RegionShape) (allocations : CircuitAllocations) :
    slottedEndFrom shapes (slotInFrom shapes allocations).1 =
      slottedSummaryEndFrom (shapes.map RegionShape.toSummary)
        (slotShapeSummariesFrom
          (shapes.map RegionShape.toSummary) allocations).1 := by
  rw [slottedEndFrom_forgetIndices_eq]
  have hslot := slotInFrom_forgetIndices shapes allocations
  have hstarts :
      (slotInFrom shapes allocations).1.map (·.2) =
        (slotShapeSummariesFrom
          (shapes.map RegionShape.toSummary) allocations).1 := by
    simpa using congrArg Prod.fst hslot
  rw [hstarts]

/-- Indexing a summary sequence changes no slotted endpoint, for any returned
pair sequence. -/
theorem slottedEndFrom_indexRegionSummaries_eq
    (initial : ℕ) (summaries : List RegionShapeSummary)
    (pairs : List (ℕ × ℕ)) :
    slottedEndFrom (indexRegionSummaries initial summaries) pairs =
      slottedSummaryEndFrom summaries (pairs.map (·.2)) := by
  unfold slottedEndFrom placedShapes slottedSummaryEndFrom
  apply congrArg (List.foldl max 0)
  induction summaries generalizing initial pairs with
  | nil => rfl
  | cons summary rest inductionHypothesis =>
      cases pairs with
      | nil => rfl
      | cons pair pairs =>
          simp only [indexRegionSummaries, List.map_cons,
            List.zip_cons_cons, measureRegionSummary]
          rw [inductionHypothesis]

/-- Region indices are irrelevant to the endpoint of an actual slotted summary
sequence. -/
theorem slottedEndFrom_indexRegionSummaries
    (initial : ℕ) (summaries : List RegionShapeSummary)
    (allocations : CircuitAllocations) :
    slottedEndFrom (indexRegionSummaries initial summaries)
        (slotInFrom (indexRegionSummaries initial summaries) allocations).1 =
      slottedSummaryEndFrom summaries
        (slotShapeSummariesFrom summaries allocations).1 := by
  rw [slottedEndFrom_indexRegionSummaries_eq]
  have hslot := slotInFrom_indexRegionSummaries
    initial summaries allocations
  have hstarts :
      (slotInFrom (indexRegionSummaries initial summaries) allocations).1.map
          (·.2) =
        (slotShapeSummariesFrom summaries allocations).1 := by
    simpa using congrArg Prod.fst hslot
  rw [hstarts]

private theorem placedShapeEnds_eq
    (allPairs : List (ℕ × ℕ)) (shapes : List RegionShape)
    (starts : List ℕ)
    (hindices : allPairs.map (·.1) = shapes.map RegionShape.index)
    (hstarts : ∀ pair ∈ allPairs,
      starts.getD pair.1 0 = pair.2) :
    (placedShapes shapes allPairs).map (fun placed =>
      placed.2 + placed.1.rowCount) =
      shapes.map (fun shape =>
        starts.getD shape.index 0 + shape.rowCount) := by
  induction shapes generalizing allPairs with
  | nil => rfl
  | cons shape rest inductionHypothesis =>
      cases allPairs with
      | nil => simp at hindices
      | cons pair pairs =>
          simp only [List.map_cons, List.cons.injEq] at hindices
          simp only [placedShapes, List.map_cons, List.zip_cons_cons]
          rw [← hstarts pair (by simp), hindices.1]
          congr 1
          exact inductionHypothesis
            pairs hindices.2
            (by
              intro candidate hcandidate
              exact hstarts candidate (by simp [hcandidate]))

/-- `placementEndFrom` can be evaluated directly in the planner's slotting order.
The final index-restoration sort is irrelevant to the endpoint. -/
theorem placementEndFrom_planCandidate_eq_slottedEndFrom
    (shapes : List RegionShape)
    (hindices : shapes.map RegionShape.index = List.range shapes.length) :
    placementEndFrom shapes (planCandidate shapes).1 =
      let sortedDesc :=
        (Pdqsort.quicksort shapes.toArray
          (fun left right => left.key < right.key)).reverse.toList
      slottedEndFrom sortedDesc (slotIn sortedDesc).1 := by
  let sortedDesc :=
    (Pdqsort.quicksort shapes.toArray
      (fun left right => left.key < right.key)).reverse.toList
  let pairs := (slotIn sortedDesc).1
  let starts := (sortPairsByIndex pairs).map (·.2)
  have hsorted : sortedDesc.Perm shapes := by
    have hquick := Pdqsort.quicksort_perm shapes.toArray
      (fun left right => left.key < right.key)
    exact (by
      simpa [sortedDesc] using
        (List.reverse_perm
          (Pdqsort.quicksort shapes.toArray
            (fun left right => left.key < right.key)).toList).trans hquick)
  have hpairsIndices : pairs.map (·.1) =
      sortedDesc.map RegionShape.index := by
    exact slotIn_indices sortedDesc
  have hpairsRange : (pairs.map (·.1)).Perm
      (List.range shapes.length) := by
    rw [hpairsIndices]
    simpa only [hindices] using hsorted.map RegionShape.index
  have hsortedIndices :
      (sortPairsByIndex pairs).map (·.1) =
        List.range shapes.length :=
    sortPairsByIndex_fst_eq_range pairs shapes.length hpairsRange
  have hstarts : ∀ pair ∈ pairs,
      starts.getD pair.1 0 = pair.2 := by
    intro pair hpair
    exact starts_getD_of_pair_mem pairs shapes.length
      hsortedIndices hpair
  have hends := placedShapeEnds_eq
    pairs sortedDesc starts hpairsIndices hstarts
  have hpermEnds := hsorted.map (fun shape =>
    starts.getD shape.index 0 + shape.rowCount)
  change
    (shapes.map (fun shape =>
      starts.getD shape.index 0 + shape.rowCount)).foldl max 0 = _
  rw [← hpermEnds.foldl_eq 0, ← hends]
  rfl

theorem shape_end_le_placementEndFrom_of_mem
    (shapes : List RegionShape) (regionStarts : List ℕ)
    (shape : RegionShape) (hshape : shape ∈ shapes) :
    regionStarts.getD shape.index 0 + shape.rowCount ≤
      placementEndFrom shapes regionStarts := by
  exact value_le_foldl_max_of_mem
    (shapes.map fun current =>
      regionStarts.getD current.index 0 + current.rowCount)
    id 0
    (regionStarts.getD shape.index 0 + shape.rowCount)
    (List.mem_map.mpr ⟨shape, hshape, rfl⟩)

/-- Rows occupied in one column, as a finite set of placed half-open intervals. -/
def occupiedRowsIn (shapes : List RegionShape) (regionStarts : List ℕ)
    (column : RegionColumn) : Finset ℕ :=
  shapes.foldr (fun shape occupied =>
    if column ∈ shape.columns then
      Finset.Ico (regionStarts.getD shape.index 0)
          (regionStarts.getD shape.index 0 + shape.rowCount) ∪ occupied
    else occupied) ∅

theorem occupiedRowsIn_nil
    (regionStarts : List ℕ) (column : RegionColumn) :
    occupiedRowsIn [] regionStarts column = ∅ := rfl

theorem occupiedRowsIn_cons
    (shape : RegionShape) (rest : List RegionShape)
    (regionStarts : List ℕ) (column : RegionColumn) :
    occupiedRowsIn (shape :: rest) regionStarts column =
      if column ∈ shape.columns then
        Finset.Ico (regionStarts.getD shape.index 0)
            (regionStarts.getD shape.index 0 + shape.rowCount) ∪
          occupiedRowsIn rest regionStarts column
      else occupiedRowsIn rest regionStarts column := rfl

theorem mem_occupiedRowsIn_iff
    (shapes : List RegionShape) (regionStarts : List ℕ)
    (column : RegionColumn) (row : ℕ) :
    row ∈ occupiedRowsIn shapes regionStarts column ↔
      ∃ shape ∈ shapes,
        column ∈ shape.columns ∧
          regionStarts.getD shape.index 0 ≤ row ∧
          row < regionStarts.getD shape.index 0 + shape.rowCount := by
  induction shapes with
  | nil => simp [occupiedRowsIn_nil]
  | cons shape rest inductionHypothesis =>
      by_cases hcolumn : column ∈ shape.columns
      · simp only [occupiedRowsIn_cons, hcolumn, ↓reduceIte,
          Finset.mem_union, Finset.mem_Ico, inductionHypothesis,
          List.mem_cons, exists_eq_or_imp, true_and]
      · simp only [occupiedRowsIn_cons, hcolumn, ↓reduceIte,
          inductionHypothesis, List.mem_cons, exists_eq_or_imp,
          false_and, false_or]

theorem occupiedRowsIn_card_le_columnOccupiedLength
    (shapes : List RegionShape) (regionStarts : List ℕ)
    (column : RegionColumn) :
    (occupiedRowsIn shapes regionStarts column).card ≤
      columnOccupiedLength shapes column := by
  induction shapes with
  | nil => simp [occupiedRowsIn, columnOccupiedLength]
  | cons shape rest inductionHypothesis =>
      by_cases hcolumn : column ∈ shape.columns
      · simp only [occupiedRowsIn_cons, hcolumn, ↓reduceIte,
          columnOccupiedLength_cons]
        apply (Finset.card_union_le _ _).trans
        have hinterval :
            (Finset.Ico (regionStarts.getD shape.index 0)
              (regionStarts.getD shape.index 0 + shape.rowCount)).card =
              shape.rowCount := by
          rw [Nat.card_Ico]
          omega
        exact Nat.add_le_add (Nat.le_of_eq hinterval) (by
          exact inductionHypothesis)
      · simpa only [occupiedRowsIn_cons, hcolumn, ↓reduceIte,
          columnOccupiedLength_cons, zero_add] using
          inductionHypothesis

theorem occupiedRowsIn_card_eq_columnOccupiedLength
    (shapes : List RegionShape) (regionStarts : List ℕ)
    (column : RegionColumn)
    (hindices : (shapes.map (·.index)).Nodup)
    (hdisjoint : SharedColumnIntervalsDisjoint shapes regionStarts) :
    (occupiedRowsIn shapes regionStarts column).card =
      columnOccupiedLength shapes column := by
  induction shapes with
  | nil => simp only [occupiedRowsIn_nil, Finset.card_empty,
      columnOccupiedLength_nil]
  | cons shape rest inductionHypothesis =>
      rw [List.map_cons, List.nodup_cons] at hindices
      have hrestDisjoint : SharedColumnIntervalsDisjoint rest regionStarts := by
        intro left right hleft hright hne currentColumn
          hleftColumn hrightColumn
        exact hdisjoint (by simp [hleft]) (by simp [hright]) hne
          hleftColumn hrightColumn
      have hrestCard := inductionHypothesis hindices.2 hrestDisjoint
      by_cases hcolumn : column ∈ shape.columns
      · have hintervals : Disjoint
            (Finset.Ico (regionStarts.getD shape.index 0)
              (regionStarts.getD shape.index 0 + shape.rowCount))
            (occupiedRowsIn rest regionStarts column) := by
          rw [Finset.disjoint_left]
          intro row hshapeRow hrestRow
          rw [Finset.mem_Ico] at hshapeRow
          obtain ⟨other, hother, hotherColumn, hotherRow⟩ :=
            (mem_occupiedRowsIn_iff rest regionStarts column row).mp hrestRow
          have hindex : shape.index ≠ other.index := by
            intro hequal
            apply hindices.1
            exact List.mem_map.mpr ⟨other, hother, hequal.symm⟩
          have hplaced := hdisjoint (by simp) (by simp [hother]) hindex
            hcolumn hotherColumn
          unfold RowIntervalsDisjoint at hplaced
          omega
        simp only [occupiedRowsIn_cons, hcolumn, ↓reduceIte,
          columnOccupiedLength_cons]
        rw [Finset.card_union_of_disjoint hintervals, Nat.card_Ico,
          hrestCard]
        omega
      · simpa only [occupiedRowsIn_cons, hcolumn, ↓reduceIte,
          columnOccupiedLength_cons, zero_add] using hrestCard

theorem columnOccupiedLength_le_placementEndFrom
    (shapes : List RegionShape) (regionStarts : List ℕ)
    (column : RegionColumn)
    (hindices : (shapes.map (·.index)).Nodup)
    (hdisjoint : SharedColumnIntervalsDisjoint shapes regionStarts) :
    columnOccupiedLength shapes column ≤
      placementEndFrom shapes regionStarts := by
  rw [← occupiedRowsIn_card_eq_columnOccupiedLength
    shapes regionStarts column hindices hdisjoint]
  have hsubset : occupiedRowsIn shapes regionStarts column ⊆
      Finset.range (placementEndFrom shapes regionStarts) := by
    intro row hrow
    rw [Finset.mem_range]
    obtain ⟨shape, hshape, hcolumn, hbounds⟩ :=
      (mem_occupiedRowsIn_iff shapes regionStarts column row).mp hrow
    exact hbounds.2.trans_le
      (shape_end_le_placementEndFrom_of_mem
        shapes regionStarts shape hshape)
  simpa using Finset.card_le_card hsubset

/-- One past the last row occupied by any placed region.  This is Halo 2 V1's
`first_unassigned_row`, stated directly from the final placement rather than through
the planner's internal per-column allocation map. -/
def placementEnd (ops : Operations F) : ℕ :=
  placementEndFrom (measureRegions ops) (starts ops)

/-- The exact index-free summary order consumed by V1 after its legacy pdqsort. -/
def sortedSummaryOrder (ops : Operations F) : List RegionShapeSummary :=
  let shapes := measureRegions ops
  (Pdqsort.quicksort shapes.toArray
    (fun left right => left.key < right.key)).reverse.toList.map
      RegionShape.toSummary

theorem sortedSummaryOrder_perm_synthesisSummary (ops : Operations F) :
    (sortedSummaryOrder ops).Perm
      (synthesisSummary ops).regionShapes := by
  let shapes := measureRegions ops
  let sorted :=
    (Pdqsort.quicksort shapes.toArray
      (fun left right => left.key < right.key)).toList
  have hquick : sorted.Perm shapes := by
    exact Pdqsort.quicksort_perm shapes.toArray
      (fun left right => left.key < right.key)
  have hsorted : sorted.reverse.Perm shapes :=
    (List.reverse_perm sorted).trans hquick
  have hsummaries := hsorted.map RegionShape.toSummary
  have hforget :
      (measureRegions ops).map RegionShape.toSummary =
        (synthesisSummary ops).regionShapes := by
    rw [measureRegions_eq_synthesisSummary_regionShapes,
      indexRegionSummaries_toSummary]
  rw [← hforget]
  simpa only [sortedSummaryOrder, shapes, sorted,
    Array.toList_reverse] using hsummaries

/-- V1's placement endpoint is exactly the result of running the reduced summary
planner in its consensus sort order. -/
theorem placementEnd_eq_slotSummaryEndFrom (ops : Operations F) :
    placementEnd ops =
      slotSummaryEndFrom (sortedSummaryOrder ops) ∅ := by
  unfold placementEnd starts
  rw [planOperations_eq]
  have hindices := measureRegions_indices_eq_range ops
  have hlength : (measureRegions ops).length = ops.regionCount := by
    have := congrArg List.length hindices
    simpa using this
  rw [← hlength] at hindices
  rw [placementEndFrom_planCandidate_eq_slottedEndFrom
    (measureRegions ops) hindices]
  let sortedDesc :=
    (Pdqsort.quicksort (measureRegions ops).toArray
      (fun left right => left.key < right.key)).reverse.toList
  have hsummary := slottedEndFrom_eq_slottedSummaryEndFrom
    sortedDesc (∅ : CircuitAllocations)
  simpa only [sortedSummaryOrder, sortedDesc, slotIn,
    slotSummaryEndFrom, slotSummaryEndFromWith] using hsummary

/-- When virtual selectors are anchored by physical columns, the exact V1
endpoint can be computed after erasing selectors from the consensus-sorted
summary stream. -/
theorem placementEnd_eq_slotSummaryEndFrom_withoutSelectors
    (ops : Operations F) (anchor : ℕ → RegionColumn)
    (hanchors : SelectorAnchoredBy
      (synthesisSummary ops).regionShapes anchor) :
    placementEnd ops =
      slotSummaryEndFrom
        ((sortedSummaryOrder ops).map
          RegionShapeSummary.withoutSelectors) ∅ := by
  let sorted := sortedSummaryOrder ops
  have hperm := sortedSummaryOrder_perm_synthesisSummary ops
  have hsourceWellFormed := synthesisSummary_regionShapes_wellFormed ops
  have hsortedWellFormed :
      sorted.Forall RegionShapeSummary.WellFormed := by
    rw [List.forall_iff_forall_mem]
    intro summary hsummary
    exact List.forall_iff_forall_mem.mp hsourceWellFormed summary
      (hperm.mem_iff.mp hsummary)
  have hsortedAnchors : SelectorAnchoredBy sorted anchor := by
    rw [SelectorAnchoredBy, List.forall_iff_forall_mem]
    intro summary hsummary
    exact List.forall_iff_forall_mem.mp hanchors summary
      (hperm.mem_iff.mp hsummary)
  rw [placementEnd_eq_slotSummaryEndFrom]
  have herasure := slotSummaryEndFrom_eq_withoutSelectors sorted ∅ ∅
    hsortedWellFormed CircuitAllocations.Valid.empty
    CircuitAllocations.Valid.empty
    (CircuitAllocations.PhysicalEquivalent.refl ∅)
    (SelectorAllocationsDominatedBy.empty anchor) hsortedAnchors
  simpa only [sorted, slotSummaryEndFrom, slotSummaryEndFromWith]
    using herasure

def rowOccupiedIn (shapes : List RegionShape) (regionStarts : List ℕ)
    (column : RegionColumn) (row : ℕ) : Bool :=
  match shapes with
  | [] => false
  | shape :: rest =>
      (shape.columns.contains column &&
        decide (regionStarts.getD shape.index 0 ≤ row) &&
        decide (row < regionStarts.getD shape.index 0 + shape.rowCount)) ||
      rowOccupiedIn rest regionStarts column row

theorem rowOccupiedIn_eq_true_iff_mem_occupiedRowsIn
    (shapes : List RegionShape) (regionStarts : List ℕ)
    (column : RegionColumn) (row : ℕ) :
    rowOccupiedIn shapes regionStarts column row = true ↔
      row ∈ occupiedRowsIn shapes regionStarts column := by
  induction shapes with
  | nil => simp [rowOccupiedIn, occupiedRowsIn]
  | cons shape rest inductionHypothesis =>
      by_cases hcolumn : column ∈ shape.columns
      · simp [rowOccupiedIn, occupiedRowsIn, hcolumn,
          inductionHypothesis]
      · simp [rowOccupiedIn, occupiedRowsIn, hcolumn,
          inductionHypothesis]

/-- Whether a placed region occupies `row` in `column`. -/
def rowOccupied (ops : Operations F) (column : RegionColumn) (row : ℕ) : Bool :=
  rowOccupiedIn (measureRegions ops) (starts ops) column row

def constantFreeRowsFrom (shapes : List RegionShape) (regionStarts : List ℕ)
    (endRow column : ℕ) : List ℕ :=
  (List.range endRow).filter fun row =>
    !rowOccupiedIn shapes regionStarts (.column .fixed column) row

private theorem filter_not_length_add_filter_length
    (values : List ℕ) (predicate : ℕ → Bool) :
    (values.filter fun value => !predicate value).length +
      (values.filter predicate).length = values.length := by
  induction values with
  | nil => rfl
  | cons value values inductionHypothesis =>
      cases hpredicate : predicate value <;>
        simp [hpredicate] <;> omega

theorem constantFreeRowsFrom_length_lowerBound
    (shapes : List RegionShape) (regionStarts : List ℕ)
    (endRow column : ℕ) :
    endRow - columnOccupiedLength shapes (.column .fixed column) ≤
      (constantFreeRowsFrom shapes regionStarts endRow column).length := by
  let occupied :=
    (List.range endRow).filter fun row =>
      rowOccupiedIn shapes regionStarts (.column .fixed column) row
  have hoccupiedNodup : occupied.Nodup :=
    List.Nodup.filter _ List.nodup_range
  have hsubset : occupied.toFinset ⊆
      occupiedRowsIn shapes regionStarts (.column .fixed column) := by
    intro row hrow
    rw [List.mem_toFinset, List.mem_filter] at hrow
    exact (rowOccupiedIn_eq_true_iff_mem_occupiedRowsIn
      shapes regionStarts (.column .fixed column) row).mp hrow.2
  have hoccupied : occupied.length ≤
      columnOccupiedLength shapes (.column .fixed column) := by
    rw [← List.toFinset_card_of_nodup hoccupiedNodup]
    exact (Finset.card_le_card hsubset).trans
      (occupiedRowsIn_card_le_columnOccupiedLength
        shapes regionStarts (.column .fixed column))
  have hpartition :
      (constantFreeRowsFrom shapes regionStarts endRow column).length +
        occupied.length = endRow := by
    simpa only [constantFreeRowsFrom, occupied, List.length_range] using
      filter_not_length_add_filter_length (List.range endRow)
        (fun row => rowOccupiedIn shapes regionStarts
          (.column .fixed column) row)
  omega

/-- Compositional lower bound on the total deferred-constant capacity.  The placement
end is bounded below by every column's exact occupied length; subtracting a constant
column's exact occupied length therefore counts slots guaranteed free in that column. -/
def constantCapacityLowerBound (ops : Operations F)
    (constantColumns : List ℕ) : ℕ :=
  let shapes := measureRegions ops
  let regionStarts := starts ops
  let endRow := placementEndFrom shapes regionStarts
  (constantColumns.map fun column =>
    endRow - columnOccupiedLength shapes (.column .fixed column)).sum

theorem mem_constantFreeRowsFrom_lt
    (shapes : List RegionShape) (regionStarts : List ℕ)
    (endRow column row : ℕ)
    (hrow : row ∈ constantFreeRowsFrom shapes regionStarts endRow column) :
    row < endRow := by
  rw [constantFreeRowsFrom, List.mem_filter] at hrow
  exact List.mem_range.mp hrow.1

/-- Free rows of a concrete fixed column below V1's final region end, in ascending
order.  This is the extensional content of `Allocations.free_intervals` used by Halo 2
for deferred constants. -/
def constantFreeRows (ops : Operations F) (column : ℕ) : List ℕ :=
  let shapes := measureRegions ops
  let regionStarts := starts ops
  constantFreeRowsFrom shapes regionStarts
    (placementEndFrom shapes regionStarts) column

theorem constantCapacityLowerBound_le_positions_length
    (ops : Operations F) (constantColumns : List ℕ) :
    constantCapacityLowerBound ops constantColumns ≤
      (constantColumns.flatMap fun column =>
        (constantFreeRows ops column).map fun row => (column, row)).length := by
  rw [List.length_flatMap]
  apply List.sum_le_sum
  intro column hcolumn
  simp only [List.length_map, constantFreeRows]
  exact constantFreeRowsFrom_length_lowerBound
    (measureRegions ops) (starts ops)
    (placementEndFrom (measureRegions ops) (starts ops)) column

/--
V1 placement makes regions sharing any measured column row-disjoint by construction,
independently of the legacy candidate's sorting implementation.
-/
theorem starts_sharedColumnIntervalsDisjoint
    (ops : Operations F) :
    SharedColumnIntervalsDisjoint
      (measureRegions ops) (starts ops) := by
  rw [starts, planOperations_eq]
  exact planCandidate_measureRegions_sharedColumnIntervalsDisjoint ops

/-- Every column's exact compositional occupancy fits below V1's placement end. -/
theorem columnOccupiedLength_le_placementEnd
    (ops : Operations F) (column : RegionColumn) :
    columnOccupiedLength (measureRegions ops) column ≤
      V1.placementEnd ops := by
  exact columnOccupiedLength_le_placementEndFrom
    (measureRegions ops) (V1.starts ops) column
    (measureRegions_indices_nodup ops)
    (V1.starts_sharedColumnIntervalsDisjoint ops)

theorem synthesisSummary_maxColumnOccupancy_le_placementEnd
    (ops : Operations F) :
    (synthesisSummary ops).maxColumnOccupancy ≤ V1.placementEnd ops := by
  apply SynthesisSummary.maxColumnOccupancy_le
  intro column hcolumn
  rw [synthesisSummary_columnOccupancy_eq]
  exact V1.columnOccupiedLength_le_placementEnd ops column

theorem synthesisSummary_constantCapacityLowerBound_le
    (ops : Operations F) (constantColumns : List (Column .fixed)) :
    (synthesisSummary ops).constantCapacityLowerBound constantColumns ≤
      V1.constantCapacityLowerBound ops (constantColumns.map (·.index)) := by
  unfold SynthesisSummary.constantCapacityLowerBound
  unfold V1.constantCapacityLowerBound
  simp only [List.map_map]
  apply List.sum_le_sum
  intro column hcolumn
  rw [SynthesisSummary.fixedColumnOccupancy,
    synthesisSummary_columnOccupancy_eq]
  exact Nat.sub_le_sub_right
    (synthesisSummary_maxColumnOccupancy_le_placementEnd ops)
    (columnOccupiedLength (measureRegions ops) (.column .fixed column.index))

/-- The full V1 shared-column invariant implies its virtual-selector projection. -/
theorem starts_sharedSelectorIntervalsDisjoint
    (ops : Operations F) :
    SharedSelectorIntervalsDisjoint
      (measureRegions ops) (starts ops) := by
  intro left right hleft hright hindices selector
    hleftSelector hrightSelector
  exact starts_sharedColumnIntervalsDisjoint ops
    hleft hright hindices hleftSelector hrightSelector

/-! ### Constants allocation (`v1.rs:79-136`)

After planning, V1 assigns the collected `constrain_constant` values into the constants
fixed columns: `first_unassigned_row = max column unbounded_interval_start`
(`v1.rs:83-87`); `constant_positions` enumerates, per constants column in order, the FREE
rows in `[0, first_unassigned_row)` of that column's allocations (`v1.rs:102-108`); these are
zipped with `plan.constants` — the `constrain_constant` `(value, cell)` list collected in
region-then-body order during the assignment pass (`v1.rs:122`). -/

/-- `plan.constants` values in collection order (`assign_advice_from_constant` /
`constrain_constant` push `(constant, cell)`; we keep the constant), region-index order then
body order (`v1.rs` `AssignmentPass` runs regions in order). -/
def regionConstantValues (body : RegionOperations F) : List F :=
  match body with
  | [] => []
  | .constrainConstant _ value :: rest =>
      value :: regionConstantValues rest
  | _ :: rest => regionConstantValues rest

def constantValues (ops : Operations F) : List F :=
  (indexedRegions ops 0).1.flatMap fun (_, body) =>
    regionConstantValues body

theorem regionConstantValues_length
    (body : RegionOperations F) :
    (regionConstantValues body).length =
      (regionSynthesisSummary body).constantSiteCount := by
  induction body with
  | nil => rfl
  | cons operation rest inductionHypothesis =>
      cases operation <;>
        simp [regionConstantValues, regionSynthesisSummary,
          RegionSynthesisSummary.combine,
          RegionSynthesisSummary.ofOperation,
          regionOperationConstantSiteCount, inductionHypothesis,
          Nat.add_comm]

theorem constantValues_length
    (ops : Operations F) :
    (constantValues ops).length =
      (synthesisSummary ops).constantSiteCount := by
  have general : ∀ (operations : Operations F) (initial : ℕ),
      ((indexedRegions operations initial).1.flatMap fun (_, body) =>
        regionConstantValues body).length =
        (synthesisSummary operations).constantSiteCount := by
    intro operations
    induction operations with
    | nil => intro initial; rfl
    | cons operation rest inductionHypothesis =>
        intro initial
        cases operation with
        | region name body =>
            simp only [indexedRegions, List.flatMap_cons, List.length_append,
              synthesisSummary, SynthesisSummary.combine,
              SynthesisSummary.ofRegion, regionConstantValues_length]
            rw [inductionHypothesis]
        | constrainInstance cell column row =>
            simpa only [indexedRegions, synthesisSummary] using
              inductionHypothesis initial
        | loadTable table values =>
            simpa only [indexedRegions, synthesisSummary] using
              inductionHypothesis initial
  exact general ops 0

/-- `first_unassigned_row` (`v1.rs:83-87`): the max `unbounded_interval_start` over all
allocated columns. -/
def firstUnassignedRow (colAllocs : CircuitAllocations) : ℕ :=
  colAllocs.toList.foldl (fun m (_, a) => max m a.unboundedStart) 0

/-- Free rows of a fixed column's allocations within `[0, endRow)` (`constant_positions`'
`free_intervals(0, Some(first_unassigned_row))` expanded to individual rows). -/
def freeRows (colAllocs : CircuitAllocations) (colIdx endRow : ℕ) : List ℕ :=
  (colAllocs.getD (.column .fixed colIdx) #[]).freeIntervals 0 (some endRow)
    |>.flatMap fun (s, e?) => match e? with
      | some e => (List.range (e - s)).map (· + s)
      | none => []

/-- Every bounded constant-allocation position lies below its requested end row. -/
theorem mem_freeRows_lt
    (colAllocs : CircuitAllocations) (colIdx endRow row : ℕ)
    (hrow : row ∈ freeRows colAllocs colIdx endRow) :
    row < endRow := by
  rw [freeRows, List.mem_flatMap] at hrow
  obtain ⟨⟨intervalStart, intervalEnd⟩, hinterval, hrow⟩ := hrow
  cases intervalEnd with
  | none => simp at hrow
  | some intervalEnd =>
      rw [List.mem_map] at hrow
      obtain ⟨offset, hoffset, rfl⟩ := hrow
      have hoffsetBound := List.mem_range.mp hoffset
      have hintervalBound :=
        Allocations.freeIntervals_end_le
          (colAllocs.getD (.column .fixed colIdx) #[])
          0 endRow hinterval
      omega

/--
The V1 constants allocation `(value, constantsColIdx, row)`, retaining field values.

`constCols` is the list of constants fixed-column indices (`cs.constants`, from
`enable_constant`; Orchard uses a single column). This is the semantic compiler view:
field values stay in the field instead of making a round trip through a backend-specific
natural-number encoding.
-/
def constantAssignments (ops : Operations F) (constCols : List ℕ) :
    List (F × ℕ × ℕ) :=
  let shapes := measureRegions ops
  let regionStarts := starts ops
  let endRow := placementEndFrom shapes regionStarts
  let positions : List (ℕ × ℕ) := constCols.flatMap fun c =>
    (constantFreeRowsFrom shapes regionStarts endRow c).map fun row => (c, row)
  (positions.zip (constantValues ops)).map fun ((c, row), v) => (v, c, row)

/-- The compositional capacity law is sufficient for V1 to allocate every deferred
constant site; `zip` therefore does not truncate the constant-value stream. -/
theorem constantValues_length_le_constantAssignments_length
    (ops : Operations F) (constantColumns : List ℕ)
    (hcapacity :
      (constantValues ops).length ≤
        constantCapacityLowerBound ops constantColumns) :
    (constantValues ops).length ≤
      (constantAssignments ops constantColumns).length := by
  let shapes := measureRegions ops
  let regionStarts := starts ops
  let endRow := placementEndFrom shapes regionStarts
  let positions : List (ℕ × ℕ) := constantColumns.flatMap fun column =>
    (constantFreeRowsFrom shapes regionStarts endRow column).map fun row =>
      (column, row)
  have hlower : constantCapacityLowerBound ops constantColumns ≤
      positions.length := by
    dsimp only [positions]
    rw [List.length_flatMap]
    apply List.sum_le_sum
    intro column hcolumn
    simp only [List.length_map]
    exact constantFreeRowsFrom_length_lowerBound
      shapes regionStarts endRow column
  have hpositions : (constantValues ops).length ≤ positions.length :=
    hcapacity.trans hlower
  have hlength :
      (constantAssignments ops constantColumns).length =
        min positions.length (constantValues ops).length := by
    simp [constantAssignments, positions, shapes, regionStarts, endRow]
  rw [hlength]
  omega

/-- A complete V1 allocation preserves the constant-value stream in order. -/
theorem constantAssignments_map_fst
    (ops : Operations F) (constantColumns : List ℕ)
    (hfull :
      (constantValues ops).length ≤
        (constantAssignments ops constantColumns).length) :
    (constantAssignments ops constantColumns).map Prod.fst =
      constantValues ops := by
  let shapes := measureRegions ops
  let regionStarts := starts ops
  let endRow := placementEndFrom shapes regionStarts
  let positions : List (ℕ × ℕ) := constantColumns.flatMap fun column =>
    (constantFreeRowsFrom shapes regionStarts endRow column).map fun row =>
      (column, row)
  have hpositions : (constantValues ops).length ≤ positions.length := by
    have hlength :
        (constantValues ops).length ≤
          min positions.length (constantValues ops).length := by
      simpa only [constantAssignments, positions, shapes, regionStarts,
        endRow, List.length_map, List.length_zip] using hfull
    omega
  simp only [constantAssignments, List.map_map]
  simpa only [Function.comp_apply] using
    List.map_snd_zip hpositions

/-- Every V1 constant allocation uses one of the configured constants columns. -/
theorem constantAssignments_column_mem
    (ops : Operations F) (constCols : List ℕ)
    {value : F} {column row : ℕ}
    (hassignment :
      (value, column, row) ∈ constantAssignments ops constCols) :
    column ∈ constCols := by
  let positions : List (ℕ × ℕ) := constCols.flatMap fun currentColumn =>
    (constantFreeRows ops currentColumn).map fun currentRow =>
      (currentColumn, currentRow)
  rw [constantAssignments, List.mem_map] at hassignment
  obtain ⟨⟨⟨foundColumn, foundRow⟩, foundValue⟩,
    hzipped, hequal⟩ := hassignment
  have hposition : (foundColumn, foundRow) ∈ positions :=
    (List.of_mem_zip hzipped).1
  dsimp only [positions] at hposition
  rw [List.mem_flatMap] at hposition
  obtain ⟨currentColumn, hcolumn, hposition⟩ := hposition
  rw [List.mem_map] at hposition
  obtain ⟨currentRow, _, hposition⟩ := hposition
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hposition
  obtain ⟨rfl, rfl, rfl⟩ := hequal
  exact hcolumn

/-- Every V1 constant allocation lies below the final placed-region end. -/
theorem constantAssignments_row_lt_placementEnd
    (ops : Operations F) (constCols : List ℕ)
    {value : F} {column row : ℕ}
    (hassignment :
      (value, column, row) ∈ constantAssignments ops constCols) :
    row < placementEnd ops := by
  let positions : List (ℕ × ℕ) := constCols.flatMap fun currentColumn =>
    (constantFreeRows ops currentColumn).map fun currentRow =>
      (currentColumn, currentRow)
  rw [constantAssignments, List.mem_map] at hassignment
  obtain ⟨⟨⟨foundColumn, foundRow⟩, foundValue⟩,
    hzipped, hequal⟩ := hassignment
  have hposition : (foundColumn, foundRow) ∈ positions :=
    (List.of_mem_zip hzipped).1
  have hrow : foundRow < placementEnd ops := by
    dsimp only [positions] at hposition
    rw [List.mem_flatMap] at hposition
    obtain ⟨currentColumn, hcolumn, hposition⟩ := hposition
    rw [List.mem_map] at hposition
    obtain ⟨currentRow, hcurrentRow, hposition⟩ := hposition
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hposition
    exact mem_constantFreeRowsFrom_lt
      (measureRegions ops) (starts ops)
      (placementEndFrom (measureRegions ops) (starts ops))
      currentColumn currentRow hcurrentRow
  obtain ⟨rfl, rfl, rfl⟩ := hequal
  exact hrow

end V1

namespace SimpleFloorPlanner

/-- `SingleChipLayouter::assign_region` placement (`single_pass.rs:86-106`): for each region
in stream order, `region_start = max` over the region's columns of that column's first-empty
row, then bump each column's first-empty row to `region_start + row_count`. Returns starts per
`assignRegion` index. -/
def starts (ops : Operations F) : List ℕ := Id.run do
  let mut cols : Std.HashMap RegionColumn ℕ := ∅
  let mut out : List ℕ := []
  for (idx, body) in (indexedRegions ops 0).1 do
    let shape := measureRegion idx body
    let mut rstart := 0
    for c in shape.columns do rstart := max rstart (cols.getD c 0)
    out := out ++ [rstart]
    for c in shape.columns do cols := cols.insert c (rstart + shape.rowCount)
  return out

end SimpleFloorPlanner

end Halo2.FloorPlanner
