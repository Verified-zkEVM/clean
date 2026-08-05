import Clean.Halo2.Operations
import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.List.TakeDrop

/-!
# Floor planner: deriving region placements from the operation stream

Computes `starts : List ℕ` — the start row per `assignRegion`-index region — purely from
the Halo2-Clean `Operations`, by porting halo2's floor planners. This is the region
placement input to the keygen-view activation table and to the domain-size derivation.

Two planners, matching the Rust module split (`halo2_proofs/src/circuit/floor_planner`):

* **`V1`** (`v1.rs`, `v1/strategy.rs`) — the planner the real orchard `Circuit` declares
  (`orchard/src/circuit.rs`, `type FloorPlanner = V1`, with the
  `floor-planner-v1-legacy-pdqsort` feature — see `V1.planFull`). A dual pass:
  a measurement pass computes each region's shape (`measureRegions`/`RegionShape`), then
  a greedy first-fit places the regions biggest-advice-area first
  (`slot_in_biggest_advice_first` + `slot_in` + `first_fit_region`). Drives the Action
  fixtures.
* **`SimpleFloorPlanner`** (`single_pass.rs`) — sequential per-region placement at the
  earliest row where none of the region's columns are in use. Drives the Add/Mul fixtures.

Everything is `#eval`-computable. V1 retains the exact candidate placement when a
small finite selector-interval guard accepts it, and otherwise uses a conservative
globally row-disjoint plan. Tests can `#guard`/`#eval` the derived starts against
fixture placements.

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
  (cols.toArray.qsort RegionColumn.lt).toList

/-! ## Measurement pass (`v1.rs` `MeasurementPass` / `layouter.rs` `RegionShape`) -/

/-- The shape of a region: its region index, the SET of columns it touches, and its row
count. Rust `RegionShape` (`layouter.rs:117-122`). -/
structure RegionShape where
  index : ℕ
  columns : List RegionColumn
  rowCount : ℕ
deriving Repr, Inhabited

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
    columns := summary.columns.foldl addCol []
    rowCount := summary.rowCount }

theorem mem_measureRegion_columns_iff
    (index : ℕ) (body : RegionOperations F) (column : RegionColumn) :
    column ∈ (measureRegion index body).columns ↔
      column ∈ (regionSynthesisSummary body).columns := by
  simp only [measureRegion]
  rw [show addCol = addColumn by rfl, mem_foldl_addColumn_iff]
  simp

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

/-- Swap two array entries by index (`slice::swap`). -/
@[inline] def swp (a : Array T) (i j : ℕ) : Array T :=
  let x := a[i]!
  let y := a[j]!
  (a.set! i y).set! j x

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
    let left := fun i => l + leftData.2.2[i]!
    let right := fun i => r - rightData.2.2[i]! - 1
    let tmp := a[left leftData.1]!
    let afterFirst := a.set! (left leftData.1)
      a[right rightData.1]!
    let result : ℕ × ℕ × Array T := Id.run <|
      forIn (List.range' 0 (count - 1))
        (leftData.1, rightData.1, afterFirst) fun _ state =>
          let startL' := state.1 + 1
          let afterLeft := state.2.2.set! (right state.2.1)
            state.2.2[left startL']!
          let startR' := state.2.1 + 1
          let afterRight := afterLeft.set! (left startL')
            afterLeft[right startR']!
          pure (.yield (startL', startR', afterRight))
    result.2.2.set! (right result.2.1) tmp
  else
    a

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

private theorem blockLoopStep_yield_pre
    (original : Array T) (pivot : T)
    (isLess : T → T → Bool)
    (state result : BlockLoopState T)
    (hinv : BlockPreInv original state)
    (hstep : blockLoopStep pivot isLess state = .yield result) :
    BlockPreInv original result := by
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
  have hcoreSize : core.v.size = original.size := by
    simpa using hcorePerm.length_eq
  have hcoreASize : core.v.size = a.size := by omega
  have hatMostOneCore :
      ¬(core.startL < core.endL ∧
        core.startR < core.endR) := by
    intro hpending
    rcases hcExhaust with hdoneL | hdoneR <;> omega
  exact blockPreInv_coreState original core hcorePerm hcoreSize
    hcursorRaw.1 (hcursorRaw.2.trans_eq hcoreASize.symm)
    hcSizeL hcSizeR hcStartL hcEndL hcStartR hcEndR
    hcActiveL hcActiveR hatMostOneCore
    hpendingGap.1 hpendingGap.2

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
      state result hinv hstep
  · intro _ state result hinv hstep
    have hout := blockLoopStep_cleanup v pivot isLess state hinv
    rw [hstep] at hout
    exact hout
  · exact blockPreInv_cleanup v
  · show BlockPreInv v initial
    simp [BlockPreInv, initial]

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

end Pdqsort

/-! ## Column allocations (`v1/strategy.rs` `Allocations` / `CircuitAllocations`)

Per-column set of disjoint `[start, start+length)` allocated intervals, kept sorted by
`start` (Rust `BTreeSet<AllocatedRegion>` ordered by `start`). -/

/-- A column's allocated intervals `(start, length)`, sorted by `start`, disjoint. -/
abbrev Allocations := Array (ℕ × ℕ)

/-- Insert an allocated interval keeping the sort by `start` (`BTreeSet::insert`). -/
def Allocations.insert (a : Allocations) (start len : ℕ) : Allocations :=
  let rec go : List (ℕ × ℕ) → List (ℕ × ℕ)
    | [] => [(start, len)]
    | (s, l) :: rest => if start < s then (start, len) :: (s, l) :: rest else (s, l) :: go rest
  (go a.toList).toArray

/-- `unbounded_interval_start` (`strategy.rs:53-59`): the row after the last allocated
interval, or 0. -/
def Allocations.unboundedStart (a : Allocations) : ℕ :=
  match a.toList.getLast? with
  | some (s, l) => s + l
  | none => 0

/-- One step of `free_intervals`, exposed separately so its elementary range
invariants do not depend on unfolding the imperative loop. -/
private def Allocations.freeIntervalsNext (endBound : Option ℕ)
    (state : MProd (Array (ℕ × Option ℕ)) ℕ) (interval : ℕ × ℕ) :
    MProd (Array (ℕ × Option ℕ)) ℕ :=
  let (regionStart, regionLength) := interval
  let output := state.fst
  let row := state.snd
  let past : Bool := match endBound with
    | some endRow => decide (regionStart ≥ endRow)
    | none => false
  if !past then
    let output :=
      if row < regionStart then output.push (row, some regionStart)
      else output
    ⟨output, max row (regionStart + regionLength)⟩
  else
    state

/-- `free_intervals(start, end)` (`strategy.rs:64-98`): the unallocated intervals of this
column intersecting `[start, end)`, as `(spaceStart, spaceEnd?)` (`end? = none` unbounded).
Verbatim port of the `scan`: a region with `start ≥ end` is skipped without advancing `row`,
and the final unbounded item emits `[row, end)` when `end = none ∨ row < end`. -/
def Allocations.freeIntervals (a : Allocations) (start : ℕ) (endBound : Option ℕ) :
    List (ℕ × Option ℕ) :=
  let result : MProd (Array (ℕ × Option ℕ)) ℕ := Id.run <|
    forIn a.toList ⟨#[], start⟩ fun interval state =>
      pure (.yield (Allocations.freeIntervalsNext endBound state interval))
  let output :=
    match endBound with
    | some endRow =>
        if result.snd < endRow then
          result.fst.push (result.snd, some endRow)
        else result.fst
    | none => result.fst.push (result.snd, none)
  output.toList

private theorem list_forIn_yield_invariant
    {ι S : Type} (items : List ι) (next : ι → S → S)
    (property : S → Prop) (initial : S)
    (hnext : ∀ item state, property state → property (next item state))
    (hinitial : property initial) :
    property (Id.run <|
      forIn items initial fun item state =>
        pure (.yield (next item state))) := by
  induction items generalizing initial with
  | nil => simpa using hinitial
  | cons item items inductionHypothesis =>
      rw [List.forIn_cons]
      exact inductionHypothesis _ (hnext item initial hinitial)

/-- Every bounded free interval ends within the requested upper bound. -/
theorem Allocations.freeIntervals_end_le
    (allocations : Allocations) (start endRow : ℕ)
    {intervalStart intervalEnd : ℕ}
    (hinterval :
      (intervalStart, some intervalEnd) ∈
        allocations.freeIntervals start (some endRow)) :
    intervalEnd ≤ endRow := by
  let Good := fun state : MProd (Array (ℕ × Option ℕ)) ℕ =>
    ∀ interval ∈ state.fst.toList,
      ∀ foundEnd, interval.2 = some foundEnd → foundEnd ≤ endRow
  let initial : MProd (Array (ℕ × Option ℕ)) ℕ := ⟨#[], start⟩
  let result : MProd (Array (ℕ × Option ℕ)) ℕ := Id.run <|
    forIn allocations.toList initial fun interval state =>
      pure (.yield (Allocations.freeIntervalsNext (some endRow) state interval))
  have hresult : Good result := by
    apply list_forIn_yield_invariant allocations.toList
      (fun interval state =>
        Allocations.freeIntervalsNext (some endRow) state interval)
      Good initial
    · intro interval state hstate
      rcases interval with ⟨regionStart, regionLength⟩
      simp only [Allocations.freeIntervalsNext]
      by_cases hpast : regionStart ≥ endRow
      · simp [hpast]
        exact hstate
      · simp only [hpast, decide_false, Bool.not_false]
        by_cases hgap : state.snd < regionStart
        · simp only [hgap, ↓reduceIte]
          intro found hfound foundEnd hfoundEnd
          simp at hfound
          rcases hfound with hfound | rfl
          · exact hstate found (by simpa using hfound) foundEnd hfoundEnd
          · simp only [Option.some.injEq] at hfoundEnd
            subst foundEnd
            omega
        · simp only [hgap, ↓reduceIte]
          exact hstate
    · intro interval hinterval foundEnd hfoundEnd
      simp [initial] at hinterval

  unfold Allocations.freeIntervals at hinterval
  dsimp only at hinterval
  change
    (intervalStart, some intervalEnd) ∈
      (if result.snd < endRow then
        result.fst.push (result.snd, some endRow)
      else result.fst).toList at hinterval
  by_cases hfinal : result.snd < endRow
  · simp only [hfinal, ↓reduceIte, Array.toList_push,
      List.mem_append, List.mem_singleton] at hinterval
    rcases hinterval with hprevious | hlast
    · exact hresult (intervalStart, some intervalEnd) hprevious
        intervalEnd rfl
    · exact Nat.le_of_eq (by simpa using congrArg Prod.snd hlast)
  · simp only [hfinal, ↓reduceIte] at hinterval
    exact hresult (intervalStart, some intervalEnd) hinterval
      intervalEnd rfl

/-- The circuit's per-column allocations. -/
abbrev CircuitAllocations := Std.HashMap RegionColumn Allocations

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

/-- `slot_in` (`strategy.rs:165-195`): place each shape (in the given order) at the earliest
free common row via `first_fit_region`, threading the allocations. Returns the
`(regionIndex, start)` pairs in the input order plus the final allocations. -/
def slotIn (shapes : List RegionShape) : List (ℕ × ℕ) × CircuitAllocations :=
  shapes.foldl (init := ([], ∅)) fun (acc : List (ℕ × ℕ) × CircuitAllocations) shape =>
    let (pairs, colAllocs) := acc
    let cols := sortRegionColumns shape.columns
    let (row?, colAllocs') := firstFit cols.length colAllocs cols shape.rowCount 0 none
    (pairs ++ [(shape.index, row?.getD 0)], colAllocs')

/-! ## Guarded selector placement

The legacy planner's two sorting implementations are consensus-critical computations,
but their implementations do not expose permutation proofs. Rather than make selector
cell-disjointness depend on those implementation details, V1 validates the candidate's
small list of virtual-selector intervals. A rejected candidate falls back to a
globally row-disjoint placement with matching allocation state.
-/

/-- Disjointness of two half-open row intervals. -/
def RowIntervalsDisjoint
    (leftStart leftLength rightStart rightLength : ℕ) : Prop :=
  leftStart + leftLength ≤ rightStart ∨
    rightStart + rightLength ≤ leftStart

/-- Whether two measured regions share any concrete or virtual column. -/
def columnsOverlap
    (left right : List RegionColumn) : Bool :=
  left.any fun column => right.contains column

/-- Finite safety check for every shared measured column in a candidate placement. -/
def CheckedSharedColumnIntervalsDisjoint
    (shapes : List RegionShape) (starts : List ℕ) : Prop :=
  shapes.Pairwise fun left right =>
    columnsOverlap left.columns right.columns = false ∨
      RowIntervalsDisjoint
        (starts.getD left.index 0) left.rowCount
        (starts.getD right.index 0) right.rowCount

private def checkedSharedColumnIntervalsDisjointDecidable
    (shapes : List RegionShape) (starts : List ℕ) :
    Decidable (CheckedSharedColumnIntervalsDisjoint shapes starts) := by
  unfold CheckedSharedColumnIntervalsDisjoint RowIntervalsDisjoint
  infer_instance

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

/-- Hash-set form of the placed selector activation stream, used by the V1 guard. -/
def activationSet
    (starts : List ℕ) (regions : List (ℕ × RegionOperations F)) :
    Std.HashSet (ℕ × ℕ) :=
  (activations starts regions).foldl
    (fun set activation => set.insert activation) ∅

/--
Executable guard for the exact placed selector fact lookup semantics needs. The
activation set is built once before the nested lookup-input walk.
-/
def placedLookupSelectorRowsExactCheck
    (operations : Operations F) (starts : List ℕ) : Bool :=
  let regions := (indexedRegions operations 0).1
  let active := activationSet starts regions
  regions.all fun region =>
    region.2.all fun operation =>
      match operation with
      | .enableLookup argument enabled row =>
          argument.inputs.all fun expression =>
            expression.selectorIndices.all fun selector =>
              (enabled.any fun candidate =>
                  candidate.index == selector) ==
                active.contains
                  (selector, starts.getD region.1 0 + row)
      | _ => true

/--
Every selector leaf occurring in a lookup input has the lookup operation's zero/one
enabled value at that absolute row.
-/
def PlacedLookupSelectorRowsExact
    (operations : Operations F) (starts : List ℕ) : Prop :=
  placedLookupSelectorRowsExactCheck operations starts = true

private def placedLookupSelectorRowsExactDecidable
    (operations : Operations F) (starts : List ℕ) :
    Decidable (PlacedLookupSelectorRowsExact operations starts) := by
  unfold PlacedLookupSelectorRowsExact
  infer_instance

/-- One occurrence of a virtual selector column in a placed region. -/
structure SelectorPlacement where
  selector : ℕ
  regionIndex : ℕ
  start : ℕ
  length : ℕ
deriving DecidableEq

/-- Flatten the virtual-selector part of a placed region layout. -/
def selectorPlacements
    (shapes : List RegionShape) (starts : List ℕ) :
    List SelectorPlacement :=
  shapes.flatMap fun shape =>
    shape.columns.filterMap fun
      | .selector selector =>
          some
            { selector
              regionIndex := shape.index
              start := starts.getD shape.index 0
              length := shape.rowCount }
      | .column _ _ => none

/-- Finite selector-only safety check for a candidate placement. -/
def CheckedSharedSelectorIntervalsDisjoint
    (shapes : List RegionShape) (starts : List ℕ) : Prop :=
  (selectorPlacements shapes starts).Pairwise fun left right =>
    left.selector ≠ right.selector ∨
      left.regionIndex = right.regionIndex ∨
      RowIntervalsDisjoint
        left.start left.length right.start right.length

private def checkedSharedSelectorIntervalsDisjointDecidable
    (shapes : List RegionShape) (starts : List ℕ) :
    Decidable (CheckedSharedSelectorIntervalsDisjoint shapes starts) := by
  unfold CheckedSharedSelectorIntervalsDisjoint RowIntervalsDisjoint
  infer_instance

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

/-- Acceptance of the full finite guard implies the shared-column invariant. -/
theorem sharedColumnIntervalsDisjoint_of_checked
    {shapes : List RegionShape} {starts : List ℕ}
    (hchecked :
      CheckedSharedColumnIntervalsDisjoint shapes starts) :
    SharedColumnIntervalsDisjoint shapes starts := by
  intro left right hleft hright hindices column
    hleftColumn hrightColumn
  have hne : left ≠ right := by
    intro heq
    apply hindices
    exact congrArg RegionShape.index heq
  rcases rel_or_reverse_of_pairwise_of_mem
      hchecked hleft hright hne with hforward | hreverse
  · rcases hforward with hcolumns | hintervals
    · have hnotContains :=
        List.any_eq_false.mp hcolumns column hleftColumn
      exact False.elim
        (hnotContains (List.contains_iff_mem.mpr hrightColumn))
    · exact hintervals
  · rcases hreverse with hcolumns | hintervals
    · have hnotContains :=
        List.any_eq_false.mp hcolumns column hrightColumn
      exact False.elim
        (hnotContains (List.contains_iff_mem.mpr hleftColumn))
    · exact hintervals.elim Or.inr Or.inl

private theorem selectorPlacement_mem
    {shapes : List RegionShape} {starts : List ℕ}
    {shape : RegionShape} (hshape : shape ∈ shapes)
    {selector : ℕ}
    (hselector : RegionColumn.selector selector ∈ shape.columns) :
    { selector
      regionIndex := shape.index
      start := starts.getD shape.index 0
      length := shape.rowCount : SelectorPlacement } ∈
      selectorPlacements shapes starts := by
  rw [selectorPlacements, List.mem_flatMap]
  refine ⟨shape, hshape, ?_⟩
  rw [List.mem_filterMap]
  exact ⟨.selector selector, hselector, rfl⟩

/-- Acceptance of the finite guard implies the semantic selector invariant. -/
theorem sharedSelectorIntervalsDisjoint_of_checked
    {shapes : List RegionShape} {starts : List ℕ}
    (hchecked :
      CheckedSharedSelectorIntervalsDisjoint shapes starts) :
    SharedSelectorIntervalsDisjoint shapes starts := by
  intro left right hleft hright hindices selector
    hleftSelector hrightSelector
  let leftPlacement : SelectorPlacement :=
    { selector
      regionIndex := left.index
      start := starts.getD left.index 0
      length := left.rowCount }
  let rightPlacement : SelectorPlacement :=
    { selector
      regionIndex := right.index
      start := starts.getD right.index 0
      length := right.rowCount }
  have hleftPlacement : leftPlacement ∈ selectorPlacements shapes starts :=
    selectorPlacement_mem hleft hleftSelector
  have hrightPlacement : rightPlacement ∈ selectorPlacements shapes starts :=
    selectorPlacement_mem hright hrightSelector
  have hne : leftPlacement ≠ rightPlacement := by
    intro heq
    apply hindices
    exact congrArg SelectorPlacement.regionIndex heq
  rcases rel_or_reverse_of_pairwise_of_mem hchecked
      hleftPlacement hrightPlacement hne with hforward | hreverse
  · rcases hforward with hselector | hregion | hintervals
    · exact False.elim (hselector rfl)
    · exact False.elim (hindices hregion)
    · exact hintervals
  · rcases hreverse with hselector | hregion | hintervals
    · exact False.elim (hselector rfl)
    · exact False.elim (hindices hregion.symm)
    · exact hintervals.elim Or.inr Or.inl

/-- One plus the largest region index, enough entries to address every shape. -/
def fallbackStartsLength (shapes : List RegionShape) : ℕ :=
  shapes.foldl (fun length shape => max length (shape.index + 1)) 0

/-- The largest measured region height. -/
def fallbackStride (shapes : List RegionShape) : ℕ :=
  shapes.foldl (fun stride shape => max stride shape.rowCount) 0

/--
A universally safe fallback: region `i` starts at `i * maxRowCount`, so distinct
region indices occupy globally disjoint row intervals.
-/
def globallyDisjointStarts (shapes : List RegionShape) : List ℕ :=
  (List.range (fallbackStartsLength shapes)).map
    fun index => index * fallbackStride shapes

private theorem index_lt_fallbackStartsLength_of_mem
    {shapes : List RegionShape} {shape : RegionShape}
    (hshape : shape ∈ shapes) :
    shape.index < fallbackStartsLength shapes := by
  rw [Nat.lt_iff_add_one_le]
  exact value_le_foldl_max_of_mem shapes
    (fun current => current.index + 1) 0 shape hshape

private theorem rowCount_le_fallbackStride_of_mem
    {shapes : List RegionShape} {shape : RegionShape}
    (hshape : shape ∈ shapes) :
    shape.rowCount ≤ fallbackStride shapes := by
  exact value_le_foldl_max_of_mem shapes
    RegionShape.rowCount 0 shape hshape

private theorem globallyDisjointStarts_getD
    {shapes : List RegionShape} {shape : RegionShape}
    (hshape : shape ∈ shapes) :
    (globallyDisjointStarts shapes).getD shape.index 0 =
      shape.index * fallbackStride shapes := by
  have hindex :=
    index_lt_fallbackStartsLength_of_mem hshape
  simp [globallyDisjointStarts, hindex]

/-- The conservative fallback satisfies the shared-column invariant. -/
theorem globallyDisjointStarts_sharedColumnIntervalsDisjoint
    (shapes : List RegionShape) :
    SharedColumnIntervalsDisjoint
      shapes (globallyDisjointStarts shapes) := by
  intro left right hleft hright hindices column
    hleftColumn hrightColumn
  rw [globallyDisjointStarts_getD hleft,
    globallyDisjointStarts_getD hright]
  have hleftHeight :=
    rowCount_le_fallbackStride_of_mem hleft
  have hrightHeight :=
    rowCount_le_fallbackStride_of_mem hright
  rcases Nat.lt_or_gt_of_ne hindices with hlt | hgt
  · left
    calc
      left.index * fallbackStride shapes + left.rowCount ≤
          left.index * fallbackStride shapes +
            fallbackStride shapes :=
        Nat.add_le_add_left hleftHeight _
      _ = (left.index + 1) * fallbackStride shapes := by
        rw [Nat.add_mul, one_mul]
      _ ≤ right.index * fallbackStride shapes :=
        Nat.mul_le_mul_right _ (Nat.add_one_le_iff.mpr hlt)
  · right
    calc
      right.index * fallbackStride shapes + right.rowCount ≤
          right.index * fallbackStride shapes +
            fallbackStride shapes :=
        Nat.add_le_add_left hrightHeight _
      _ = (right.index + 1) * fallbackStride shapes := by
        rw [Nat.add_mul, one_mul]
      _ ≤ left.index * fallbackStride shapes :=
        Nat.mul_le_mul_right _ (Nat.add_one_le_iff.mpr hgt)

/-- The conservative fallback also satisfies the selector-only projection. -/
theorem globallyDisjointStarts_sharedSelectorIntervalsDisjoint
    (shapes : List RegionShape) :
    SharedSelectorIntervalsDisjoint
      shapes (globallyDisjointStarts shapes) := by
  intro left right hleft hright hindices selector
    hleftSelector hrightSelector
  exact globallyDisjointStarts_sharedColumnIntervalsDisjoint shapes
    hleft hright hindices hleftSelector hrightSelector

/-- Allocation state corresponding to `globallyDisjointStarts`. -/
def globallyDisjointAllocations
    (shapes : List RegionShape) : CircuitAllocations :=
  let stride := fallbackStride shapes
  shapes.foldl (init := ∅) fun allocations shape =>
    let start := shape.index * stride
    shape.columns.foldl (init := allocations) fun current column =>
      let columnAllocations := current.getD column #[]
      current.insert column
        (columnAllocations.insert start shape.rowCount)

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
  exact mem_foldl_addCol_of_mem
    (regionSynthesisSummary body).columns [] hcolumn

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

/-! ## The two planners -/

namespace V1

/-- `slot_in_biggest_advice_first` (`strategy.rs:198-242`) then un-sort: sort the shapes by
`key` (legacy pdqsort), reverse (biggest advice area first), slot them in, and re-order the
resulting starts back to region-index order. Returns `(starts, finalAllocations)`. -/
def planCandidate (shapes : List RegionShape) : List ℕ × CircuitAllocations :=
  let sortedDesc := (Pdqsort.quicksort shapes.toArray (fun a b => a.key < b.key)).reverse
  let (pairs, colAllocs) := slotIn sortedDesc.toList
  let byIndex := pairs.toArray.qsort (fun p q => p.1 < q.1)
  ((byIndex.toList).map (·.2), colAllocs)

/--
The exact legacy V1 plan when every pair of regions sharing a measured column passes
the finite safety guard; otherwise a conservative plan whose region intervals and
allocation state agree.
-/
def planFull (shapes : List RegionShape) : List ℕ × CircuitAllocations :=
  let candidate := planCandidate shapes
  if @decide
      (CheckedSharedColumnIntervalsDisjoint shapes candidate.1)
      (checkedSharedColumnIntervalsDisjointDecidable shapes candidate.1) then
    candidate
  else
    (globallyDisjointStarts shapes, globallyDisjointAllocations shapes)

/--
Apply the semantic lookup-selector guard to the shape-safe V1 plan. A faithful
candidate is preserved exactly; a rejected candidate uses the same globally
row-disjoint starts and allocation state as the shape guard's fallback.
-/
def planOperations
    (operations : Operations F) : List ℕ × CircuitAllocations :=
  let shapes := measureRegions operations
  let candidate := planFull shapes
  if @decide
      (PlacedLookupSelectorRowsExact operations candidate.1)
      (placedLookupSelectorRowsExactDecidable operations candidate.1) then
    candidate
  else
    (globallyDisjointStarts shapes, globallyDisjointAllocations shapes)

/-- The V1 region starts, per `assignRegion` index, from the operation stream. -/
def starts (ops : Operations F) : List ℕ := (planOperations ops).1

def placementEndFrom (shapes : List RegionShape) (regionStarts : List ℕ) : ℕ :=
  shapes.map (fun shape =>
    regionStarts.getD shape.index 0 + shape.rowCount)
    |>.foldl max 0

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
  unfold starts planOperations
  dsimp only
  split
  · exact (by
      unfold planFull
      dsimp only
      split
      · rename_i hchecked
        exact sharedColumnIntervalsDisjoint_of_checked
          (@of_decide_eq_true
            (CheckedSharedColumnIntervalsDisjoint
              (measureRegions ops) (planCandidate (measureRegions ops)).1)
            (checkedSharedColumnIntervalsDisjointDecidable
              (measureRegions ops) (planCandidate (measureRegions ops)).1)
            hchecked)
      · exact globallyDisjointStarts_sharedColumnIntervalsDisjoint
          (measureRegions ops))
  · exact globallyDisjointStarts_sharedColumnIntervalsDisjoint
      (measureRegions ops)

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
