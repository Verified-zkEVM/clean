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

/-- A virtual column in a region's shape: a concrete column (kind + index) or a selector
(by index). Rust `RegionColumn`. -/
inductive RegionColumn where
  | column : ColumnKind → ℕ → RegionColumn
  | selector : ℕ → RegionColumn
deriving DecidableEq, Repr, BEq, ReflBEq, LawfulBEq

namespace RegionColumn

/-- `Any`'s consensus-critical rank: `Instance(0) < Advice(1) < Fixed(2)`
(`plonk/circuit.rs:95` "sort Instance < Advice < Fixed"). -/
def kindRank : ColumnKind → ℕ
  | .instance => 0
  | .advice => 1
  | .fixed => 2

/-- The `RegionColumn::Ord` sort key as a lexicographically-ordered triple
`(group, subrank, index)`: concrete columns are group 0 (subrank = `kindRank`), selectors
group 1 — so all columns precede all selectors (`layouter.rs:151-152`). -/
def ordKey : RegionColumn → ℕ × ℕ × ℕ
  | .column k i => (0, kindRank k, i)
  | .selector i => (1, 0, i)

/-- Hash via `ordKey` (avoids needing `Hashable ColumnKind`); consistent with `BEq`
because `ordKey` is injective on `RegionColumn`. -/
instance : Hashable RegionColumn := ⟨fun c => hash c.ordKey⟩

/-- Strict `RegionColumn::Ord` (`layouter.rs:146-155`), spelled out lexicographically on
`ordKey` (Lean's `<` on `ℕ × ℕ × ℕ` is not lexicographic). -/
def lt (a b : RegionColumn) : Bool :=
  let (a1, a2, a3) := a.ordKey
  let (b1, b2, b3) := b.ordKey
  a1 < b1 || (a1 == b1 && (a2 < b2 || (a2 == b2 && a3 < b3)))

/-- Is this a concrete advice column? Used by the V1 sort key (advice-area). -/
def isAdvice : RegionColumn → Bool
  | .column .advice _ => true
  | _ => false

end RegionColumn

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
  if cols.contains c then cols else cols ++ [c]

/-- The one-past-last row touched by a region operation. Copy-only operations touch no
new row; every semantically active gate, lookup, or assignment contributes its offset. -/
def regionOperationRowExtent : RegionOperation F → ℕ
  | .assignAdvice _ row _
  | .assignFixed _ row _
  | .enableGate _ row
  | .enableLookup _ _ row => row + 1
  | .constrainEqual _ _
  | .constrainConstant _ _
  | .constrainInstance _ _ _ => 0

/-- Add the columns touched by one operation to a region's measured column set. -/
def addOperationColumns
    (columns : List RegionColumn) (operation : RegionOperation F) :
    List RegionColumn :=
  match operation with
  | .assignAdvice column _ _ =>
      addCol columns (.column .advice column.index)
  | .assignFixed column _ _ =>
      addCol columns (.column .fixed column.index)
  | .enableGate gate _ =>
      addCol columns (.selector gate.selector.index)
  | .enableLookup _ enabled _ =>
      enabled.foldl
        (fun current selector =>
          addCol current (.selector selector.index))
        columns
  | _ => columns

/-- Measure one region body to its `RegionShape` (`layouter.rs`, `impl RegionLayouter for
RegionShape`). See the module header for the per-operation contribution. -/
def measureRegion (idx : ℕ) (body : RegionOperations F) : RegionShape :=
  { index := idx
    columns := body.foldl addOperationColumns []
    rowCount :=
      body.foldl
        (fun current operation =>
          max current (regionOperationRowExtent operation))
        0 }

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
  exact value_le_foldl_max_of_mem body regionOperationRowExtent 0
    (.enableLookup argument enabled row) hlookup

/-- Measure every `assignRegion` region (in region-index order; `loadTable`/layouter-level
`constrainInstance` are not measured — V1 `assign_table` is a no-op in the measurement pass,
`v1.rs:183-184`). -/
def measureRegions (ops : Operations F) : List RegionShape :=
  (indexedRegions ops 0).1.map fun (idx, body) => measureRegion idx body

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

/-- `recurse` (`sort.rs:694-777`): the pdqsort driver. The Rust `loop` with tail-`continue`
is unrolled into recursion — the "continue with the longer side" call carries the updated
`(was_balanced, was_partitioned)`; every *fresh* recursive call (the shorter side, and the
`partition_equal` tail) re-initialises them to `true` at function entry, exactly as a new
`recurse` frame does. Result is the fully sorted slice (children concatenated with the
pivot).

Total via explicit fuel (the `buildCombinations` pattern), recursion structural on the
fuel: every recursive call is on a STRICT sub-slice — the two sides exclude the pivot
(`sort.rs:760-763`), and the `partition_equal` tail drops at least the pivot
(`sort.rs:745-752`) — so the recursion depth is bounded by the slice length and
`fuel = v.size + 1` at the `quicksort` entry provably suffices. The `fuel = 0` arm is
unreachable; it falls back to `heapsort` — mirroring Rust's own strategy-exhaustion
fallback (`sort.rs:717-720`), so even that arm is a correct sort. -/
def recurse : ℕ → Array T → (T → T → Bool) → Option T → ℕ → Bool → Bool → Array T
  | 0, v, isLess, _, _, _, _ => heapsort v isLess
  | fuel + 1, v, isLess, pred, limit0, wasBalanced0, wasPartitioned => Id.run do
    let len := v.size
    if len ≤ 20 then return insertionSort v isLess
    if limit0 == 0 then return heapsort v isLess
    let mut v := v
    let mut limit := limit0
    let mut wasBalanced := wasBalanced0
    if !wasBalanced then
      v := breakPatterns v
      limit := limit - 1
    let ((pivot, likelySorted), v1) := choosePivot v isLess
    v := v1
    if wasBalanced && wasPartitioned && likelySorted then
      let (sorted, v2) := partialInsertionSort v isLess
      v := v2
      if sorted then return v
    -- pred-equal case: pivot is the smallest element (equal to predecessor).
    match pred with
    | some p =>
      if !isLess p (v[pivot]!) then
        let (mid, v3) := partitionEqual v pivot isLess
        let head := v3.extract 0 mid
        let tail := recurse fuel (v3.extract mid v3.size) isLess pred limit
          wasBalanced wasPartitioned
        return head ++ tail
    | none => pure ()
    let ((mid, wasP), v4) := partitionP v pivot isLess
    let newBalanced := decide (Nat.min mid (len - mid) ≥ len / 8)
    let pivotVal := v4[mid]!
    let left := v4.extract 0 mid
    let right := v4.extract (mid+1) v4.size
    if left.size < right.size then
      let left' := recurse fuel left isLess pred limit true true
      let right' := recurse fuel right isLess (some pivotVal) limit newBalanced wasP
      return left' ++ #[pivotVal] ++ right'
    else
      let right' := recurse fuel right isLess (some pivotVal) limit true true
      let left' := recurse fuel left isLess pred limit newBalanced wasP
      return left' ++ #[pivotVal] ++ right'

/-- `quicksort` (`sort.rs:780-793`): `limit = usize::BITS − leading_zeros(len)` = the bit
length of `len` = `Nat.log2 len + 1` for `len ≥ 1`. Fuel `v.size + 1` bounds the
recursion depth (see `recurse`). -/
def quicksort (v : Array T) (isLess : T → T → Bool) : Array T :=
  if v.size == 0 then v
  else recurse (v.size + 1) v isLess none (Nat.log2 v.size + 1) true true

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

/-- `free_intervals(start, end)` (`strategy.rs:64-98`): the unallocated intervals of this
column intersecting `[start, end)`, as `(spaceStart, spaceEnd?)` (`end? = none` unbounded).
Verbatim port of the `scan`: a region with `start ≥ end` is skipped without advancing `row`,
and the final unbounded item emits `[row, end)` when `end = none ∨ row < end`. -/
def Allocations.freeIntervals (a : Allocations) (start : ℕ) (endBound : Option ℕ) :
    List (ℕ × Option ℕ) := Id.run do
  let mut row := start
  let mut out : Array (ℕ × Option ℕ) := #[]
  for (rs, rlen) in a do
    let past : Bool := match endBound with | some e => decide (rs ≥ e) | none => false
    if !past then
      if row < rs then out := out.push (row, some rs)
      row := max row (rs + rlen)
  let emitFinal : Bool := match endBound with | some e => decide (row < e) | none => true
  if emitFinal then out := out.push (row, endBound)
  return out.toList

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

/-- The conservative fallback satisfies the semantic selector invariant. -/
theorem globallyDisjointStarts_sharedSelectorIntervalsDisjoint
    (shapes : List RegionShape) :
    SharedSelectorIntervalsDisjoint
      shapes (globallyDisjointStarts shapes) := by
  intro left right hleft hright hindices selector
    hleftSelector hrightSelector
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
  unfold addCol
  by_cases hcontains : columns.contains column = true
  · simp only [hcontains, ↓reduceIte]
    exact List.contains_iff_mem.mp hcontains
  · have hnotmem : column ∉ columns := by
      simpa only [List.contains_iff_mem] using hcontains
    simp [hnotmem]

private theorem mem_addCol_of_mem
    (columns : List RegionColumn) (added column : RegionColumn)
    (hcolumn : column ∈ columns) :
    column ∈ addCol columns added := by
  unfold addCol
  split <;> simp_all

private theorem mem_foldl_addCol_of_initial_mem
    (selectors : List Selector) (columns : List RegionColumn)
    {column : RegionColumn} (hcolumn : column ∈ columns) :
    column ∈
      selectors.foldl
        (fun current next => addCol current (.selector next.index))
        columns := by
  induction selectors generalizing columns with
  | nil =>
      exact hcolumn
  | cons head tail ih =>
      simp only [List.foldl_cons]
      exact ih _ (mem_addCol_of_mem columns (.selector head.index) column hcolumn)

private theorem mem_foldl_addCol_of_mem
    (selectors : List Selector) (columns : List RegionColumn)
    {selector : Selector} (hselector : selector ∈ selectors) :
    RegionColumn.selector selector.index ∈
      selectors.foldl
        (fun current next => addCol current (.selector next.index))
        columns := by
  induction selectors generalizing columns with
  | nil =>
      simp at hselector
  | cons head tail ih =>
      simp only [List.mem_cons] at hselector
      simp only [List.foldl_cons]
      rcases hselector with rfl | htail
      · exact mem_foldl_addCol_of_initial_mem tail _
          (mem_addCol_self columns (.selector selector.index))
      · exact ih (addCol columns (.selector head.index)) htail

private theorem mem_addOperationColumns_of_mem
    (columns : List RegionColumn) (operation : RegionOperation F)
    {column : RegionColumn} (hcolumn : column ∈ columns) :
    column ∈ addOperationColumns columns operation := by
  cases operation <;>
    simp [addOperationColumns, mem_addCol_of_mem,
      mem_foldl_addCol_of_initial_mem, hcolumn]

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
        cases operation with
        | enableGate gate operationRow =>
            rcases hactivation with ⟨rfl, rfl⟩
            exact mem_addCol_self columns (.selector gate.selector.index)
        | enableLookup argument enabled operationRow =>
            rcases hactivation with ⟨⟨selected, hselected, rfl⟩, rfl⟩
            exact mem_foldl_addCol_of_mem enabled columns hselected
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
  exact selector_mem_foldl_addOperationColumns_of_activation
    body [] hoperation hactivation

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
      exact value_le_foldl_max_of_mem body regionOperationRowExtent 0
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
Membership in the flattened activation list retains a concrete source region,
operation, and local row.
-/
theorem exists_activation_origin_of_mem_activations
    {starts : List ℕ} {regions : List (ℕ × RegionOperations F)}
    {selector absoluteRow : ℕ}
    (hactivation :
      (selector, absoluteRow) ∈ activations starts regions) :
    ∃ regionIndex body operation localRow,
      (regionIndex, body) ∈ regions ∧
      operation ∈ body ∧
      activatesSelectorAt selector localRow operation ∧
      absoluteRow = starts.getD regionIndex 0 + localRow := by
  simp only [activations, List.mem_flatMap] at hactivation
  obtain ⟨region, hregion, hbody⟩ := hactivation
  rcases region with ⟨regionIndex, body⟩
  obtain ⟨operation, hoperation, hop⟩ := hbody
  cases operation with
  | enableGate gate operationRow =>
      simp only [List.mem_singleton] at hop
      have hselector : gate.selector.index = selector :=
        (congrArg Prod.fst hop).symm
      have habsolute :
          starts.getD regionIndex 0 + operationRow = absoluteRow :=
        (congrArg Prod.snd hop).symm
      exact ⟨regionIndex, body, .enableGate gate operationRow,
        operationRow, hregion, hoperation, ⟨hselector, rfl⟩,
        habsolute.symm⟩
  | enableLookup argument enabled operationRow =>
      simp only [List.mem_map] at hop
      obtain ⟨enabledSelector, henabledSelector, hpair⟩ := hop
      have hselector : enabledSelector.index = selector :=
        congrArg Prod.fst hpair
      have habsolute :
          starts.getD regionIndex 0 + operationRow = absoluteRow :=
        congrArg Prod.snd hpair
      exact ⟨regionIndex, body,
        .enableLookup argument enabled operationRow, operationRow,
        hregion, hoperation,
        ⟨⟨enabledSelector, henabledSelector, hselector⟩, rfl⟩,
        habsolute.symm⟩
  | assignAdvice | assignFixed | constrainEqual | constrainConstant |
      constrainInstance =>
      simp at hop

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
The exact legacy V1 plan when its selector intervals pass the finite safety guard;
otherwise a conservative plan whose region intervals and allocation state agree.
-/
def planFull (shapes : List RegionShape) : List ℕ × CircuitAllocations :=
  let candidate := planCandidate shapes
  if @decide
      (CheckedSharedSelectorIntervalsDisjoint shapes candidate.1)
      (checkedSharedSelectorIntervalsDisjointDecidable shapes candidate.1) then
    candidate
  else
    (globallyDisjointStarts shapes, globallyDisjointAllocations shapes)

/-- The V1 region starts, per `assignRegion` index, from the operation stream. -/
def starts (ops : Operations F) : List ℕ := (planFull (measureRegions ops)).1

/--
V1 placement makes regions sharing a virtual selector column row-disjoint by
construction, independently of the legacy candidate's sorting implementation.
-/
theorem starts_sharedSelectorIntervalsDisjoint
    (ops : Operations F) :
    SharedSelectorIntervalsDisjoint
      (measureRegions ops) (starts ops) := by
  unfold starts planFull
  dsimp only
  split
  · rename_i hchecked
    exact sharedSelectorIntervalsDisjoint_of_checked
      (@of_decide_eq_true
        (CheckedSharedSelectorIntervalsDisjoint
          (measureRegions ops) (planCandidate (measureRegions ops)).1)
        (checkedSharedSelectorIntervalsDisjointDecidable
          (measureRegions ops) (planCandidate (measureRegions ops)).1)
        hchecked)
  · exact globallyDisjointStarts_sharedSelectorIntervalsDisjoint
      (measureRegions ops)

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
def constantValues (ops : Operations F) : List F :=
  (indexedRegions ops 0).1.flatMap fun (_, body) =>
    body.filterMap fun op => match op with
      | .constrainConstant _ v => some v
      | _ => none

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

/-- The V1 constants allocation `(value, constantsColIdx, row)` — the fixture's `constants`
field — derived from the operation stream and the planner's allocations. `constCols` is the
list of constants fixed-column indices (`cs.constants`, from `enable_constant`; orchard uses
a single column). Reproduces `v1.rs:102-136`: enumerate free rows per constants column, zip
with the collected constants. -/
def constants (toNat : F → ℕ) (ops : Operations F) (constCols : List ℕ) :
    List (ℕ × ℕ × ℕ) :=
  let (_, colAllocs) := planFull (measureRegions ops)
  let endRow := firstUnassignedRow colAllocs
  let positions : List (ℕ × ℕ) := constCols.flatMap fun c =>
    (freeRows colAllocs c endRow).map fun row => (c, row)
  (positions.zip (constantValues ops)).map fun ((c, row), v) => (toNat v, c, row)

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
