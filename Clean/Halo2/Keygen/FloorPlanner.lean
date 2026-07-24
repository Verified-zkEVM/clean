import Clean.Halo2.Operations

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

/-- `partition_in_blocks` (`sort.rs:233-465`): block-based Hoare partition. Returns the number
of elements `< pivot` and the mutated slice. The cyclic-permutation of swapped elements is
what fixes the (unstable) order of equal keys, so it is ported verbatim. -/
def partitionInBlocks (v0 : Array T) (pivot : T) (isLess : T → T → Bool) : ℕ × Array T := Id.run do
  let BLOCK := 128
  let mut v := v0
  let mut l : ℕ := 0
  let mut r : ℕ := v.size
  let mut block_l := BLOCK
  let mut block_r := BLOCK
  let mut offsets_l : Array ℕ := Array.replicate BLOCK 0
  let mut offsets_r : Array ℕ := Array.replicate BLOCK 0
  let mut start_l : ℕ := 0
  let mut end_l : ℕ := 0
  let mut start_r : ℕ := 0
  let mut end_r : ℕ := 0
  for _ in [0:v.size+4] do
    let is_done := (r - l) ≤ 2*BLOCK
    if is_done then
      let mut rem := r - l
      if start_l < end_l || start_r < end_r then rem := rem - BLOCK
      if start_l < end_l then block_r := rem
      else if start_r < end_r then block_l := rem
      else block_l := rem/2; block_r := rem - rem/2
    if start_l == end_l then
      start_l := 0; end_l := 0
      for i in [0:block_l] do
        offsets_l := offsets_l.set! end_l i
        if !isLess (v[l+i]!) pivot then end_l := end_l + 1
    if start_r == end_r then
      start_r := 0; end_r := 0
      for i in [0:block_r] do
        offsets_r := offsets_r.set! end_r i
        if isLess (v[r-1-i]!) pivot then end_r := end_r + 1
    let count := min (end_l - start_l) (end_r - start_r)
    if count > 0 then
      let tmp := v[l + offsets_l[start_l]!]!
      v := v.set! (l + offsets_l[start_l]!) (v[r - offsets_r[start_r]! - 1]!)
      for _ in [0:count-1] do
        start_l := start_l + 1
        v := v.set! (r - offsets_r[start_r]! - 1) (v[l + offsets_l[start_l]!]!)
        start_r := start_r + 1
        v := v.set! (l + offsets_l[start_l]!) (v[r - offsets_r[start_r]! - 1]!)
      v := v.set! (r - offsets_r[start_r]! - 1) tmp
      start_l := start_l + 1
      start_r := start_r + 1
    if start_l == end_l then l := l + block_l
    if start_r == end_r then r := r - block_r
    if is_done then break
  if start_l < end_l then
    for _ in [0:BLOCK+1] do
      if start_l < end_l then
        end_l := end_l - 1
        v := swp v (l + offsets_l[end_l]!) (r-1)
        r := r - 1
      else break
    return (r, v)
  else if start_r < end_r then
    for _ in [0:BLOCK+1] do
      if start_r < end_r then
        end_r := end_r - 1
        v := swp v l (r - offsets_r[end_r]! - 1)
        l := l + 1
      else break
    return (l, v)
  else
    return (l, v)

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
  | .enableGate gate operationRow =>
      gate.selector.index = selector ∧ operationRow = row
  | .enableLookup _ enabled operationRow =>
      (∃ enabledSelector ∈ enabled, enabledSelector.index = selector) ∧
        operationRow = row
  | _ => False

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
