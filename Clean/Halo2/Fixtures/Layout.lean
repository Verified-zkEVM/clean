import Clean.Halo2.Fixtures.FixtureTypes
import Clean.Halo2.Operations

/-!
# Phase-2 layout reconstruction (reusable, NOT mul-specific)

Given a Halo2-Clean layouter circuit's `Operations` and a `LayoutFixture` (the keygen-view
dump produced Rust-side), this module reconstructs — purely, `#eval`/`Decide`-computably —
the four layout products the fixture pins, so a test can `#guard` them EQUAL:

* the **ordered copy list** — the `region.copy(left, right)` sequence the keygen `Assembly`
  receives, in Rust floor-planner order (order-sensitive; pinpoints placement bugs);
* the permutation **σ** — the keygen cycle structure, replaying `permutation/keygen.rs`'s
  `Assembly::copy` merge-and-swap verbatim over the ordered copy list;
* the **fixed** assignments — loaded lookup tables (+ default-fill), the constants column,
  and the post-compression packed-selector columns;
* (implicitly, via `place`) the **region placements**.

## Conventions decided here (cross-checked against the Rust, documented at each site)

* **Copy argument order** — `region.constrain_equal(left, right)` lowers to
  `cs.copy(left.column, left.row, right.column, right.row)` (`single_pass.rs`
  `constrain_equal`), and `copy_advice` calls `constrain_equal(new_cell, src)`; the
  Halo2-Clean monad matches both (`Basic.lean`: `copyAdvice` emits
  `.constrainEqual (new) (src)`). So a copy tuple is `(leftCol, leftRow, rightCol, rightRow)`
  with `left` = the FIRST argument of `constrain_equal`.
* **Constants are deferred to the end of each `assign_region`** — `SingleChipLayouter::
  assign_region` runs the region body (emitting all its `constrain_equal` copies in order),
  THEN, after `exit_region`, assigns+copies the region's collected constants
  (`single_pass.rs`). Each `constrain_constant` therefore contributes ONE copy
  `cs.copy(constants_col, next_const_row, advice.col, advice.row)` — `left` = the constants
  cell — appended AFTER that region's `constrain_equal` copies. The constants-column cell
  `(col, row)` is not derivable Lean-side (the planner picks the row), so it is read from the
  fixture's `constants` allocation map, consumed in region-then-body order.
* **loadTable default-fill** starts at `values.length` and fills every remaining usable row
  with the row-0 value (`single_pass.rs` `fill_from_row` via `SimpleTableLayouter`); usable
  rows = `n − (blindingFactors + 1)`.
* **Packed selector encoding** — `compress_selectors` writes, into each combination's packed
  fixed column, this row's active selector's `assignedRoot` (1-based; 0 where none is active,
  and the invariant is that combination members are never co-enabled). Complex/degree-0
  selectors sit alone in their column (`len = 1, root = 1`), giving the bare 0/1 column.

All region indices threaded here are Halo2-Clean's `assignRegion`-only indices (like Rust's
`SingleChipLayouter::regions`), which — unlike the fixture's `enter_region`-order `regions`
list — do NOT count `assign_table`. `place` bridges the two by a lockstep walk (a `loadTable`
op consumes one fixture region slot, matching Rust's `assign_table` `enter_region`).
-/

namespace Halo2.Fixtures.Layout

open Halo2

variable {F : Type}

/-! ## Column translation (permutation-column order) -/

/-- A `ColRef` as an `AnyColumn` (the `Cell`/`Column` column spelling). -/
def ColRef.toAny : ColRef → AnyColumn
  | .advice i => ⟨.advice, i⟩
  | .fixed i => ⟨.fixed, i⟩
  | .instance i => ⟨.instance, i⟩

/-- Index of a column within the fixture's permutation-column order
(`cs.permutation.get_columns()`). Copy/σ tuples index into this list. -/
def permIndex (permCols : List ColRef) (c : AnyColumn) : ℕ :=
  ((permCols.map ColRef.toAny).findIdx? (· = c)).getD 9999

/-! ## Region placement (`place : regionIndex → start row`)

Lockstep walk over the flattened operation stream: every `region` and every `loadTable`
consumes the next fixture `RegionPlacement` (matching the Rust `enter_region` enumeration);
only `region`s carry a Halo2-Clean region index. The result is the start row per
`assignRegion`-index. -/

/-- The ordered stream of "region slots" (a `region` or a table load) as the fixture's
`enter_region` enumeration sees them. Recurses into layouter-level subcircuits. `true` marks
a real `assignRegion` (carries a Halo2-Clean index), `false` a `loadTable`/table slot. -/
def regionSlots : Operations F → List (Bool × String)
  | [] => []
  | .region name _ :: rest => (true, name) :: regionSlots rest
  | .loadTable _ _ :: rest => (false, "") :: regionSlots rest
  | .constrainInstance _ _ _ :: rest => regionSlots rest
  | .subcircuit sub :: rest => regionSlots sub ++ regionSlots rest
termination_by ops => sizeOf ops

/-- Start rows indexed by Halo2-Clean `assignRegion` index, obtained by zipping the region
slots with the fixture's `regions` (in index order): each slot consumes one placement; only
real regions contribute a start. -/
def regionStarts (ops : Operations F) (fx : LayoutFixture) : List ℕ :=
  let sorted := fx.regions.toArray.qsort (·.index < ·.index) |>.toList
  ((regionSlots ops).zip sorted).filterMap fun ((isRegion, _), pl) =>
    if isRegion then some pl.start else none

/-- `place : regionIndex → start row`, from the reconstructed `regionStarts`. -/
def place (starts : List ℕ) (i : RegionIndex) : ℕ := starts.getD i 0

/-- Absolute `(permColIdx, row)` of a cell: translate its column into permutation-column
order and add the region start to the region-local offset. -/
def resolveCell (permCols : List ColRef) (starts : List ℕ) (c : Cell) : ℕ × ℕ :=
  (permIndex permCols c.column, place starts c.regionIndex + c.rowOffset)

/-! ## Indexed region walk

Pairs each `assignRegion` body with its Halo2-Clean region index, threading the index
through subcircuits (region-level subcircuits stay in the ambient region; only `region`
increments). Everything downstream (copies, activations) is a fold over this list. -/

def indexedRegions : Operations F → ℕ → List (ℕ × RegionOperations F) × ℕ
  | [], i => ([], i)
  | .region _ body :: rest, i =>
      let (rs, i') := indexedRegions rest (i + 1)
      ((i, body) :: rs, i')
  | .subcircuit sub :: rest, i =>
      let (rs1, i1) := indexedRegions sub i
      let (rs2, i2) := indexedRegions rest i1
      (rs1 ++ rs2, i2)
  | .constrainInstance _ _ _ :: rest, i => indexedRegions rest i
  | .loadTable _ _ :: rest, i => indexedRegions rest i
termination_by ops => sizeOf ops

/-- Flatten a region body into its ordered leaf operations (recursing region-level
subcircuits, which share the ambient region). -/
def flattenRegion : RegionOperations F → List (RegionOperation F)
  | [] => []
  | .subcircuit sub :: rest => flattenRegion sub ++ flattenRegion rest
  | op :: rest => op :: flattenRegion rest
termination_by ops => sizeOf ops

/-! ## Ordered copy extraction -/

/-- Copies of ONE region, in Rust order: all `constrain_equal` copies in body order, THEN
the region's `constrain_constant` copies (deferred to the end of `assign_region`), each
consuming the next entry of the fixture's constants allocation map. Returns the copies and
the unconsumed constants tail. -/
def regionCopies (permCols : List ColRef) (starts : List ℕ)
    (body : RegionOperations F) (consts : List (ℕ × ℕ × ℕ)) :
    List (ℕ × ℕ × ℕ × ℕ) × List (ℕ × ℕ × ℕ) :=
  let leaves := flattenRegion body
  let eqCopies : List (ℕ × ℕ × ℕ × ℕ) := leaves.filterMap fun op =>
    match op with
    | .constrainEqual a b =>
        let (lc, lr) := resolveCell permCols starts a
        let (rc, rr) := resolveCell permCols starts b
        some (lc, lr, rc, rr)
    | .assignAdviceFromInstance icol irow cell =>
        -- Rust `assign_advice_from_instance`: the advice-left copy against the
        -- instance cell at its absolute row
        let (rc, rr) := resolveCell permCols starts cell
        some (rc, rr, permIndex permCols icol.toAny, irow)
    | _ => none
  -- deferred constants, in body order, consuming the fixture's allocation map
  let rec go : List (RegionOperation F) → List (ℕ × ℕ × ℕ) →
      List (ℕ × ℕ × ℕ × ℕ) × List (ℕ × ℕ × ℕ)
    | [], cs => ([], cs)
    | .constrainConstant cell _ :: rest, (_, cc, cr) :: cs =>
        let (rc, rr) := resolveCell permCols starts cell
        let (rest', cs') := go rest cs
        -- left = constants cell (fixed col `cc`, row `cr`), right = the advice cell
        ((permIndex permCols (ColRef.toAny (.fixed cc)), cr, rc, rr) :: rest', cs')
    | _ :: rest, cs => go rest cs
  let (constCopies, consts') := go leaves consts
  (eqCopies ++ constCopies, consts')

/-- The whole ordered copy list, folding `regionCopies` over regions in region order and
threading the fixture's constants allocation map. -/
def copyList (permCols : List ColRef) (starts : List ℕ)
    (regions : List (ℕ × RegionOperations F)) (consts : List (ℕ × ℕ × ℕ)) :
    List (ℕ × ℕ × ℕ × ℕ) :=
  let rec go : List (ℕ × RegionOperations F) → List (ℕ × ℕ × ℕ) → List (ℕ × ℕ × ℕ × ℕ)
    | [], _ => []
    | (_, body) :: rest, cs =>
        let (cps, cs') := regionCopies permCols starts body cs
        cps ++ go rest cs'
  go regions consts

/-- Like `regionCopies`, but with the equality and deferred-constants copies returned
separately (for planners that defer constants past the whole synthesis). -/
def regionCopiesSplit (permCols : List ColRef) (starts : List ℕ)
    (body : RegionOperations F) (consts : List (ℕ × ℕ × ℕ)) :
    List (ℕ × ℕ × ℕ × ℕ) × List (ℕ × ℕ × ℕ × ℕ) × List (ℕ × ℕ × ℕ) :=
  let (cps, consts') := regionCopies permCols starts body consts
  let isConst : (ℕ × ℕ × ℕ × ℕ) → Bool := fun _ => false
  -- `regionCopies` returns eq-copies first, then exactly the consumed constants
  let nEq := cps.length - (consts.length - consts'.length)
  (cps.take nEq, cps.drop nEq, consts')

/-- The whole-synthesis copy stream in the halo2-0.5 `SimpleFloorPlanner` order: region
equality copies in creation order with the layouter-level `constrain_instance` copies
inline (advice-left, instance-right), and ALL deferred `constrain_constant` copies at
the very end of synthesis (in region/collection order). -/
def copyStreamDeferred (permCols : List ColRef) (starts : List ℕ) :
    Operations F → List (ℕ × ℕ × ℕ) →
    List (ℕ × ℕ × ℕ × ℕ) × List (ℕ × ℕ × ℕ × ℕ)
  | [], _ => ([], [])
  | .region _ body :: rest, cs =>
      let (eqs, cnsts, cs') := regionCopiesSplit permCols starts body cs
      let (r1, r2) := copyStreamDeferred permCols starts rest cs'
      (eqs ++ r1, cnsts ++ r2)
  | .subcircuit sub :: rest, cs =>
      let (s1, s2) := copyStreamDeferred permCols starts sub cs
      -- thread the constants tail by count (sub consumed `cs.length - ?` — recompute)
      let consumed := s2.length
      let (r1, r2) := copyStreamDeferred permCols starts rest (cs.drop consumed)
      (s1 ++ r1, s2 ++ r2)
  | .constrainInstance cell col row :: rest, cs =>
      let (rc, rr) := resolveCell permCols starts cell
      let (r1, r2) := copyStreamDeferred permCols starts rest cs
      ((rc, rr, permIndex permCols col.toAny, row) :: r1, r2)
  | .loadTable _ _ :: rest, cs => copyStreamDeferred permCols starts rest cs
termination_by ops => sizeOf ops

/-- `copyStreamDeferred`, concatenated (the actual keygen copy order). -/
def copyListDeferred (permCols : List ColRef) (starts : List ℕ)
    (ops : Operations F) (consts : List (ℕ × ℕ × ℕ)) : List (ℕ × ℕ × ℕ × ℕ) :=
  let (eqs, cnsts) := copyStreamDeferred permCols starts ops consts
  eqs ++ cnsts

/-! ## Permutation σ — keygen `Assembly` replay (`permutation/keygen.rs`)

Verbatim port of `Assembly::{new, copy}`: `mapping`/`aux`/`sizes` are `numCols × n`; `copy`
merges the smaller cycle into the larger (size tie keeps `left`), re-points the merged
cycle's `aux`, then swaps the two `mapping` entries. Replayed over the ordered copy list. -/

structure Asm where
  mapping : Array (Array (ℕ × ℕ))
  aux : Array (Array (ℕ × ℕ))
  sizes : Array (Array ℕ)

namespace Asm

/-- `[(i,0), (i,1), …, (i,n-1)]` — column `i`'s initial 1-cycles. -/
def initCol (i n : ℕ) : Array (ℕ × ℕ) := (Array.range n).map (fun j => (i, j))

/-- `Assembly::new`: every cell its own 1-cycle. -/
def new (n numCols : ℕ) : Asm where
  mapping := (Array.range numCols).map (fun i => initCol i n)
  aux := (Array.range numCols).map (fun i => initCol i n)
  sizes := (Array.range numCols).map (fun _ => Array.replicate n 1)

@[inline] def getPair (a : Array (Array (ℕ × ℕ))) (p : ℕ × ℕ) : ℕ × ℕ := (a[p.1]!)[p.2]!
@[inline] def setPair (a : Array (Array (ℕ × ℕ))) (p : ℕ × ℕ) (v : ℕ × ℕ) :
    Array (Array (ℕ × ℕ)) := a.modify p.1 (·.set! p.2 v)
@[inline] def getNat (a : Array (Array ℕ)) (p : ℕ × ℕ) : ℕ := (a[p.1]!)[p.2]!
@[inline] def setNat (a : Array (Array ℕ)) (p : ℕ × ℕ) (v : ℕ) : Array (Array ℕ) :=
  a.modify p.1 (·.set! p.2 v)

/-- `Assembly::copy` over a permutation-column-indexed cell pair, with `n` bounding the
cycle walk (a cycle has ≤ `n·numCols` cells; `n` alone suffices since one column's walk
never exceeds `n` distinct rows before closing — but we bound generously by the copy count
in the caller). Here we bound the walk by `fuel`. -/
def copy (a : Asm) (fuel : ℕ) (lc lr rc rr : ℕ) : Asm := Id.run do
  let mut a := a
  let mut leftCycle := getPair a.aux (lc, lr)
  let mut rightCycle := getPair a.aux (rc, rr)
  if leftCycle == rightCycle then return a
  if getNat a.sizes leftCycle < getNat a.sizes rightCycle then
    let t := leftCycle; leftCycle := rightCycle; rightCycle := t
  -- sizes[leftCycle] += sizes[rightCycle]
  a := { a with sizes := setNat a.sizes leftCycle (getNat a.sizes leftCycle + getNat a.sizes rightCycle) }
  -- walk the right cycle, re-pointing aux to leftCycle (do-while: at least `rightCycle`)
  let mut i := rightCycle
  for _ in [0:fuel] do
    a := { a with aux := setPair a.aux i leftCycle }
    i := getPair a.mapping i
    if i == rightCycle then break
  -- swap mapping[lc][lr] and mapping[rc][rr]
  let tmp := getPair a.mapping (lc, lr)
  a := { a with mapping := setPair a.mapping (lc, lr) (getPair a.mapping (rc, rr)) }
  a := { a with mapping := setPair a.mapping (rc, rr) tmp }
  return a

end Asm

/-- Replay the whole copy list through the keygen `Assembly`, returning the final `mapping`. -/
def runAssembly (n numCols : ℕ) (copies : List (ℕ × ℕ × ℕ × ℕ)) : Array (Array (ℕ × ℕ)) :=
  (copies.foldl (fun a (lc, lr, rc, rr) => a.copy n lc lr rc rr) (Asm.new n numCols)).mapping

/-- Sparse σ entries `(col, row, col', row')` where `mapping[col][row] ≠ (col, row)`, in
`(col, row)` order (col-major) — the fixture's sorting. -/
def sigmaEntries (mapping : Array (Array (ℕ × ℕ))) : List (ℕ × ℕ × ℕ × ℕ) :=
  (mapping.toList.zipIdx.flatMap fun (colArr, i) =>
    colArr.toList.zipIdx.filterMap fun (v, j) =>
      if v = (i, j) then none else some (i, j, v.1, v.2))

/-! ## Fixed assignments -/

/-- Selector-activation rows: `(selectorIndex, absRow)` for every `enableGate` (its own
selector) and `enableLookup` (each enabled selector) across all regions. -/
def activations (starts : List ℕ) (regions : List (ℕ × RegionOperations F)) : List (ℕ × ℕ) :=
  regions.flatMap fun (idx, body) =>
    (flattenRegion body).flatMap fun op =>
      match op with
      | .enableGate gate row => [(gate.selector.index, place starts idx + row)]
      | .enableLookup _ enabled row =>
          enabled.map fun s => (s.index, place starts idx + row)
      | _ => []

/-- Blinding-factor count (`ConstraintSystem::blinding_factors`, `circuit.rs`):
`max(3, maxAdviceQueriesPerColumn) + 2`. -/
def blindingFactors (adviceQueryLayout : List (ℕ × ℤ)) : ℕ :=
  let cols := adviceQueryLayout.map Prod.fst
  let maxQ := (cols.map fun c => (cols.filter (· = c)).length).foldl Nat.max 0
  Nat.max 3 maxQ + 2

/-- Usable rows `n − (blindingFactors + 1)` (the last row is not usable). -/
def usableRows (n : ℕ) (adviceQueryLayout : List (ℕ × ℤ)) : ℕ :=
  n - blindingFactors adviceQueryLayout - 1

/-- Fixed entries from `loadTable` ops: the explicit block `[0, len)` then the default-fill
`[len, usable)` at the row-0 value, per table column (its inner fixed-column index). -/
def tableFixed [Inhabited F] (toNat : F → ℕ) (usable : ℕ) : Operations F → List (ℕ × ℕ × ℕ)
  | [] => []
  | .loadTable tbl values :: rest =>
      let col := tbl.inner.index
      let block := (List.range values.length).map fun r => (col, r, toNat values[r]!)
      let fill := if values.isEmpty then []
        else (List.range (usable - values.length)).map fun r =>
          (col, values.length + r, toNat values[0]!)
      block ++ fill ++ tableFixed toNat usable rest
  | .subcircuit sub :: rest => tableFixed toNat usable sub ++ tableFixed toNat usable rest
  | _ :: rest => tableFixed toNat usable rest
termination_by ops => sizeOf ops

/-- Packed selector-column fixed entries: for each selector activation, look its index up in
the compression map and write `assignedRoot` into its packed column at that row. The
activation list is deduped first: a selector shared by several gates is enabled once per
gate object per row (e.g. `mul_fixed`'s `q_range_check` under both the range-check and the
coords gate, matching Rust's two `enable` calls), and Rust's `enable_selector` is
idempotent per cell. -/
def selectorFixed (selMap : SelCompressMap) (acts : List (ℕ × ℕ)) : List (ℕ × ℕ × ℕ) :=
  acts.dedup.filterMap fun (sel, row) =>
    (selMap.entries.find? (·.1 = sel)).map fun (_, sc) => (sc.packedCol, row, sc.assignedRoot)

/-- Fixed entries from region-level `assignFixed` ops (e.g. `mul_fixed`'s per-window
Lagrange/`z` constants), at their placed absolute rows. -/
def regionAssignFixed {F : Type} (toNat : F → ℕ) (starts : List ℕ)
    (regions : List (ℕ × RegionOperations F)) : List (ℕ × ℕ × ℕ) :=
  regions.flatMap fun (idx, body) =>
    (flattenRegion body).filterMap fun op =>
      match op with
      | .assignFixed col row v => some (col.index, place starts idx + row, toNat v)
      | _ => none

/-- Fixed entries from in-region `assignFixed` ops (Rust `region.assign_fixed` — e.g.
Sinsemilla's per-row `q_s2` boundary values and the `fixed_y_q` load), resolved to
absolute rows. -/
def assignedFixed (toNat : F → ℕ) (starts : List ℕ)
    (regions : List (ℕ × RegionOperations F)) : List (ℕ × ℕ × ℕ) :=
  regions.flatMap fun (idx, body) =>
    (flattenRegion body).filterMap fun op =>
      match op with
      | .assignFixed col row v => some (col.index, place starts idx + row, toNat v)
      | _ => none

/-- Deduplicate fixed entries by cell, keeping the LAST write (Rust `assign_fixed` on the
same cell overwrites; Halo2-Clean re-pins — e.g. a piece boundary's `q_s2` — are idempotent
same-value double writes, and a selector enabled by both a gate and a lookup at the same row
activates once). -/
def dedupFixed (l : List (ℕ × ℕ × ℕ)) : List (ℕ × ℕ × ℕ) :=
  let rec go : List (ℕ × ℕ × ℕ) → List (ℕ × ℕ × ℕ)
    | [] => []
    | (c, r, v) :: rest =>
        if rest.any fun (c', r', _) => c' = c ∧ r' = r then go rest
        else (c, r, v) :: go rest
  go l

/-- The constants column's fixed entries, straight from the fixture's allocation map:
`(value, col, row) ↦ (col, row, value)`. -/
def constantsFixed (consts : List (ℕ × ℕ × ℕ)) : List (ℕ × ℕ × ℕ) :=
  consts.map fun (v, c, r) => (c, r, v)

/-- Sort fixed entries canonically by `(col, row)` (col-major) — the fixture's order. -/
def sortFixed (l : List (ℕ × ℕ × ℕ)) : List (ℕ × ℕ × ℕ) :=
  l.toArray.qsort (fun (c₁, r₁, _) (c₂, r₂, _) => c₁ < c₂ ∨ (c₁ = c₂ ∧ r₁ < r₂)) |>.toList

/-- The full canonical fixed list: tables ++ region `assignFixed`s ++ constants ++ packed
selectors, sorted. -/
def allFixed [Inhabited F] (toNat : F → ℕ) (usable : ℕ) (selMap : SelCompressMap)
    (ops : Operations F) (starts : List ℕ) (regions : List (ℕ × RegionOperations F))
    (consts : List (ℕ × ℕ × ℕ)) : List (ℕ × ℕ × ℕ) :=
  sortFixed (tableFixed toNat usable ops
    ++ regionAssignFixed toNat starts regions
    ++ constantsFixed consts
    ++ selectorFixed selMap (activations starts regions))

end Halo2.Fixtures.Layout
