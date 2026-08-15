import Clean.Halo2.Keygen.CompressSelectors
import Clean.Halo2.Keygen.FloorPlanner
import Batteries.Data.Array.Lemmas
import Mathlib.Data.List.GetD

/-!
# Phase-2 layout reconstruction (reusable, NOT mul-specific)

Given a Halo2-Clean layouter circuit's `Operations`, this module reconstructs — purely,
`#eval`/`Decide`-computably — the keygen layout products a fixture (or verifying-key
derivation) consumes:

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
* **Constants-copy timing is the floor planner's ONE degree of freedom** — each
  `constrain_constant` contributes ONE copy
  `cs.copy(constants_col, next_const_row, advice.col, advice.row)` — `left` = the
  constants cell — but WHEN it enters the stream depends on the planner:
  `SimpleFloorPlanner` flushes per `assign_region`, `V1` (what orchard declares) once at
  the end of synthesis. See the "Ordered copy extraction" section; the two planner
  namespaces there mirror the Rust module split. The constants-column cell `(col, row)`
  is not derivable Lean-side (the planner picks the row), so it is read from the
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

namespace Halo2.Layout

variable {F : Type}

/-- A permutation-argument column reference, in `cs.permutation.get_columns()` order
(`.advice`/`.fixed`/`.instance` with a per-type column index). -/
inductive ColRef where
  | advice : ℕ → ColRef
  | fixed : ℕ → ColRef
  | instance : ℕ → ColRef
deriving DecidableEq, Repr

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
`enter_region` enumeration sees them. `true` marks a real `assignRegion` (carries a
Halo2-Clean index), `false` a `loadTable`/table slot. -/
def regionSlots : Operations F → List (Bool × String)
  | [] => []
  | .region name _ :: rest => (true, name) :: regionSlots rest
  | .loadTable _ _ :: rest => (false, "") :: regionSlots rest
  | .constrainInstance _ _ _ :: rest => regionSlots rest

/-- `place : regionIndex → start row`, from the reconstructed `regionStarts`. -/
def place (starts : List ℕ) (i : RegionIndex) : ℕ := starts.getD i 0

/-- Absolute `(permColIdx, row)` of a cell: translate its column into permutation-column
order and add the region start to the region-local offset. -/
def resolveCell (permCols : List ColRef) (starts : List ℕ) (c : Cell) : ℕ × ℕ :=
  (permIndex permCols c.column, place starts c.regionIndex + c.rowOffset)

/-! ## Ordered copy extraction — the two halo2 floor planners

`halo2_proofs 0.3.2` (github.com/zcash/halo2) ships two floor planners, and for the
copy stream they differ ONLY in when the `constrain_constant` copies collected during
a region are handed to keygen:

* **`SimpleFloorPlanner`** (`floor_planner/single_pass.rs:115-138`): at the end of EACH
  `assign_region` — the stream interleaves per region. Used by the isolated-chip dump
  harnesses (the Add/Mul fixtures).
* **`V1`** (`floor_planner/v1.rs:118-122`): once at the very end of synthesis — every
  equality/instance copy first (region creation order), then all constants copies.
  This is the planner the real orchard `Circuit` declares (`orchard/src/circuit.rs:1044`,
  VK-stable via the `floor-planner-v1-legacy-pdqsort` feature), so the Action fixtures
  follow it.

Everything else is planner-independent: `constrain_equal` and in-region instance copies
are recorded in body order during the region closures, layouter-level
`constrain_instance` copies inline between regions. `regionCopiesSplit` extracts one
region's (equality, constants) streams; each planner namespace below is just its flush
policy, mirroring the Rust module split. Constants-column rows are read from the
fixture's allocation map — the planner picks them, Lean does not re-derive placement. -/

/-- One region's copies, split into the `constrain_equal`/instance copies (body order)
and the `constrain_constant` copies (body order, each consuming the next entry of the
fixture's constants allocation map); also returns the unconsumed constants tail.
If the allocation map runs out, remaining `constrain_constant` copies are dropped —
the copy-list `#guard` then fails against the fixture, so a truncated map is loud, but
when debugging a mismatch check the fixture's `constants` length first. -/
def regionCopiesSplit (permCols : List ColRef) (starts : List ℕ)
    (body : RegionOperations F) (consts : List (ℕ × ℕ × ℕ)) :
    List (ℕ × ℕ × ℕ × ℕ) × List (ℕ × ℕ × ℕ × ℕ) × List (ℕ × ℕ × ℕ) :=
  let eqCopies : List (ℕ × ℕ × ℕ × ℕ) := body.filterMap fun op =>
    match op with
    | .constrainEqual a b =>
        let (lc, lr) := resolveCell permCols starts a
        let (rc, rr) := resolveCell permCols starts b
        some (lc, lr, rc, rr)
    | .constrainInstance cell icol irow =>
        -- Rust `assign_advice_from_instance`: the advice-left copy against the
        -- instance cell at its absolute row
        let (rc, rr) := resolveCell permCols starts cell
        some (rc, rr, permIndex permCols icol.toAny, irow)
    | _ => none
  let rec go : List (RegionOperation F) → List (ℕ × ℕ × ℕ) →
      List (ℕ × ℕ × ℕ × ℕ) × List (ℕ × ℕ × ℕ)
    | [], cs => ([], cs)
    | .constrainConstant cell _ :: rest, (_, cc, cr) :: cs =>
        let (rc, rr) := resolveCell permCols starts cell
        let (rest', cs') := go rest cs
        -- left = constants cell (fixed col `cc`, row `cr`), right = the advice cell
        ((permIndex permCols (ColRef.toAny (.fixed cc)), cr, rc, rr) :: rest', cs')
    | _ :: rest, cs => go rest cs
  let (constCopies, consts') := go body consts
  (eqCopies, constCopies, consts')

namespace SimpleFloorPlanner

/-- The op-stream walk in `SimpleFloorPlanner` order: each region flushes its constants
copies immediately after its equality copies (`assign_region` assigns
`constants_to_assign` on exit, `single_pass.rs:115-138`). Returns the copies and the
unconsumed constants tail. -/
def go (permCols : List ColRef) (starts : List ℕ) :
    Operations F → List (ℕ × ℕ × ℕ) →
    List (ℕ × ℕ × ℕ × ℕ) × List (ℕ × ℕ × ℕ)
  | [], cs => ([], cs)
  | .region _ body :: rest, cs =>
      let (eqs, cnsts, cs') := regionCopiesSplit permCols starts body cs
      let (r, cs'') := go permCols starts rest cs'
      (eqs ++ cnsts ++ r, cs'')
  | .constrainInstance cell col row :: rest, cs =>
      let (rc, rr) := resolveCell permCols starts cell
      let (r, cs') := go permCols starts rest cs
      ((rc, rr, permIndex permCols col.toAny, row) :: r, cs')
  | .loadTable _ _ :: rest, cs => go permCols starts rest cs

/-- The keygen copy list under `SimpleFloorPlanner` (`single_pass.rs`). -/
def copyList (permCols : List ColRef) (starts : List ℕ)
    (ops : Operations F) (consts : List (ℕ × ℕ × ℕ)) : List (ℕ × ℕ × ℕ × ℕ) :=
  (go permCols starts ops consts).1

end SimpleFloorPlanner

namespace V1

/-- The op-stream walk in `V1` order: the equality/instance stream and the
whole-synthesis constants stream, kept separate (`v1.rs` collects `plan.constants`
across all regions and assigns them at the end, `v1.rs:118-122`). Returns both streams
and the unconsumed constants tail. -/
def go (permCols : List ColRef) (starts : List ℕ) :
    Operations F → List (ℕ × ℕ × ℕ) →
    (List (ℕ × ℕ × ℕ × ℕ) × List (ℕ × ℕ × ℕ × ℕ)) × List (ℕ × ℕ × ℕ)
  | [], cs => (([], []), cs)
  | .region _ body :: rest, cs =>
      let (eqs, cnsts, cs') := regionCopiesSplit permCols starts body cs
      let ((r1, r2), cs'') := go permCols starts rest cs'
      ((eqs ++ r1, cnsts ++ r2), cs'')
  | .constrainInstance cell col row :: rest, cs =>
      let (rc, rr) := resolveCell permCols starts cell
      let ((r1, r2), cs') := go permCols starts rest cs
      (((rc, rr, permIndex permCols col.toAny, row) :: r1, r2), cs')
  | .loadTable _ _ :: rest, cs => go permCols starts rest cs

/-- The keygen copy list under the `V1` floor planner (`v1.rs`): the equality/instance
stream, then ALL deferred constants. The planner the orchard `Circuit` declares — the
Action fixtures' order. -/
def copyList (permCols : List ColRef) (starts : List ℕ)
    (ops : Operations F) (consts : List (ℕ × ℕ × ℕ)) : List (ℕ × ℕ × ℕ × ℕ) :=
  let ((eqs, cnsts), _) := go permCols starts ops consts
  eqs ++ cnsts

end V1

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

/-- Re-point the `aux` representative of every cell on the `mapping`-walk from `i` to
`tgt`, stopping once the walk returns to `stop` (Rust's do-while over the merged-in
cycle: the first visited cell IS `stop`, so it is re-pointed before the return test).
Structurally fuel-recursive — iteration-for-iteration the `for`-loop it replaces — so
proofs can follow the walk directly; callers pass fuel covering any cycle length. -/
def repoint (a : Asm) : ℕ → (ℕ × ℕ) → (ℕ × ℕ) → (ℕ × ℕ) → Asm
  | 0, _, _, _ => a
  | fuel + 1, i, tgt, stop =>
      let a' := { a with aux := setPair a.aux i tgt }
      let next := getPair a.mapping i
      if next == stop then a' else a'.repoint fuel next tgt stop

/-- The merge branch of `Assembly::copy`: absorb the smaller cycle into the larger and
swap the two mapping entries. Split from `copy` so its `mapping`/`aux` components can be
characterized separately (the walk never touches `mapping` or `sizes`; the swap never
touches `aux`). -/
def merge (a : Asm) (fuel : ℕ) (lp rp : ℕ × ℕ) : Asm :=
  let leftRep := getPair a.aux lp
  let rightRep := getPair a.aux rp
  -- the size comparison decides which representative survives the merge
  let smaller := getNat a.sizes leftRep < getNat a.sizes rightRep
  let leftCycle := if smaller then rightRep else leftRep
  let rightCycle := if smaller then leftRep else rightRep
  -- sizes[leftCycle] += sizes[rightCycle]
  let a1 := { a with sizes := setNat a.sizes leftCycle (getNat a.sizes leftCycle + getNat a.sizes rightCycle) }
  -- walk the right cycle, re-pointing aux to leftCycle (do-while: at least `rightCycle`)
  let a2 := a1.repoint fuel rightCycle leftCycle rightCycle
  -- swap mapping[lc][lr] and mapping[rc][rr]
  let tmp := getPair a2.mapping lp
  let a3 := { a2 with mapping := setPair a2.mapping lp (getPair a2.mapping rp) }
  { a3 with mapping := setPair a3.mapping rp tmp }

/-- `Assembly::copy` over a permutation-column-indexed cell pair, with `fuel` bounding
the cycle walk (a cycle has ≤ `n·numCols` cells; the caller passes exactly that). Plain
lets and a recursive walk instead of Rust's mutation, so the merge is provable against
the abstract swap-composition replay (`replayKeygenPermutation`). -/
def copy (a : Asm) (fuel : ℕ) (lc lr rc rr : ℕ) : Asm :=
  if getPair a.aux (lc, lr) == getPair a.aux (rc, rr) then a
  else merge a fuel (lc, lr) (rc, rr)

end Asm

/-- Replay the whole copy list through the keygen `Assembly`, returning the final `mapping`.
The walk fuel is `n * numCols` — an upper bound on any cycle's length (a cycle visits each
cell at most once), so every `repoint` walk completes exactly as Rust's unbounded do-while. -/
def runAssembly (n numCols : ℕ) (copies : List (ℕ × ℕ × ℕ × ℕ)) : Array (Array (ℕ × ℕ)) :=
  (copies.foldl (fun a (lc, lr, rc, rr) => a.copy (n * numCols) lc lr rc rr)
    (Asm.new n numCols)).mapping

/-- Sparse σ entries `(col, row, col', row')` where `mapping[col][row] ≠ (col, row)`, in
`(col, row)` order (col-major) — the fixture's sorting. -/
def sigmaEntries (mapping : Array (Array (ℕ × ℕ))) : List (ℕ × ℕ × ℕ × ℕ) :=
  (mapping.toList.zipIdx.flatMap fun (colArr, i) =>
    colArr.toList.zipIdx.filterMap fun (v, j) =>
      if v = (i, j) then none else some (i, j, v.1, v.2))

/-! ## Fixed assignments -/

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
  | _ :: rest => tableFixed toNat usable rest

/-- Packed selector-column fixed entries: for each selector activation, look its index up in
the compression map and write `assignedRoot` into its packed column at that row. The
activation list is deduped first: a selector shared by several gates is enabled once per
gate object per row (e.g. `mul_fixed`'s `q_range_check` under both the range-check and the
coords gate, matching Rust's two `enable` calls), and Rust's `enable_selector` is
idempotent per cell.

Dedup is by `Std.HashSet` (O(n)) rather than `List.dedup` (O(n²) over thousands of
activations). Set-semantics is exact: duplicate activations are the SAME `(sel, row)` pair,
so they map to identical output entries; the resulting output order is arbitrary but every
call site immediately sorts with `sortFixed` (verified: `selectorFixed` is only ever used
inside a `sortFixed (…)`), so order-freedom is safe. -/
def selectorFixed (selMap : SelCompressMap) (acts : List (ℕ × ℕ)) : List (ℕ × ℕ × ℕ) :=
  let uniq : Std.HashSet (ℕ × ℕ) := acts.foldl (·.insert ·) ∅
  uniq.toList.filterMap fun (sel, row) =>
    (selMap.entries.find? (·.1 = sel)).map fun (_, sc) => (sc.packedCol, row, sc.assignedRoot)

/-- Fixed entries from region-level `assignFixed` ops (Rust `region.assign_fixed` —
e.g. `mul_fixed`'s per-window Lagrange/`z` constants, Sinsemilla's per-row `q_s2`
boundary values and the `fixed_y_q` load), at their placed absolute rows. -/
def regionAssignFixed {F : Type} (toNat : F → ℕ) (starts : List ℕ)
    (regions : List (ℕ × RegionOperations F)) : List (ℕ × ℕ × ℕ) :=
  regions.flatMap fun (idx, body) =>
    body.filterMap fun op =>
      match op with
      | .assignFixed col row v => some (col.index, place starts idx + row, toNat v)
      | _ => none

/-- Deduplicate fixed entries by cell, keeping the LAST write (Rust `assign_fixed` on the
same cell overwrites; Halo2-Clean re-pins — e.g. a piece boundary's `q_s2` — are idempotent
same-value double writes, and a selector enabled by both a gate and a lookup at the same row
activates once).

Implemented with `Std.HashMap` keyed on the cell `(col, row)` — O(n) rather than the O(n²)
of the previous `rest.any`-per-element scan (the fixed list runs to 17.5k+ entries). Folding
left with `insert` keeps the LAST value per key (later writes overwrite), which is exactly
the overwrite semantics above. The output order is arbitrary but every call site immediately
sorts with `sortFixed` (verified: `dedupFixed` is only ever used inside a `sortFixed (…)`),
so order-freedom is safe. -/
def dedupFixed (l : List (ℕ × ℕ × ℕ)) : List (ℕ × ℕ × ℕ) :=
  let m : Std.HashMap (ℕ × ℕ) ℕ := l.foldl (fun m (c, r, v) => m.insert (c, r) v) ∅
  m.toList.map fun ((c, r), v) => (c, r, v)

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

/-! ## Field-valued fixed-row compiler

The fixture-facing helpers above deliberately expose natural-number encodings. Semantic
environments and key generation should instead consume the field-valued compiler below.
It derives every input from the closed constraint system and operation stream; callers
cannot substitute arbitrary fixed cells, placements, or constants allocations.
-/

/-- One compiled fixed-cell assignment `(column, absolute row, field value)`. -/
abbrev FixedAssignment (F : Type) := ℕ × ℕ × F

namespace FixedAssignment

/-- The fixed cell addressed by one sparse assignment. -/
def cell (assignment : FixedAssignment F) : ℕ × ℕ :=
  (assignment.1, assignment.2.1)

end FixedAssignment

/-- Loaded-table assignments, including Halo2's default-fill over all usable rows. -/
def tableAssignments (usable : ℕ) : Operations F → List (FixedAssignment F)
  | [] => []
  | .loadTable table values :: rest =>
      let column := table.inner.index
      let block := values.zipIdx.map fun (value, row) => (column, row, value)
      let fill := match values with
        | [] => []
        | first :: _ =>
            (List.range (usable - values.length)).map fun row =>
              (column, values.length + row, first)
      block ++ fill ++ tableAssignments usable rest
  | _ :: rest => tableAssignments usable rest

/-- Region-level `assignFixed` operations at their V1-placed absolute rows. -/
def regionAssignments (starts : List ℕ)
    (regions : List (ℕ × RegionOperations F)) : List (FixedAssignment F) :=
  regions.flatMap fun (index, body) =>
    body.filterMap fun operation =>
      match operation with
      | .assignFixed column row value =>
          some (column.index, place starts index + row, value)
      | _ => none

/-- V1 deferred constants as ordinary fixed-cell assignments. -/
def constantAssignments
    (assignments : List (F × ℕ × ℕ)) : List (FixedAssignment F) :=
  assignments.map fun (value, column, row) => (column, row, value)

/--
Packed-selector assignments in the circuit field.

`assignedRoot` is a combinatorial natural-number output of selector compression.
`FiniteField.fromNat` is the canonical interpretation in an arbitrary finite field;
in particular this does not incorrectly use `Nat.cast` for binary extension fields.
-/
def selectorAssignments [FiniteField F]
    (selectorMap : SelCompressMap) (selectorActivations : List (ℕ × ℕ)) :
    List (FixedAssignment F) :=
  let unique : Std.HashSet (ℕ × ℕ) :=
    selectorActivations.foldl (·.insert ·) ∅
  unique.toList.filterMap fun (selector, row) =>
    (selectorMap.entries.find? (·.1 = selector)).map fun (_, compressed) =>
      (compressed.packedCol, row, FiniteField.fromNat compressed.assignedRoot)

/-- Deduplicate field-valued assignments by cell, retaining the last write. -/
def dedupAssignments
    (assignments : List (FixedAssignment F)) : List (FixedAssignment F) :=
  let values : Std.HashMap (ℕ × ℕ) F :=
    assignments.foldl
      (fun values (column, row, value) =>
        values.insert (column, row) value)
      ∅
  values.toList.map fun ((column, row), value) => (column, row, value)

/-- Hash-map deduplication emits at most one assignment for each fixed cell. -/
theorem dedupAssignments_cells_nodup
    (assignments : List (FixedAssignment F)) :
    (dedupAssignments assignments).map FixedAssignment.cell |>.Nodup := by
  let values : Std.HashMap (ℕ × ℕ) F :=
    assignments.foldl
      (fun values (column, row, value) =>
        values.insert (column, row) value)
      ∅
  have hcellMap :
      FixedAssignment.cell ∘
          (fun (entry : (ℕ × ℕ) × F) =>
            (entry.1.1, entry.1.2, entry.2)) =
        Prod.fst := by
    funext entry
    rcases entry with ⟨⟨column, row⟩, value⟩
    rfl
  rw [show dedupAssignments assignments =
      values.toList.map
        (fun entry => (entry.1.1, entry.1.2, entry.2)) from rfl,
    List.map_map, hcellMap, Std.HashMap.map_fst_toList_eq_keys]
  exact values.nodup_keys

/-- Sort field-valued assignments canonically by `(column, row)`. -/
def sortAssignments
    (assignments : List (FixedAssignment F)) : List (FixedAssignment F) :=
  assignments.mergeSort
    (fun (leftColumn, leftRow, _) (rightColumn, rightRow, _) =>
      leftColumn < rightColumn ∨
        (leftColumn = rightColumn ∧ leftRow < rightRow))

/-- Canonical sorting changes only assignment order. -/
theorem sortAssignments_perm
    (assignments : List (FixedAssignment F)) :
    (sortAssignments assignments).Perm assignments := by
  exact List.mergeSort_perm _ _

/-- Canonical sorting preserves fixed-cell uniqueness. -/
theorem sortAssignments_cells_nodup
    (assignments : List (FixedAssignment F))
    (hnodup : (assignments.map FixedAssignment.cell).Nodup) :
    ((sortAssignments assignments).map FixedAssignment.cell).Nodup := by
  exact ((sortAssignments_perm assignments).map FixedAssignment.cell).nodup_iff.mpr
    hnodup

/--
Compile every fixed cell of a closed circuit: tables, V1 deferred constants, compressed
selectors, and placed region assignments.
-/
def compileFixed [FiniteField F]
    (usable : ℕ) (selectorMap : SelCompressMap)
    (constraintSystem : ConstraintSystem F) (operations : Operations F) :
    List (FixedAssignment F) :=
  let starts := FloorPlanner.V1.starts operations
  let regions := (indexedRegions operations 0).1
  sortAssignments (dedupAssignments
    (tableAssignments usable operations
      ++ constantAssignments
        (FloorPlanner.V1.constantAssignments operations
          (constraintSystem.constants.map (·.index)))
      ++ selectorAssignments selectorMap (activations starts regions)
      ++ regionAssignments starts regions))

/-- The fixed compiler emits at most one value for each fixed cell. -/
theorem compileFixed_cells_nodup [FiniteField F]
    (usable : ℕ) (selectorMap : SelCompressMap)
    (constraintSystem : ConstraintSystem F) (operations : Operations F) :
    ((compileFixed usable selectorMap constraintSystem operations).map
      FixedAssignment.cell).Nodup := by
  apply sortAssignments_cells_nodup
  apply dedupAssignments_cells_nodup

/-- Scatter one fixed assignment into a rectangular dense-column accumulator. -/
def scatterFixed [Zero F] (numColumns : ℕ) (columns : Array (Array F))
    (assignment : FixedAssignment F) : Array (Array F) :=
  let (column, row, value) := assignment
  if column < numColumns then
    columns.modify column fun values => values.set! row value
  else
    columns

private def fixedCell? (columns : Array (Array F))
    (column row : ℕ) : Option F :=
  columns[column]?.bind fun values => values[row]?

private theorem fixedCell?_scatterFixed [Zero F]
    {numRows numColumns : ℕ} {columns : Array (Array F)}
    (hcolumns : columns.size = numColumns)
    (hrows : ∀ column (hcolumn : column < columns.size),
      columns[column].size = numRows)
    (assignment : FixedAssignment F)
    (column row : ℕ) (hcolumn : column < numColumns)
    (hrow : row < numRows) :
    fixedCell? (scatterFixed numColumns columns assignment) column row =
      if assignment.cell = (column, row) then some assignment.2.2
      else fixedCell? columns column row := by
  rcases assignment with ⟨assignedColumn, assignedRow, value⟩
  simp only [FixedAssignment.cell, scatterFixed]
  have hcolumnCurrent : column < columns.size := by
    simpa only [hcolumns] using hcolumn
  have hrowCurrent : row < columns[column].size := by
    simpa only [hrows column hcolumnCurrent] using hrow
  split
  next hassignedColumn =>
    by_cases hsameColumn : assignedColumn = column
    · subst assignedColumn
      by_cases hsameRow : assignedRow = row
      · subst assignedRow
        simp only [fixedCell?, Array.getElem?_modify]
        rw [Array.getElem?_eq_getElem hcolumnCurrent]
        simp only [Option.map_some, Option.bind_some, Array.set!, if_true]
        rw [Array.getElem?_eq_getElem (by simpa using hrowCurrent)]
        rw [Array.getElem_setIfInBounds hrowCurrent]
        simp
      · have hpair : (column, assignedRow) ≠ (column, row) := by
          simp [hsameRow]
        simp only [fixedCell?, Array.getElem?_modify]
        rw [Array.getElem?_eq_getElem hcolumnCurrent]
        simp only [Option.map_some, Option.bind_some, Array.set!, if_true]
        rw [Array.getElem?_eq_getElem (by simpa using hrowCurrent)]
        rw [Array.getElem_setIfInBounds (by simpa using hrowCurrent)]
        simp [hsameRow, hpair]
    · have hpair : (assignedColumn, assignedRow) ≠ (column, row) := by
        simp [hsameColumn]
      simp [fixedCell?, Array.getElem?_modify, hsameColumn, hpair]
  next hassignedColumn =>
    have hne : (assignedColumn, assignedRow) ≠ (column, row) := by
      intro hequal
      injection hequal with hequal
      subst assignedColumn
      exact hassignedColumn hcolumn
    simp [fixedCell?, hne]

/--
Compile sparse fixed assignments into `numColumns` dense columns of `numRows` values.
Unassigned and out-of-range cells are zero, matching Halo2's empty Lagrange polynomial.
-/
def denseFixedColumns [Zero F] (numRows numColumns : ℕ)
    (assignments : List (FixedAssignment F)) : List (List F) :=
  let initial : Array (Array F) :=
    Array.replicate numColumns (Array.replicate numRows 0)
  (assignments.foldl (scatterFixed numColumns) initial).toList.map Array.toList

private theorem scatterFixed_sized [Zero F]
    {numRows numColumns : ℕ} {columns : Array (Array F)}
    (hcolumns : columns.size = numColumns)
    (hrows : ∀ column (hcolumn : column < columns.size),
      columns[column].size = numRows)
    (assignment : FixedAssignment F) :
    let next := scatterFixed numColumns columns assignment
    next.size = numColumns ∧
      ∀ column (hcolumn : column < next.size),
        next[column].size = numRows := by
  rcases assignment with ⟨column, row, value⟩
  simp only [scatterFixed]
  split
  next hcolumn =>
    constructor
    · simpa only [Array.size_modify] using hcolumns
    · intro other hother
      rw [Array.getElem_modify hother]
      split
      next hequal =>
        subst other
        simp only [Array.size_set!]
        exact hrows column (by simpa only [hcolumns] using hcolumn)
      next _ =>
        exact hrows other (by simpa using hother)
  next _ =>
    exact ⟨hcolumns, hrows⟩

private theorem scatterFixed_fold_sized [Zero F]
    {numRows numColumns : ℕ}
    (assignments : List (FixedAssignment F))
    {columns : Array (Array F)}
    (hcolumns : columns.size = numColumns)
    (hrows : ∀ column (hcolumn : column < columns.size),
      columns[column].size = numRows) :
    let result := assignments.foldl (scatterFixed numColumns) columns
    result.size = numColumns ∧
      ∀ column (hcolumn : column < result.size),
        result[column].size = numRows := by
  induction assignments generalizing columns with
  | nil =>
      exact ⟨hcolumns, hrows⟩
  | cons assignment rest inductionHypothesis =>
      simp only [List.foldl_cons]
      have hnext := scatterFixed_sized hcolumns hrows assignment
      exact inductionHypothesis hnext.1 hnext.2

private theorem fixedCell?_scatterFixed_fold_eq_of_forall_cell_ne [Zero F]
    {numRows numColumns : ℕ}
    (assignments : List (FixedAssignment F))
    {columns : Array (Array F)}
    (hcolumns : columns.size = numColumns)
    (hrows : ∀ column (hcolumn : column < columns.size),
      columns[column].size = numRows)
    (column row : ℕ) (hcolumn : column < numColumns)
    (hrow : row < numRows)
    (havoids : ∀ assignment ∈ assignments,
      assignment.cell ≠ (column, row)) :
    fixedCell? (assignments.foldl (scatterFixed numColumns) columns) column row =
      fixedCell? columns column row := by
  induction assignments generalizing columns with
  | nil => rfl
  | cons assignment rest inductionHypothesis =>
      simp only [List.foldl_cons]
      have hnext := scatterFixed_sized hcolumns hrows assignment
      rw [inductionHypothesis hnext.1 hnext.2]
      · rw [fixedCell?_scatterFixed hcolumns hrows assignment column row hcolumn hrow]
        simp only [if_neg (havoids assignment List.mem_cons_self)]
      · intro remaining hremaining
        exact havoids remaining (List.mem_cons_of_mem assignment hremaining)

private theorem fixedCell?_scatterFixed_fold_eq_of_mem [Zero F]
    {numRows numColumns : ℕ}
    (assignments : List (FixedAssignment F))
    {columns : Array (Array F)}
    (hcolumns : columns.size = numColumns)
    (hrows : ∀ column (hcolumn : column < columns.size),
      columns[column].size = numRows)
    (assignment : FixedAssignment F) (hassignment : assignment ∈ assignments)
    (hnodup : (assignments.map FixedAssignment.cell).Nodup)
    (hcolumn : assignment.1 < numColumns)
    (hrow : assignment.2.1 < numRows) :
    fixedCell? (assignments.foldl (scatterFixed numColumns) columns)
        assignment.1 assignment.2.1 =
      some assignment.2.2 := by
  induction assignments generalizing columns with
  | nil => simp at hassignment
  | cons current rest inductionHypothesis =>
      have hrestNodup : (rest.map FixedAssignment.cell).Nodup :=
        (List.nodup_cons.mp hnodup).2
      rcases List.mem_cons.mp hassignment with hcurrent | hrest
      · subst current
        simp only [List.foldl_cons]
        rw [fixedCell?_scatterFixed_fold_eq_of_forall_cell_ne rest]
        · rw [fixedCell?_scatterFixed hcolumns hrows assignment
              assignment.1 assignment.2.1 hcolumn hrow]
          simp [FixedAssignment.cell]
        · exact (scatterFixed_sized hcolumns hrows assignment).1
        · exact (scatterFixed_sized hcolumns hrows assignment).2
        · exact hcolumn
        · exact hrow
        · intro remaining hremaining hequal
          exact (List.nodup_cons.mp hnodup).1
            (List.mem_map.mpr ⟨remaining, hremaining, hequal⟩)
      · simp only [List.foldl_cons]
        have hnext := scatterFixed_sized hcolumns hrows current
        exact inductionHypothesis hnext.1 hnext.2 hrest hrestNodup

/-- Dense compilation emits exactly the requested number of fixed columns. -/
@[simp] theorem denseFixedColumns_length [Zero F]
    (numRows numColumns : ℕ)
    (assignments : List (FixedAssignment F)) :
    (denseFixedColumns numRows numColumns assignments).length = numColumns := by
  let initial : Array (Array F) :=
    Array.replicate numColumns (Array.replicate numRows 0)
  let result := assignments.foldl (scatterFixed numColumns) initial
  have hshape := scatterFixed_fold_sized assignments
    (columns := initial) (numRows := numRows) (numColumns := numColumns)
    (by simp [initial]) (by simp [initial])
  simpa [denseFixedColumns, initial, result] using hshape.1

/-- Every in-range dense fixed column spans the requested row count. -/
theorem denseFixedColumns_getD_length [Zero F]
    (numRows numColumns : ℕ)
    (assignments : List (FixedAssignment F))
    (column : ℕ) (hcolumn : column < numColumns) :
    ((denseFixedColumns numRows numColumns assignments).getD column []).length =
      numRows := by
  let initial : Array (Array F) :=
    Array.replicate numColumns (Array.replicate numRows 0)
  let result := assignments.foldl (scatterFixed numColumns) initial
  have hshape := scatterFixed_fold_sized assignments
    (columns := initial) (numRows := numRows) (numColumns := numColumns)
    (by simp [initial]) (by simp [initial])
  have hresultColumn : column < result.size := by
    rw [hshape.1]
    exact hcolumn
  rw [List.getD_eq_getElem _ _ (by
    simpa only [denseFixedColumns_length] using hcolumn)]
  simp only [denseFixedColumns, List.getElem_map,
    Array.getElem_toList, Array.length_toList]
  exact hshape.2 column hresultColumn

/-- Every retained in-bounds sparse assignment is realized by dense compilation. -/
theorem denseFixedColumns_getD_getD_eq_of_mem [Zero F]
    (numRows numColumns : ℕ)
    (assignments : List (FixedAssignment F))
    (assignment : FixedAssignment F) (hassignment : assignment ∈ assignments)
    (hnodup : (assignments.map FixedAssignment.cell).Nodup)
    (hcolumn : assignment.1 < numColumns)
    (hrow : assignment.2.1 < numRows) :
    ((denseFixedColumns numRows numColumns assignments).getD assignment.1 []).getD
        assignment.2.1 0 =
      assignment.2.2 := by
  let initial : Array (Array F) :=
    Array.replicate numColumns (Array.replicate numRows 0)
  let result := assignments.foldl (scatterFixed numColumns) initial
  have hshape := scatterFixed_fold_sized assignments
    (columns := initial) (numRows := numRows) (numColumns := numColumns)
    (by simp [initial]) (by simp [initial])
  have hresultColumn : assignment.1 < result.size := by
    rw [hshape.1]
    exact hcolumn
  have hresultRow : assignment.2.1 < result[assignment.1].size := by
    rw [hshape.2 assignment.1 hresultColumn]
    exact hrow
  have hrealizes := fixedCell?_scatterFixed_fold_eq_of_mem assignments
    (columns := initial) (numRows := numRows) (numColumns := numColumns)
    (by simp [initial]) (by simp [initial]) assignment hassignment hnodup
    hcolumn hrow
  have hvalue : result[assignment.1][assignment.2.1] = assignment.2.2 := by
    simp only [fixedCell?] at hrealizes
    rw [Array.getElem?_eq_getElem hresultColumn, Option.bind_some,
      Array.getElem?_eq_getElem hresultRow] at hrealizes
    exact Option.some.inj hrealizes
  have hdenseColumn :
      assignment.1 < (denseFixedColumns numRows numColumns assignments).length := by
    simpa only [denseFixedColumns_length] using hcolumn
  rw [List.getD_eq_getElem _ _ hdenseColumn]
  have hdenseRow : assignment.2.1 <
      (denseFixedColumns numRows numColumns assignments)[assignment.1].length := by
    simpa only [denseFixedColumns, List.getElem_map, Array.getElem_toList,
      Array.length_toList, initial, result] using hresultRow
  rw [List.getD_eq_getElem _ _ hdenseRow]
  simpa only [denseFixedColumns, List.getElem_map, Array.getElem_toList,
    initial, result] using hvalue

end Halo2.Layout
