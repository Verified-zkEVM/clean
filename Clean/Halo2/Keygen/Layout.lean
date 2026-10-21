import Clean.Halo2.Keygen.CompressSelectors
import Clean.Halo2.Keygen.FloorPlanner.ConstantAllocation
import Clean.Halo2.Operations.FixedWrites
import Batteries.Data.Array.Lemmas
import Mathlib.Data.List.GetD
import Std.Data.HashSet.Lemmas

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

/-- Every pair of writes to one fixed cell carries the same value. -/
def FixedAssignmentsAgree
    (assignments : List (FixedAssignment F)) : Prop :=
  ∀ ⦃left right : FixedAssignment F⦄,
    left ∈ assignments →
    right ∈ assignments →
    left.cell = right.cell →
    left.2.2 = right.2.2

/-- Cell uniqueness is a sufficient, stronger fixed-write discipline. -/
theorem FixedAssignmentsAgree.of_cells_nodup
    {assignments : List (FixedAssignment F)}
    (hnodup : (assignments.map FixedAssignment.cell).Nodup) :
    FixedAssignmentsAgree assignments := by
  induction assignments with
  | nil => simp [FixedAssignmentsAgree]
  | cons head rest inductionHypothesis =>
      rw [List.map_cons, List.nodup_cons] at hnodup
      intro left right hleft hright hcell
      simp only [List.mem_cons] at hleft hright
      rcases hleft with rfl | hleft <;> rcases hright with rfl | hright
      · rfl
      · exfalso
        exact hnodup.1 (List.mem_map.mpr ⟨right, hright, hcell.symm⟩)
      · exfalso
        exact hnodup.1 (List.mem_map.mpr ⟨left, hleft, hcell⟩)
      · exact inductionHypothesis hnodup.2 hleft hright hcell

/-- Agreement composes when the two assignment streams occupy disjoint cells. -/
theorem FixedAssignmentsAgree.append_of_disjoint_cells
    {left right : List (FixedAssignment F)}
    (hleft : FixedAssignmentsAgree left)
    (hright : FixedAssignmentsAgree right)
    (hdisjoint : (left.map FixedAssignment.cell).Disjoint
      (right.map FixedAssignment.cell)) :
    FixedAssignmentsAgree (left ++ right) := by
  intro first second hfirst hsecond hcell
  rw [List.mem_append] at hfirst hsecond
  rcases hfirst with hfirst | hfirst <;>
    rcases hsecond with hsecond | hsecond
  · exact hleft hfirst hsecond hcell
  · exfalso
    exact List.disjoint_left.mp hdisjoint
      (List.mem_map.mpr ⟨first, hfirst, rfl⟩)
      (List.mem_map.mpr ⟨second, hsecond, hcell.symm⟩)
  · exfalso
    exact List.disjoint_left.mp hdisjoint
      (List.mem_map.mpr ⟨second, hsecond, rfl⟩)
      (List.mem_map.mpr ⟨first, hfirst, hcell⟩)
  · exact hright hfirst hsecond hcell

private theorem fixedColumn_eq_of_index_eq
    {left right : Column .fixed} (hindex : left.index = right.index) :
    left = right := by
  cases left
  cases right
  simp_all

/-- One loaded table column, including Halo2's default-fill over all usable rows. -/
def tableColumnAssignments (usable column : ℕ) (values : List F) :
    List (FixedAssignment F) :=
  let block := values.zipIdx.map fun (value, row) => (column, row, value)
  let fill := match values with
    | [] => []
    | first :: _ =>
        (List.range (usable - values.length)).map fun row =>
          (column, values.length + row, first)
  block ++ fill

/-- Loaded-table assignments, including Halo2's default-fill over all usable rows. -/
def tableAssignments (usable : ℕ) : Operations F → List (FixedAssignment F)
  | [] => []
  | .loadTable table values :: rest =>
      tableColumnAssignments usable table.inner.index values ++
        tableAssignments usable rest
  | _ :: rest => tableAssignments usable rest

private theorem mem_tableColumnAssignments
    (usable column : ℕ) (values : List F)
    {assignment : FixedAssignment F}
    (hassignment : assignment ∈
      tableColumnAssignments usable column values) :
    assignment.1 = column ∧
      ∃ first rest,
        values = first :: rest ∧
          assignment.2.2 = values.getD assignment.2.1 first := by
  rcases values with _ | ⟨first, rest⟩
  · simp [tableColumnAssignments] at hassignment
  · simp only [tableColumnAssignments, List.mem_append] at hassignment
    rcases hassignment with hblock | hfill
    · rw [List.mem_map] at hblock
      obtain ⟨⟨value, row⟩, hrow, rfl⟩ := hblock
      refine ⟨rfl, first, rest, rfl, ?_⟩
      have hrowBound : row < (first :: rest).length := by
        simpa using (List.mem_zipIdx hrow).2.1
      change value = (first :: rest).getD row first
      rw [List.getD_eq_getElem _ _ hrowBound]
      simpa using List.fst_eq_of_mem_zipIdx hrow
    · rw [List.mem_map] at hfill
      obtain ⟨row, hrow, rfl⟩ := hfill
      refine ⟨rfl, first, rest, rfl, ?_⟩
      change first = (first :: rest).getD ((first :: rest).length + row) first
      symm
      apply List.getD_eq_default
      omega

/-- Assignments emitted for one loaded table column are unambiguous. -/
theorem tableColumnAssignments_agree
    (usable column : ℕ) (values : List F) :
    FixedAssignmentsAgree (tableColumnAssignments usable column values) := by
  intro left right hleft hright hcell
  obtain ⟨_, first, rest, hvalues, hleftValue⟩ :=
    mem_tableColumnAssignments usable column values hleft
  obtain ⟨_, otherFirst, otherRest, hvalues', hrightValue⟩ :=
    mem_tableColumnAssignments usable column values hright
  injection hvalues.symm.trans hvalues' with hfirst _
  rw [hleftValue, hrightValue, ← hfirst]
  exact congrArg (fun row => values.getD row first)
    (congrArg Prod.snd hcell)

private theorem tableAssignment_column_mem_loadedTableColumns
    (usable : ℕ) (operations : Operations F)
    {assignment : FixedAssignment F}
    (hassignment : assignment ∈ tableAssignments usable operations) :
    (Column.mk assignment.1 : Column .fixed) ∈
      operations.loadedTableColumns := by
  induction operations with
  | nil => simp [tableAssignments] at hassignment
  | cons operation rest inductionHypothesis =>
      cases operation with
      | region name body | constrainInstance cell column row =>
          exact inductionHypothesis hassignment
      | loadTable table values =>
          simp only [tableAssignments, List.mem_append] at hassignment
          rcases hassignment with hcurrent | hrest
          · obtain ⟨hcolumn, first, tail, hvalues, _⟩ :=
              mem_tableColumnAssignments usable table.inner.index values hcurrent
            subst values
            rw [Operations.loadedTableColumns_loadTable_cons]
            simp only [List.cons_ne_nil, ↓reduceIte, List.singleton_append,
              List.mem_cons]
            left
            exact fixedColumn_eq_of_index_eq hcolumn
          · rw [Operations.loadedTableColumns_loadTable_cons]
            by_cases hvalues : values = []
            · simp only [hvalues, ↓reduceIte, List.nil_append]
              exact inductionHypothesis hrest
            · simp only [hvalues, ↓reduceIte, List.singleton_append,
                List.mem_cons]
              exact Or.inr (inductionHypothesis hrest)

/-- Distinct loaded table columns and per-column fill semantics make the complete table
assignment stream unambiguous. -/
theorem tableAssignments_agree
    (usable : ℕ) (operations : Operations F)
    (hnodup : operations.loadedTableColumns.Nodup) :
    FixedAssignmentsAgree (tableAssignments usable operations) := by
  induction operations with
  | nil => simp [tableAssignments, FixedAssignmentsAgree]
  | cons operation rest inductionHypothesis =>
      cases operation with
      | region name body | constrainInstance cell column row =>
          apply inductionHypothesis
          simpa using hnodup
      | loadTable table values =>
          by_cases hvalues : values = []
          · subst values
            apply inductionHypothesis
            simpa using hnodup
          · rw [Operations.loadedTableColumns_loadTable_cons,
              if_neg hvalues, List.singleton_append,
              List.nodup_cons] at hnodup
            intro left right hleft hright hcell
            simp only [tableAssignments, List.mem_append] at hleft hright
            rcases hleft with hleft | hleft <;>
              rcases hright with hright | hright
            · exact tableColumnAssignments_agree usable table.inner.index values
                hleft hright hcell
            · obtain ⟨hleftColumn, _, _, _, _⟩ :=
                mem_tableColumnAssignments usable table.inner.index values hleft
              have hrightColumn :=
                tableAssignment_column_mem_loadedTableColumns usable rest hright
              exfalso
              simp only [FixedAssignment.cell] at hcell
              have hcolumnsEqual :
                  (Column.mk right.1 : Column .fixed) = table.inner :=
                fixedColumn_eq_of_index_eq
                  ((congrArg Prod.fst hcell).symm.trans hleftColumn)
              apply hnodup.1
              rwa [← hcolumnsEqual]
            · obtain ⟨hrightColumn, _, _, _, _⟩ :=
                mem_tableColumnAssignments usable table.inner.index values hright
              have hleftColumn :=
                tableAssignment_column_mem_loadedTableColumns usable rest hleft
              exfalso
              simp only [FixedAssignment.cell] at hcell
              have hcolumnsEqual :
                  (Column.mk left.1 : Column .fixed) = table.inner :=
                fixedColumn_eq_of_index_eq
                  ((congrArg Prod.fst hcell).trans hrightColumn)
              apply hnodup.1
              rwa [← hcolumnsEqual]
            · exact inductionHypothesis hnodup.2 hleft hright hcell

/-- Region-level `assignFixed` operations at their V1-placed absolute rows. -/
def regionAssignments (starts : List ℕ)
    (regions : List (ℕ × RegionOperations F)) : List (FixedAssignment F) :=
  regions.flatMap fun (index, body) =>
    body.filterMap fun operation =>
      match operation with
      | .assignFixed column row value =>
          some (column.index, place starts index + row, value)
      | _ => none

private theorem mem_regionAssignments
    (starts : List ℕ) (regions : List (ℕ × RegionOperations F))
    {assignment : FixedAssignment F}
    (hassignment : assignment ∈ regionAssignments starts regions) :
    ∃ index body column localRow,
      (index, body) ∈ regions ∧
        .assignFixed column localRow assignment.2.2 ∈ body ∧
        assignment.1 = column.index ∧
        assignment.2.1 = place starts index + localRow := by
  rw [regionAssignments, List.mem_flatMap] at hassignment
  obtain ⟨⟨index, body⟩, hregion, hbody⟩ := hassignment
  rw [List.mem_filterMap] at hbody
  obtain ⟨operation, hoperation, hmapped⟩ := hbody
  cases operation with
  | assignFixed column row value =>
      simp only [Option.some.injEq] at hmapped
      obtain ⟨rfl, rfl, rfl⟩ := hmapped
      exact ⟨index, body, column, row, hregion, hoperation, rfl, rfl⟩
  | assignAdvice | constrainEqual | constrainConstant | constrainInstance |
      enableGate | enableLookup =>
      simp at hmapped

/-- V1 placement and region-local agreement make all placed region assignments
unambiguous. -/
theorem regionAssignments_agree
    (operations : Operations F)
    (hregions : operations.Forall Operation.FixedAssignmentsAgree) :
    FixedAssignmentsAgree
      (regionAssignments (FloorPlanner.V1.starts operations)
        (indexedRegions operations 0).1) := by
  intro left right hleft hright hcell
  obtain ⟨leftIndex, leftBody, leftColumn, leftRow,
    hleftRegion, hleftOperation, hleftColumn, hleftRow⟩ :=
      mem_regionAssignments _ _ hleft
  obtain ⟨rightIndex, rightBody, rightColumn, rightRow,
    hrightRegion, hrightOperation, hrightColumn, hrightRow⟩ :=
      mem_regionAssignments _ _ hright
  have hcolumnIndex : leftColumn.index = rightColumn.index := by
    simp only [FixedAssignment.cell] at hcell
    exact hleftColumn.symm.trans
      ((congrArg Prod.fst hcell).trans hrightColumn)
  have hcolumn : leftColumn = rightColumn :=
    fixedColumn_eq_of_index_eq hcolumnIndex
  subst rightColumn
  by_cases hindex : leftIndex = rightIndex
  · have hpairs := FloorPlanner.indexedRegions_eq_of_index_eq
      operations 0 hleftRegion hrightRegion hindex
    have hbody : leftBody = rightBody := congrArg Prod.snd hpairs
    subst rightBody
    subst rightIndex
    simp only [FixedAssignment.cell] at hcell
    have hrow : leftRow = rightRow := by
      have habsolute := hleftRow.symm.trans
        ((congrArg Prod.snd hcell).trans hrightRow)
      omega
    subst rightRow
    obtain ⟨name, hsource⟩ :=
      exists_region_mem_of_mem_indexedRegions operations 0 hleftRegion
    have hagrees :=
      List.forall_iff_forall_mem.mp hregions (.region name leftBody) hsource
    exact hagrees leftColumn leftRow left.2.2 right.2.2
      hleftOperation hrightOperation
  · have hleftShape :
        FloorPlanner.measureRegion leftIndex leftBody ∈
          FloorPlanner.measureRegions operations :=
      List.mem_map.mpr ⟨(leftIndex, leftBody), hleftRegion, rfl⟩
    have hrightShape :
        FloorPlanner.measureRegion rightIndex rightBody ∈
          FloorPlanner.measureRegions operations :=
      List.mem_map.mpr ⟨(rightIndex, rightBody), hrightRegion, rfl⟩
    have hleftColumnMeasured :
        .column .fixed leftColumn.index ∈
          (FloorPlanner.measureRegion leftIndex leftBody).columns := by
      rw [FloorPlanner.mem_measureRegion_columns_iff]
      apply RegionOperations.mem_synthesisSummary_columns_of_mem_fixedColumns
      rw [RegionOperations.fixedColumns, List.mem_filterMap]
      exact ⟨.assignFixed leftColumn leftRow left.2.2,
        hleftOperation, rfl⟩
    have hrightColumnMeasured :
        .column .fixed leftColumn.index ∈
          (FloorPlanner.measureRegion rightIndex rightBody).columns := by
      rw [FloorPlanner.mem_measureRegion_columns_iff]
      apply RegionOperations.mem_synthesisSummary_columns_of_mem_fixedColumns
      rw [RegionOperations.fixedColumns, List.mem_filterMap]
      exact ⟨.assignFixed leftColumn rightRow right.2.2,
        hrightOperation, rfl⟩
    have hleftRowBound :
        leftRow < (FloorPlanner.measureRegion leftIndex leftBody).rowCount := by
      have := FloorPlanner.regionOperationRowExtent_le_synthesisSummary_of_mem
        leftBody (.assignFixed leftColumn leftRow left.2.2) hleftOperation
      simpa only [FloorPlanner.measureRegion_rowCount,
        FloorPlanner.regionOperationRowExtent] using this
    have hrightRowBound :
        rightRow < (FloorPlanner.measureRegion rightIndex rightBody).rowCount := by
      have := FloorPlanner.regionOperationRowExtent_le_synthesisSummary_of_mem
        rightBody (.assignFixed leftColumn rightRow right.2.2) hrightOperation
      simpa only [FloorPlanner.measureRegion_rowCount,
        FloorPlanner.regionOperationRowExtent] using this
    have hdisjoint := FloorPlanner.V1.starts_sharedColumnIntervalsDisjoint operations
      hleftShape hrightShape hindex hleftColumnMeasured hrightColumnMeasured
    simp only [FixedAssignment.cell] at hcell
    have habsolute :
        (FloorPlanner.V1.starts operations).getD leftIndex 0 + leftRow =
          (FloorPlanner.V1.starts operations).getD rightIndex 0 + rightRow := by
      exact hleftRow.symm.trans
        ((congrArg Prod.snd hcell).trans hrightRow)
    unfold FloorPlanner.RowIntervalsDisjoint at hdisjoint
    simp only [FloorPlanner.measureRegion] at hdisjoint hleftRowBound hrightRowBound
    exfalso
    rcases hdisjoint with hleftBefore | hrightBefore
    · have hinside := Nat.add_lt_add_left hleftRowBound
          ((FloorPlanner.V1.starts operations).getD leftIndex 0)
      rw [habsolute] at hinside
      exact (Nat.not_lt_of_ge
        (hleftBefore.trans (Nat.le_add_right
          ((FloorPlanner.V1.starts operations).getD rightIndex 0) rightRow)))
        hinside
    · have hinside := Nat.add_lt_add_left hrightRowBound
          ((FloorPlanner.V1.starts operations).getD rightIndex 0)
      rw [← habsolute] at hinside
      exact (Nat.not_lt_of_ge
        (hrightBefore.trans (Nat.le_add_right
          ((FloorPlanner.V1.starts operations).getD leftIndex 0) leftRow)))
        hinside

/-- V1 deferred constants as ordinary fixed-cell assignments. -/
def constantAssignments
    (assignments : List (F × ℕ × ℕ)) : List (FixedAssignment F) :=
  assignments.map fun (value, column, row) => (column, row, value)

/-- V1 deferred-constant assignments are unambiguous when the configured constants
columns are unique. -/
theorem constantAssignments_agree
    (operations : Operations F) (constantColumns : List (Column .fixed))
    (hcolumns : constantColumns.Nodup) :
    FixedAssignmentsAgree
      (constantAssignments
        (FloorPlanner.V1.constantAssignments operations
          (constantColumns.map (·.index)))) := by
  apply FixedAssignmentsAgree.of_cells_nodup
  have hindices : (constantColumns.map (·.index)).Nodup := by
    apply List.Nodup.map
    · intro left right hindex
      exact fixedColumn_eq_of_index_eq hindex
    · exact hcolumns
  simpa only [constantAssignments, List.map_map,
    FixedAssignment.cell, Function.comp_apply] using
      FloorPlanner.V1.constantAssignments_cells_nodup operations
        (constantColumns.map (·.index)) hindices

private theorem exists_constantAssignment_of_mem
    (assignments : List (F × ℕ × ℕ))
    {assignment : FixedAssignment F}
    (hassignment : assignment ∈ constantAssignments assignments) :
    ∃ value,
      (value, assignment.1, assignment.2.1) ∈ assignments ∧
        assignment.2.2 = value := by
  rw [constantAssignments, List.mem_map] at hassignment
  obtain ⟨⟨value, column, row⟩, hsource, hequal⟩ := hassignment
  rcases assignment with ⟨assignedColumn, assignedRow, assignedValue⟩
  simp only [Prod.mk.injEq] at hequal
  rcases hequal with ⟨rfl, rfl, rfl⟩
  exact ⟨value, hsource, rfl⟩

private theorem regionAssignment_column_mem_regionFixedColumns
    (operations : Operations F)
    {assignment : FixedAssignment F}
    (hassignment : assignment ∈
      regionAssignments (FloorPlanner.V1.starts operations)
        (indexedRegions operations 0).1) :
    (Column.mk assignment.1 : Column .fixed) ∈
      operations.regionFixedColumns := by
  obtain ⟨index, body, column, localRow,
    hregion, hoperation, hcolumn, _⟩ :=
      mem_regionAssignments _ _ hassignment
  obtain ⟨name, hsource⟩ :=
    exists_region_mem_of_mem_indexedRegions operations 0 hregion
  rw [Operations.regionFixedColumns, List.mem_flatMap]
  refine ⟨.region name body, hsource, ?_⟩
  unfold RegionOperations.fixedColumns
  rw [List.mem_filterMap]
  refine ⟨.assignFixed column localRow assignment.2.2,
    hoperation, ?_⟩
  simp only
  apply congrArg some
  apply fixedColumn_eq_of_index_eq (left := column)
    (right := Column.mk assignment.1)
  exact hcolumn.symm

private theorem rowOccupied_eq_true_of_mem_regionAssignment
    (operations : Operations F)
    {assignment : FixedAssignment F}
    (hassignment : assignment ∈
      regionAssignments (FloorPlanner.V1.starts operations)
        (indexedRegions operations 0).1) :
    FloorPlanner.V1.rowOccupied operations
      (.column .fixed assignment.1) assignment.2.1 = true := by
  obtain ⟨index, body, column, localRow,
    hregion, hoperation, hcolumn, hrow⟩ :=
      mem_regionAssignments _ _ hassignment
  have hshape : FloorPlanner.measureRegion index body ∈
      FloorPlanner.measureRegions operations :=
    List.mem_map.mpr ⟨(index, body), hregion, rfl⟩
  have hshapeColumn : .column .fixed column.index ∈
      (FloorPlanner.measureRegion index body).columns := by
    rw [FloorPlanner.mem_measureRegion_columns_iff]
    apply RegionOperations.mem_synthesisSummary_columns_of_mem_fixedColumns
    rw [RegionOperations.fixedColumns, List.mem_filterMap]
    exact ⟨.assignFixed column localRow assignment.2.2,
      hoperation, rfl⟩
  have hlocalRow : localRow <
      (FloorPlanner.measureRegion index body).rowCount := by
    have hbound := FloorPlanner.regionOperationRowExtent_le_synthesisSummary_of_mem
      body (.assignFixed column localRow assignment.2.2) hoperation
    simpa only [FloorPlanner.measureRegion_rowCount,
      FloorPlanner.regionOperationRowExtent] using hbound
  rw [FloorPlanner.V1.rowOccupied,
    FloorPlanner.V1.rowOccupiedIn_eq_true_iff_mem_occupiedRowsIn,
    FloorPlanner.V1.mem_occupiedRowsIn_iff]
  refine ⟨FloorPlanner.measureRegion index body, hshape, ?_, ?_, ?_⟩
  · simpa [hcolumn] using hshapeColumn
  · change (FloorPlanner.V1.starts operations).getD index 0 ≤
        assignment.2.1
    rw [hrow]
    exact Nat.le_add_right _ _
  · change assignment.2.1 <
        (FloorPlanner.V1.starts operations).getD index 0 +
          (FloorPlanner.measureRegion index body).rowCount
    rw [hrow]
    exact Nat.add_lt_add_left hlocalRow _

private theorem tableAssignments_regionAssignments_cells_disjoint
    (usable : ℕ) (operations : Operations F)
    (constantColumns : List (Column .fixed))
    (hlawful : operations.FixedWritesLawful constantColumns) :
    (tableAssignments usable operations).map FixedAssignment.cell |>.Disjoint
      ((regionAssignments (FloorPlanner.V1.starts operations)
        (indexedRegions operations 0).1).map FixedAssignment.cell) := by
  rw [List.disjoint_left]
  intro cell htable hregion
  obtain ⟨tableAssignment, htableAssignment, htableCell⟩ :=
    List.mem_map.mp htable
  obtain ⟨regionAssignment, hregionAssignment, hregionCell⟩ :=
    List.mem_map.mp hregion
  have htableColumn := tableAssignment_column_mem_loadedTableColumns
    usable operations htableAssignment
  have hregionColumn := regionAssignment_column_mem_regionFixedColumns
    operations hregionAssignment
  apply List.disjoint_left.mp
    hlawful.loadedTableColumns_disjoint_regionFixedColumns
    htableColumn
  have hcolumn : tableAssignment.1 = regionAssignment.1 := by
    have hcelleq := htableCell.trans hregionCell.symm
    simp only [FixedAssignment.cell, Prod.mk.injEq] at hcelleq
    exact hcelleq.1
  simpa [hcolumn] using hregionColumn

private theorem tableAssignments_constantAssignments_cells_disjoint
    (usable : ℕ) (operations : Operations F)
    (constantColumns : List (Column .fixed))
    (hlawful : operations.FixedWritesLawful constantColumns) :
    (tableAssignments usable operations).map FixedAssignment.cell |>.Disjoint
      ((constantAssignments
        (FloorPlanner.V1.constantAssignments operations
          (constantColumns.map (·.index)))).map FixedAssignment.cell) := by
  rw [List.disjoint_left]
  intro cell htable hconstant
  obtain ⟨tableAssignment, htableAssignment, htableCell⟩ :=
    List.mem_map.mp htable
  obtain ⟨constantAssignment, hconstantAssignment, hconstantCell⟩ :=
    List.mem_map.mp hconstant
  obtain ⟨value, hsource, _⟩ :=
    exists_constantAssignment_of_mem _ hconstantAssignment
  have htableColumn := tableAssignment_column_mem_loadedTableColumns
    usable operations htableAssignment
  have hconstantIndex := FloorPlanner.V1.constantAssignments_column_mem
    operations (constantColumns.map (·.index)) hsource
  obtain ⟨constantColumn, hconstantColumn, hindex⟩ :=
    List.mem_map.mp hconstantIndex
  apply List.disjoint_left.mp
    hlawful.loadedTableColumns_disjoint_constantColumns
    htableColumn
  have hcolumn : tableAssignment.1 = constantAssignment.1 := by
    have hcelleq := htableCell.trans hconstantCell.symm
    simp only [FixedAssignment.cell, Prod.mk.injEq] at hcelleq
    exact hcelleq.1
  have hcolumnsEqual :
      (Column.mk tableAssignment.1 : Column .fixed) = constantColumn := by
    apply fixedColumn_eq_of_index_eq
      (left := Column.mk tableAssignment.1) (right := constantColumn)
    exact hcolumn.trans hindex.symm
  rwa [hcolumnsEqual]

private theorem constantAssignments_regionAssignments_cells_disjoint
    (operations : Operations F) (constantColumns : List (Column .fixed)) :
    (constantAssignments
      (FloorPlanner.V1.constantAssignments operations
        (constantColumns.map (·.index)))).map FixedAssignment.cell |>.Disjoint
      ((regionAssignments (FloorPlanner.V1.starts operations)
        (indexedRegions operations 0).1).map FixedAssignment.cell) := by
  rw [List.disjoint_left]
  intro cell hconstant hregion
  obtain ⟨constantAssignment, hconstantAssignment, hconstantCell⟩ :=
    List.mem_map.mp hconstant
  obtain ⟨regionAssignment, hregionAssignment, hregionCell⟩ :=
    List.mem_map.mp hregion
  obtain ⟨value, hsource, _⟩ :=
    exists_constantAssignment_of_mem _ hconstantAssignment
  have hfree := FloorPlanner.V1.constantAssignments_row_not_occupied
    operations (constantColumns.map (·.index)) hsource
  have hoccupied := rowOccupied_eq_true_of_mem_regionAssignment
    operations hregionAssignment
  have hcellEq : constantAssignment.cell = regionAssignment.cell :=
    hconstantCell.trans hregionCell.symm
  simp only [FixedAssignment.cell, Prod.mk.injEq] at hcellEq
  rw [hcellEq.1, hcellEq.2, hoccupied] at hfree
  simp at hfree

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

private theorem mem_foldl_hashSet_insert_iff
    (item : ℕ × ℕ) (items : List (ℕ × ℕ))
    (initial : Std.HashSet (ℕ × ℕ)) :
    item ∈ items.foldl (fun set next => set.insert next) initial ↔
      item ∈ initial ∨ item ∈ items := by
  induction items generalizing initial with
  | nil => simp
  | cons head tail inductionHypothesis =>
      rw [List.foldl_cons, inductionHypothesis]
      simp only [Std.HashSet.mem_insert, beq_iff_eq, List.mem_cons]
      aesop

/-- Every activated selector with a compression-map entry is emitted as the
corresponding packed fixed assignment. -/
theorem mem_selectorAssignments_of_activation [FiniteField F]
    (selectorMap : SelCompressMap) (selectorActivations : List (ℕ × ℕ))
    {selector row : ℕ} {compressed : SelCompress}
    (hactivation : (selector, row) ∈ selectorActivations)
    (hlookup : selectorMap.lookup selector = some compressed) :
    (compressed.packedCol, row,
      (FiniteField.fromNat compressed.assignedRoot : F)) ∈
        selectorAssignments selectorMap selectorActivations := by
  simp only [SelCompressMap.lookup, Option.map_eq_some_iff] at hlookup
  obtain ⟨entry, hfind, hcompressed⟩ := hlookup
  unfold selectorAssignments
  rw [List.mem_filterMap]
  refine ⟨(selector, row), ?_, ?_⟩
  · rw [Std.HashSet.mem_toList, mem_foldl_hashSet_insert_iff]
    exact Or.inr hactivation
  · simp only [hfind, Option.map_some]
    rw [← hcompressed]

/-- Every packed selector assignment retains its source activation and map entry. -/
theorem exists_activation_lookup_of_mem_selectorAssignments [FiniteField F]
    (selectorMap : SelCompressMap) (selectorActivations : List (ℕ × ℕ))
    {assignment : FixedAssignment F}
    (hassignment : assignment ∈
      selectorAssignments selectorMap selectorActivations) :
    ∃ selector row compressed,
      (selector, row) ∈ selectorActivations ∧
        selectorMap.lookup selector = some compressed ∧
        assignment = (compressed.packedCol, row,
          FiniteField.fromNat compressed.assignedRoot) := by
  unfold selectorAssignments at hassignment
  rw [List.mem_filterMap] at hassignment
  obtain ⟨⟨selector, row⟩, hunique, hmapped⟩ := hassignment
  rw [Std.HashSet.mem_toList, mem_foldl_hashSet_insert_iff] at hunique
  have hactivation : (selector, row) ∈ selectorActivations := by
    exact hunique.resolve_left (by simp)
  simp only [Option.map_eq_some_iff] at hmapped
  obtain ⟨entry, hfind, hresult⟩ := hmapped
  rcases entry with ⟨sourceSelector, compressed⟩
  have hselector : sourceSelector = selector := by
    have hpredicate : decide (sourceSelector = selector) = true := by
      exact List.find?_some
        (p := fun candidate : ℕ × SelCompress => candidate.1 = selector) hfind
    exact of_decide_eq_true hpredicate
  subst sourceSelector
  refine ⟨selector, row, compressed, hactivation, ?_, hresult.symm⟩
  exact congrArg (Option.map Prod.snd) hfind

/-- Circuit-derived selector assignments are unambiguous: the packer only shares a
fixed column between selectors that never activate on the same row. -/
theorem selectorAssignments_agree_deriveSelCompressMap [FiniteField F]
    (constraintSystem : ConstraintSystem F) (n : ℕ)
    (selectorActivations : List (ℕ × ℕ))
    (hrows : ∀ activation ∈ selectorActivations, activation.2 < n) :
    FixedAssignmentsAgree
      (selectorAssignments (F := F)
        (deriveSelCompressMap constraintSystem n selectorActivations)
        selectorActivations) := by
  intro left right hleft hright hcell
  obtain ⟨leftSelector, leftRow, leftCompressed,
    hleftActivation, hleftLookup, rfl⟩ :=
      exists_activation_lookup_of_mem_selectorAssignments
        (deriveSelCompressMap constraintSystem n selectorActivations)
        selectorActivations hleft
  obtain ⟨rightSelector, rightRow, rightCompressed,
    hrightActivation, hrightLookup, rfl⟩ :=
      exists_activation_lookup_of_mem_selectorAssignments
        (deriveSelCompressMap constraintSystem n selectorActivations)
        selectorActivations hright
  simp only [FixedAssignment.cell, Prod.mk.injEq] at hcell
  have hrow : leftRow < n :=
    hrows (leftSelector, leftRow) hleftActivation
  have hroots := deriveSelCompressMap_lookup_roots_agree_of_activated
    constraintSystem n selectorActivations hrow hleftActivation
      (by simpa [hcell.2] using hrightActivation)
      hleftLookup hrightLookup hcell.1
  exact congrArg FiniteField.fromNat hroots

private theorem tableAssignment_column_lt_numFixedColumns
    (usable : ℕ) (constraintSystem : ConstraintSystem F)
    (operations : Operations F)
    (hcoherent : OperationsKeygenCoherent constraintSystem operations)
    {assignment : FixedAssignment F}
    (hassignment : assignment ∈ tableAssignments usable operations) :
    assignment.1 < constraintSystem.numFixedColumns := by
  induction operations with
  | nil => simp [tableAssignments] at hassignment
  | cons operation rest inductionHypothesis =>
      cases operation with
      | region name body =>
          rw [OperationsKeygenCoherent.region_cons] at hcoherent
          exact inductionHypothesis hcoherent.2 hassignment
      | constrainInstance cell column row =>
          rw [OperationsKeygenCoherent.constrainInstance_cons] at hcoherent
          exact inductionHypothesis hcoherent.2.2 hassignment
      | loadTable table values =>
          rw [OperationsKeygenCoherent.loadTable_cons] at hcoherent
          simp only [tableAssignments, List.mem_append] at hassignment
          rcases hassignment with hcurrent | hrest
          · obtain ⟨hcolumn, _, _, _, _⟩ :=
              mem_tableColumnAssignments usable table.inner.index values hcurrent
            have htableBound :=
              (ConstraintSystem.mem_fixedColumns_iff
                constraintSystem table.inner).mp hcoherent.1
            omega
          · exact inductionHypothesis hcoherent.2 hrest

private theorem regionAssignment_column_lt_numFixedColumns
    (constraintSystem : ConstraintSystem F) (operations : Operations F)
    (hcoherent : OperationsKeygenCoherent constraintSystem operations)
    {assignment : FixedAssignment F}
    (hassignment : assignment ∈
      regionAssignments (FloorPlanner.V1.starts operations)
        (indexedRegions operations 0).1) :
    assignment.1 < constraintSystem.numFixedColumns := by
  have hcolumn := regionAssignment_column_mem_regionFixedColumns
    operations hassignment
  have hregistered : operations.KeygenRegistered constraintSystem.gates
      constraintSystem.lookups constraintSystem.fixedColumns
      constraintSystem.permutationColumns := hcoherent
  have hfixed := hregistered.mem_fixedColumns_of_mem_regionFixedColumns hcolumn
  exact (ConstraintSystem.mem_fixedColumns_iff _ _).mp hfixed

private theorem constantAssignment_column_lt_numFixedColumns
    (operations : Operations F) (constantColumns : List (Column .fixed))
    (fixedColumnCount : ℕ)
    (hcolumns : constantColumns.Forall fun column => column.index < fixedColumnCount)
    {assignment : FixedAssignment F}
    (hassignment : assignment ∈
      constantAssignments
        (FloorPlanner.V1.constantAssignments operations
          (constantColumns.map (·.index)))) :
    assignment.1 < fixedColumnCount := by
  obtain ⟨value, hsource, _⟩ :=
    exists_constantAssignment_of_mem _ hassignment
  have hcolumn := FloorPlanner.V1.constantAssignments_column_mem
    operations (constantColumns.map (·.index)) hsource
  obtain ⟨column, hcolumn, hindex⟩ := List.mem_map.mp hcolumn
  exact hindex ▸ List.forall_iff_forall_mem.mp hcolumns column hcolumn

private theorem selectorAssignment_column_ge_numFixedColumns [FiniteField F]
    (constraintSystem : ConstraintSystem F) (n : ℕ)
    (selectorActivations : List (ℕ × ℕ))
    {assignment : FixedAssignment F}
    (hassignment : assignment ∈
      selectorAssignments
        (deriveSelCompressMap constraintSystem n selectorActivations)
        selectorActivations) :
    constraintSystem.numFixedColumns ≤ assignment.1 := by
  obtain ⟨selector, row, compressed, _, hlookup, hequal⟩ :=
    exists_activation_lookup_of_mem_selectorAssignments
      (deriveSelCompressMap constraintSystem n selectorActivations)
      selectorActivations hassignment
  obtain ⟨index, _, hcolumn⟩ :=
    deriveSelCompressMap_lookup_packedColumn
      constraintSystem n selectorActivations hlookup
  rw [hequal, hcolumn]
  omega

private theorem fixedAssignment_cells_disjoint_of_column_bounds
    (left right : List (FixedAssignment F)) (bound : ℕ)
    (hleft : ∀ assignment ∈ left, assignment.1 < bound)
    (hright : ∀ assignment ∈ right, bound ≤ assignment.1) :
    (left.map FixedAssignment.cell).Disjoint
      (right.map FixedAssignment.cell) := by
  rw [List.disjoint_left]
  intro cell hleftCell hrightCell
  obtain ⟨leftAssignment, hleftAssignment, hleftEq⟩ :=
    List.mem_map.mp hleftCell
  obtain ⟨rightAssignment, hrightAssignment, hrightEq⟩ :=
    List.mem_map.mp hrightCell
  have hcolumn : leftAssignment.1 = rightAssignment.1 := by
    have hcelleq := hleftEq.trans hrightEq.symm
    simp only [FixedAssignment.cell, Prod.mk.injEq] at hcelleq
    exact hcelleq.1
  have := hleft leftAssignment hleftAssignment
  have := hright rightAssignment hrightAssignment
  omega

private theorem tableColumnAssignment_row_lt
    (usable column : ℕ) (values : List F)
    (hvalues : values.length ≤ usable)
    {assignment : FixedAssignment F}
    (hassignment : assignment ∈
      tableColumnAssignments usable column values) :
    assignment.2.1 < usable := by
  rcases values with _ | ⟨first, rest⟩
  · simp [tableColumnAssignments] at hassignment
  · simp only [tableColumnAssignments, List.mem_append] at hassignment
    rcases hassignment with hblock | hfill
    · rw [List.mem_map] at hblock
      obtain ⟨⟨value, row⟩, hrow, rfl⟩ := hblock
      change row < usable
      have hrowBound := List.snd_lt_of_mem_zipIdx hrow
      omega
    · rw [List.mem_map] at hfill
      obtain ⟨row, hrow, rfl⟩ := hfill
      change (first :: rest).length + row < usable
      have hrowBound := List.mem_range.mp hrow
      omega

private theorem tableAssignment_row_lt
    (usable : ℕ) (operations : Operations F)
    (hloads : ∀ table values, .loadTable table values ∈ operations →
      values.length ≤ usable)
    {assignment : FixedAssignment F}
    (hassignment : assignment ∈ tableAssignments usable operations) :
    assignment.2.1 < usable := by
  induction operations with
  | nil => simp [tableAssignments] at hassignment
  | cons operation rest inductionHypothesis =>
      cases operation with
      | region name body | constrainInstance cell column row =>
          apply inductionHypothesis
          · intro table values hload
            exact hloads table values (by simp [hload])
          · exact hassignment
      | loadTable table values =>
          simp only [tableAssignments, List.mem_append] at hassignment
          rcases hassignment with hcurrent | hrest
          · exact tableColumnAssignment_row_lt usable table.inner.index values
              (hloads table values (by simp)) hcurrent
          · apply inductionHypothesis
            · intro otherTable otherValues hload
              exact hloads otherTable otherValues (by simp [hload])
            · exact hrest

private theorem regionAssignment_row_lt_placementEnd
    (operations : Operations F)
    {assignment : FixedAssignment F}
    (hassignment : assignment ∈
      regionAssignments (FloorPlanner.V1.starts operations)
        (indexedRegions operations 0).1) :
    assignment.2.1 < FloorPlanner.V1.placementEnd operations := by
  obtain ⟨index, body, column, localRow,
    hregion, hoperation, _, hrow⟩ :=
      mem_regionAssignments _ _ hassignment
  have hshape : FloorPlanner.measureRegion index body ∈
      FloorPlanner.measureRegions operations :=
    List.mem_map.mpr ⟨(index, body), hregion, rfl⟩
  have hend := FloorPlanner.V1.shape_end_le_placementEndFrom_of_mem
    (FloorPlanner.measureRegions operations)
    (FloorPlanner.V1.starts operations)
    (FloorPlanner.measureRegion index body) hshape
  have hlocal : localRow <
      (FloorPlanner.measureRegion index body).rowCount := by
    have hbound := FloorPlanner.regionOperationRowExtent_le_synthesisSummary_of_mem
      body (.assignFixed column localRow assignment.2.2) hoperation
    simpa only [FloorPlanner.measureRegion_rowCount,
      FloorPlanner.regionOperationRowExtent] using hbound
  rw [hrow]
  unfold place FloorPlanner.V1.placementEnd
  exact (Nat.add_lt_add_left hlocal _).trans_le hend

private theorem selectorAssignment_bounds [FiniteField F]
    (constraintSystem : ConstraintSystem F) (n : ℕ)
    (selectorActivations : List (ℕ × ℕ))
    (hrows : ∀ activation ∈ selectorActivations, activation.2 < n)
    {assignment : FixedAssignment F}
    (hassignment : assignment ∈
      selectorAssignments
        (deriveSelCompressMap constraintSystem n selectorActivations)
        selectorActivations) :
    assignment.2.1 < n ∧
      assignment.1 < constraintSystem.numFixedColumns +
        (deriveSelCompressMap constraintSystem n selectorActivations).newFixedCols := by
  obtain ⟨selector, row, compressed, hactivation, hlookup, hequal⟩ :=
    exists_activation_lookup_of_mem_selectorAssignments
      (deriveSelCompressMap constraintSystem n selectorActivations)
      selectorActivations hassignment
  obtain ⟨index, hindex, hcolumn⟩ :=
    deriveSelCompressMap_lookup_packedColumn
      constraintSystem n selectorActivations hlookup
  rw [hequal, hcolumn]
  exact ⟨hrows (selector, row) hactivation, by omega⟩

/-- The ordered fixed-write stream before Halo 2's last-write deduplication. -/
def rawAssignments [FiniteField F]
    (usable : ℕ) (selectorMap : SelCompressMap)
    (constraintSystem : ConstraintSystem F) (operations : Operations F) :
    List (FixedAssignment F) :=
  let starts := FloorPlanner.V1.starts operations
  let regions := (indexedRegions operations 0).1
  tableAssignments usable operations
    ++ constantAssignments
      (FloorPlanner.V1.constantAssignments operations
        (constraintSystem.constants.map (·.index)))
    ++ selectorAssignments selectorMap (activations starts regions)
    ++ regionAssignments starts regions

/-- Every raw fixed write lies within the fixed-column and evaluation-domain bounds
computed from the same constraint system and operation stream. -/
theorem rawAssignments_bounds_deriveSelCompressMap [FiniteField F]
    (usable n : ℕ) (constraintSystem : ConstraintSystem F)
    (operations : Operations F)
    (hcoherent : OperationsKeygenCoherent constraintSystem operations)
    (hconstantBounds : constraintSystem.constants.Forall fun column =>
      column.index < constraintSystem.numFixedColumns)
    (hloads : ∀ table values, .loadTable table values ∈ operations →
      values.length ≤ usable)
    (husable : usable ≤ n)
    (hplacement : FloorPlanner.V1.placementEnd operations ≤ n)
    (hactivationRows : ∀ activation ∈
      activations (FloorPlanner.V1.starts operations)
        (indexedRegions operations 0).1,
      activation.2 < n)
    {assignment : FixedAssignment F}
    (hassignment : assignment ∈
      rawAssignments usable
        (deriveSelCompressMap constraintSystem n
          (activations (FloorPlanner.V1.starts operations)
            (indexedRegions operations 0).1))
        constraintSystem operations) :
    assignment.1 < constraintSystem.numFixedColumns +
        (deriveSelCompressMap constraintSystem n
          (activations (FloorPlanner.V1.starts operations)
            (indexedRegions operations 0).1)).newFixedCols ∧
      assignment.2.1 < n := by
  simp only [rawAssignments] at hassignment
  rcases List.mem_append.mp hassignment with hprefix | hregion
  rcases List.mem_append.mp hprefix with hprefix | hselector
  rcases List.mem_append.mp hprefix with htable | hconstant
  · exact ⟨(tableAssignment_column_lt_numFixedColumns usable
      constraintSystem operations hcoherent htable).trans_le (Nat.le_add_right _ _),
      (tableAssignment_row_lt usable operations hloads htable).trans_le husable⟩
  · obtain ⟨value, hsource, _⟩ :=
      exists_constantAssignment_of_mem _ hconstant
    exact ⟨(constantAssignment_column_lt_numFixedColumns operations
      constraintSystem.constants constraintSystem.numFixedColumns
      hconstantBounds hconstant).trans_le (Nat.le_add_right _ _),
      (FloorPlanner.V1.constantAssignments_row_lt_placementEnd
        operations (constraintSystem.constants.map (·.index))
        hsource).trans_le
          hplacement⟩
  · have hbounds := selectorAssignment_bounds constraintSystem n
      (activations (FloorPlanner.V1.starts operations)
        (indexedRegions operations 0).1) hactivationRows hselector
    exact ⟨hbounds.2, hbounds.1⟩
  · exact ⟨(regionAssignment_column_lt_numFixedColumns constraintSystem
      operations hcoherent hregion).trans_le (Nat.le_add_right _ _),
      (regionAssignment_row_lt_placementEnd operations hregion).trans_le hplacement⟩

/-- The four generic fixed-write sources agree under the circuit and planner laws:
tables own disjoint columns, deferred constants use region-free cells, selector
compression occupies a fresh column suffix, and region-local writes agree. -/
theorem rawAssignments_agree_deriveSelCompressMap [FiniteField F]
    (usable n : ℕ) (constraintSystem : ConstraintSystem F)
    (operations : Operations F)
    (hfixed : operations.FixedWritesLawful constraintSystem.constants)
    (hcoherent : OperationsKeygenCoherent constraintSystem operations)
    (hconstantsNodup : constraintSystem.constants.Nodup)
    (hconstantBounds : constraintSystem.constants.Forall fun column =>
      column.index < constraintSystem.numFixedColumns)
    (hactivationRows : ∀ activation ∈
      activations (FloorPlanner.V1.starts operations)
        (indexedRegions operations 0).1,
      activation.2 < n) :
    FixedAssignmentsAgree
      (rawAssignments usable
        (deriveSelCompressMap constraintSystem n
          (activations (FloorPlanner.V1.starts operations)
            (indexedRegions operations 0).1))
        constraintSystem operations) := by
  let starts := FloorPlanner.V1.starts operations
  let regions := (indexedRegions operations 0).1
  let activationRows := activations starts regions
  let tables := tableAssignments usable operations
  let constants := constantAssignments
    (FloorPlanner.V1.constantAssignments operations
      (constraintSystem.constants.map (·.index)))
  let selectors := selectorAssignments (F := F)
    (deriveSelCompressMap constraintSystem n activationRows) activationRows
  let regionWrites := regionAssignments starts regions
  have htables : FixedAssignmentsAgree tables :=
    tableAssignments_agree usable operations hfixed.loadedTableColumns_nodup
  have hconstants : FixedAssignmentsAgree constants :=
    constantAssignments_agree operations constraintSystem.constants
      hconstantsNodup
  have hselectors : FixedAssignmentsAgree selectors :=
    selectorAssignments_agree_deriveSelCompressMap
      constraintSystem n activationRows (by
        intro activation hactivation
        exact hactivationRows activation hactivation)
  have hregions : FixedAssignmentsAgree regionWrites :=
    regionAssignments_agree operations hfixed.regionAssignmentsAgree
  have htablesConstants :
      (tables.map FixedAssignment.cell).Disjoint
        (constants.map FixedAssignment.cell) :=
    tableAssignments_constantAssignments_cells_disjoint
      usable operations constraintSystem.constants hfixed
  have htablesRegions :
      (tables.map FixedAssignment.cell).Disjoint
        (regionWrites.map FixedAssignment.cell) :=
    tableAssignments_regionAssignments_cells_disjoint
      usable operations constraintSystem.constants hfixed
  have hconstantsRegions :
      (constants.map FixedAssignment.cell).Disjoint
        (regionWrites.map FixedAssignment.cell) :=
    constantAssignments_regionAssignments_cells_disjoint
      operations constraintSystem.constants
  have htablesSelectors :
      (tables.map FixedAssignment.cell).Disjoint
        (selectors.map FixedAssignment.cell) :=
    fixedAssignment_cells_disjoint_of_column_bounds tables selectors
      constraintSystem.numFixedColumns
      (by
        intro assignment hassignment
        exact tableAssignment_column_lt_numFixedColumns usable
          constraintSystem operations hcoherent hassignment)
      (by
        intro assignment hassignment
        exact selectorAssignment_column_ge_numFixedColumns
          constraintSystem n activationRows hassignment)
  have hconstantsSelectors :
      (constants.map FixedAssignment.cell).Disjoint
        (selectors.map FixedAssignment.cell) :=
    fixedAssignment_cells_disjoint_of_column_bounds constants selectors
      constraintSystem.numFixedColumns
      (by
        intro assignment hassignment
        exact constantAssignment_column_lt_numFixedColumns operations
          constraintSystem.constants constraintSystem.numFixedColumns
          hconstantBounds hassignment)
      (by
        intro assignment hassignment
        exact selectorAssignment_column_ge_numFixedColumns
          constraintSystem n activationRows hassignment)
  have hregionsSelectors :
      (regionWrites.map FixedAssignment.cell).Disjoint
        (selectors.map FixedAssignment.cell) :=
    fixedAssignment_cells_disjoint_of_column_bounds regionWrites selectors
      constraintSystem.numFixedColumns
      (by
        intro assignment hassignment
        exact regionAssignment_column_lt_numFixedColumns constraintSystem
          operations hcoherent hassignment)
      (by
        intro assignment hassignment
        exact selectorAssignment_column_ge_numFixedColumns
          constraintSystem n activationRows hassignment)
  have htablesConstantsAgree : FixedAssignmentsAgree (tables ++ constants) :=
    htables.append_of_disjoint_cells hconstants htablesConstants
  have htablesConstantsSelectorsAgree :
      FixedAssignmentsAgree (tables ++ constants ++ selectors) := by
    apply htablesConstantsAgree.append_of_disjoint_cells hselectors
    simp only [List.map_append]
    exact List.disjoint_append_left.mpr
      ⟨htablesSelectors, hconstantsSelectors⟩
  have hall : FixedAssignmentsAgree
      (tables ++ constants ++ selectors ++ regionWrites) := by
    apply htablesConstantsSelectorsAgree.append_of_disjoint_cells hregions
    simp only [List.map_append]
    exact List.disjoint_append_left.mpr
      ⟨List.disjoint_append_left.mpr
          ⟨htablesRegions, hconstantsRegions⟩,
        hregionsSelectors.symm⟩
  simpa only [rawAssignments, starts, regions, activationRows,
    tables, constants, selectors, regionWrites] using hall

/-- Deduplicate field-valued assignments by cell, retaining the last write. -/
def dedupAssignments
    (assignments : List (FixedAssignment F)) : List (FixedAssignment F) :=
  let values : Std.HashMap (ℕ × ℕ) F :=
    assignments.foldl
      (fun values (column, row, value) =>
        values.insert (column, row) value)
      ∅
  values.toList.map fun ((column, row), value) => (column, row, value)

private theorem getElem?_foldl_insert_eq_of_agree
    (remaining : List (FixedAssignment F))
    (values : Std.HashMap (ℕ × ℕ) F)
    (cell : ℕ × ℕ) (value : F)
    (hvalue : values[cell]? = some value)
    (hagrees : ∀ assignment ∈ remaining,
      assignment.cell = cell → assignment.2.2 = value) :
    (remaining.foldl
      (fun values (column, row, assignedValue) =>
        values.insert (column, row) assignedValue)
      values)[cell]? = some value := by
  induction remaining generalizing values with
  | nil => exact hvalue
  | cons assignment rest inductionHypothesis =>
      simp only [List.foldl_cons]
      apply inductionHypothesis
      · rw [Std.HashMap.getElem?_insert]
        by_cases hcell : assignment.cell = cell
        · have hassignedValue :=
            hagrees assignment (by simp) hcell
          simp only [FixedAssignment.cell] at hcell
          rw [if_pos (beq_iff_eq.mpr hcell)]
          exact congrArg some hassignedValue
        · have hcell' : (assignment.1, assignment.2.1) ≠ cell := by
            simpa only [FixedAssignment.cell] using hcell
          rw [if_neg (fun hequal => hcell' (beq_iff_eq.mp hequal))]
          exact hvalue
      · intro later hlater hcell
        exact hagrees later (by simp [hlater]) hcell

private theorem getElem?_foldl_insert_eq_of_mem
    (assignments : List (FixedAssignment F))
    (values : Std.HashMap (ℕ × ℕ) F)
    (assignment : FixedAssignment F)
    (hassignment : assignment ∈ assignments)
    (hagrees : FixedAssignmentsAgree assignments) :
    (assignments.foldl
      (fun values (column, row, value) =>
        values.insert (column, row) value)
      values)[assignment.cell]? = some assignment.2.2 := by
  induction assignments generalizing values with
  | nil => simp at hassignment
  | cons head rest inductionHypothesis =>
      simp only [List.mem_cons] at hassignment
      rcases hassignment with rfl | hrest
      · simp only [List.foldl_cons]
        apply getElem?_foldl_insert_eq_of_agree
        · rw [Std.HashMap.getElem?_insert]
          simp [FixedAssignment.cell]
        · intro later hlater hcell
          exact hagrees (by simp [hlater]) (by simp) hcell
      · simp only [List.foldl_cons]
        apply inductionHypothesis (values :=
          values.insert head.cell head.2.2) hrest
        intro left right hleft hright hcell
        exact hagrees (by simp [hleft]) (by simp [hright]) hcell

/-- Last-write deduplication retains every write when duplicate cells agree. -/
theorem mem_dedupAssignments_of_mem
    (assignments : List (FixedAssignment F))
    (hagrees : FixedAssignmentsAgree assignments)
    {assignment : FixedAssignment F}
    (hassignment : assignment ∈ assignments) :
    assignment ∈ dedupAssignments assignments := by
  let values : Std.HashMap (ℕ × ℕ) F :=
    assignments.foldl
      (fun values (column, row, value) =>
        values.insert (column, row) value)
      ∅
  rw [show dedupAssignments assignments =
      values.toList.map
        (fun entry => (entry.1.1, entry.1.2, entry.2)) from rfl,
    List.mem_map]
  refine ⟨(assignment.cell, assignment.2.2), ?_, ?_⟩
  · rw [Std.HashMap.mem_toList_iff_getElem?_eq_some]
    exact getElem?_foldl_insert_eq_of_mem
      assignments ∅ assignment hassignment hagrees
  · rcases assignment with ⟨column, row, value⟩
    rfl

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
  sortAssignments (dedupAssignments
    (rawAssignments usable selectorMap constraintSystem operations))

/-- Every lawful raw write survives fixed compilation. -/
theorem mem_compileFixed_of_mem_raw [FiniteField F]
    (usable : ℕ) (selectorMap : SelCompressMap)
    (constraintSystem : ConstraintSystem F) (operations : Operations F)
    (hagrees : FixedAssignmentsAgree
      (rawAssignments usable selectorMap constraintSystem operations))
    {assignment : FixedAssignment F}
    (hassignment : assignment ∈
      rawAssignments usable selectorMap constraintSystem operations) :
    assignment ∈ compileFixed usable selectorMap constraintSystem operations := by
  rw [compileFixed]
  exact (sortAssignments_perm _).mem_iff.mpr
    (mem_dedupAssignments_of_mem _ hagrees hassignment)

private theorem getElem?_foldl_insert_eq_none_of_not_mem
    (assignments : List (FixedAssignment F))
    (values : Std.HashMap (ℕ × ℕ) F) (cell : ℕ × ℕ)
    (hinitial : values[cell]? = none)
    (habsent : cell ∉ assignments.map FixedAssignment.cell) :
    (assignments.foldl
      (fun current (column, row, value) =>
        current.insert (column, row) value)
      values)[cell]? = none := by
  induction assignments generalizing values with
  | nil => exact hinitial
  | cons assignment rest inductionHypothesis =>
      simp only [List.foldl_cons]
      apply inductionHypothesis
      · rw [Std.HashMap.getElem?_insert]
        have hne : assignment.cell ≠ cell := by
          intro heq
          exact habsent (by simp [heq])
        have hne' : (assignment.1, assignment.2.1) ≠ cell := by
          simpa only [FixedAssignment.cell] using hne
        rw [if_neg (fun heq => hne' (beq_iff_eq.mp heq))]
        exact hinitial
      · intro hmem
        apply habsent
        simpa only [List.map_cons, List.mem_cons] using Or.inr hmem

/-- Every cell retained by last-write deduplication originated in the input
assignment stream. -/
theorem cell_mem_of_mem_dedupAssignments
    (assignments : List (FixedAssignment F))
    {assignment : FixedAssignment F}
    (hassignment : assignment ∈ dedupAssignments assignments) :
    assignment.cell ∈ assignments.map FixedAssignment.cell := by
  let values : Std.HashMap (ℕ × ℕ) F :=
    assignments.foldl
      (fun current (column, row, value) =>
        current.insert (column, row) value) ∅
  rw [show dedupAssignments assignments =
      values.toList.map
        (fun entry => (entry.1.1, entry.1.2, entry.2)) from rfl,
    List.mem_map] at hassignment
  obtain ⟨entry, hentry, heq⟩ := hassignment
  have hvalue : values[assignment.cell]? = some assignment.2.2 := by
    rw [Std.HashMap.mem_toList_iff_getElem?_eq_some] at hentry
    obtain ⟨rfl, rfl, rfl⟩ := heq
    exact hentry
  by_contra habsent
  have hnone : values[assignment.cell]? = none := by
    apply getElem?_foldl_insert_eq_none_of_not_mem
    · simp
    · exact habsent
  rw [hnone] at hvalue
  contradiction

/-- Every cell retained by fixed compilation originated in the raw compiler
assignment stream. -/
theorem cell_mem_raw_of_mem_compileFixed [FiniteField F]
    (usable : ℕ) (selectorMap : SelCompressMap)
    (constraintSystem : ConstraintSystem F) (operations : Operations F)
    {assignment : FixedAssignment F}
    (hassignment : assignment ∈
      compileFixed usable selectorMap constraintSystem operations) :
    assignment.cell ∈
      (rawAssignments usable selectorMap constraintSystem operations).map
        FixedAssignment.cell := by
  rw [compileFixed] at hassignment
  have hdedup := (sortAssignments_perm _).mem_iff.mp hassignment
  exact cell_mem_of_mem_dedupAssignments _ hdedup

/-- A raw write in the packed-selector column suffix comes from a selector
activation. Tables, constants, and region-local fixed assignments all remain in
the configure-allocated fixed-column prefix. -/
theorem exists_selectorActivation_of_mem_rawAssignments_of_column_ge
    [FiniteField F]
    (usable : ℕ) (selectorMap : SelCompressMap)
    (constraintSystem : ConstraintSystem F) (operations : Operations F)
    (hcoherent : OperationsKeygenCoherent constraintSystem operations)
    (hconstantBounds : constraintSystem.constants.Forall fun column =>
      column.index < constraintSystem.numFixedColumns)
    {assignment : FixedAssignment F}
    (hassignment : assignment ∈
      rawAssignments usable selectorMap constraintSystem operations)
    (hcolumn : constraintSystem.numFixedColumns ≤ assignment.1) :
    ∃ selector row compressed,
      (selector, row) ∈ activations (FloorPlanner.V1.starts operations)
          (indexedRegions operations 0).1 ∧
        selectorMap.lookup selector = some compressed ∧
        assignment = (compressed.packedCol, row,
          FiniteField.fromNat compressed.assignedRoot) := by
  simp only [rawAssignments] at hassignment
  rcases List.mem_append.mp hassignment with hprefix | hregion
  rcases List.mem_append.mp hprefix with hprefix | hselector
  rcases List.mem_append.mp hprefix with htable | hconstant
  · have hlt := tableAssignment_column_lt_numFixedColumns usable
      constraintSystem operations hcoherent htable
    omega
  · have hlt := constantAssignment_column_lt_numFixedColumns operations
      constraintSystem.constants constraintSystem.numFixedColumns
      hconstantBounds hconstant
    omega
  · exact exists_activation_lookup_of_mem_selectorAssignments
      selectorMap
      (activations (FloorPlanner.V1.starts operations)
        (indexedRegions operations 0).1)
      hselector
  · have hlt := regionAssignment_column_lt_numFixedColumns constraintSystem
      operations hcoherent hregion
    omega

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

/-- An in-range cell with no sparse assignment retains the dense compiler's zero
initial value. -/
theorem denseFixedColumns_getD_getD_eq_zero_of_not_mem [Zero F]
    (numRows numColumns : ℕ)
    (assignments : List (FixedAssignment F))
    (column row : ℕ)
    (habsent : (column, row) ∉ assignments.map FixedAssignment.cell)
    (hcolumn : column < numColumns) (hrow : row < numRows) :
    ((denseFixedColumns numRows numColumns assignments).getD column []).getD
        row 0 = 0 := by
  let initial : Array (Array F) :=
    Array.replicate numColumns (Array.replicate numRows 0)
  let result := assignments.foldl (scatterFixed numColumns) initial
  have hshape := scatterFixed_fold_sized assignments
    (columns := initial) (numRows := numRows) (numColumns := numColumns)
    (by simp [initial]) (by simp [initial])
  have hresultColumn : column < result.size := by
    rw [hshape.1]
    exact hcolumn
  have hresultRow : row < result[column].size := by
    rw [hshape.2 column hresultColumn]
    exact hrow
  have hpreserved := fixedCell?_scatterFixed_fold_eq_of_forall_cell_ne
    assignments (columns := initial) (numRows := numRows)
    (numColumns := numColumns) (by simp [initial]) (by simp [initial])
    column row hcolumn hrow (by
      intro assignment hassignment hequal
      exact habsent (List.mem_map.mpr ⟨assignment, hassignment, hequal⟩))
  have hvalue : result[column][row] = 0 := by
    simp only [fixedCell?] at hpreserved
    rw [Array.getElem?_eq_getElem hresultColumn, Option.bind_some,
      Array.getElem?_eq_getElem hresultRow] at hpreserved
    have hinitialColumn : column < initial.size := by
      simp [initial, hcolumn]
    have hinitialRow : row < initial[column].size := by
      simpa [initial] using hrow
    rw [Array.getElem?_eq_getElem hinitialColumn, Option.bind_some,
      Array.getElem?_eq_getElem hinitialRow] at hpreserved
    simpa [initial] using Option.some.inj hpreserved
  have hdenseColumn :
      column < (denseFixedColumns numRows numColumns assignments).length := by
    simpa only [denseFixedColumns_length] using hcolumn
  rw [List.getD_eq_getElem _ _ hdenseColumn]
  have hdenseRow : row <
      (denseFixedColumns numRows numColumns assignments)[column].length := by
    simpa only [denseFixedColumns, List.getElem_map, Array.getElem_toList,
      Array.length_toList, initial, result] using hresultRow
  rw [List.getD_eq_getElem _ _ hdenseRow]
  simpa only [denseFixedColumns, List.getElem_map, Array.getElem_toList,
    initial, result] using hvalue

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
