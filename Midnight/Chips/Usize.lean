import Midnight.Chips.CertifiedCircuit

/-! Rust's lowering in `usize`. midnight-zk builds without overflow checks (Cargo.toml's release
profile), so the floor planners' region arithmetic wraps mod 2^64: `regions[i] + offset` for every
enable, fixed write and copy endpoint, the shape's `offset + 1` (layouter.rs:218-287), Simple's
column ends and constants rows (single_pass.rs:198-231), V1's area key and first-fit arithmetic
(strategy.rs). This is the executable lowering the key is derived from. Without a wrap it is the
`Nat` lowering the certificate describes; with one the certificate, whose bounds feed Clean's
meaning at unwrapped rows, does not exist, and only this lowering and `check` admit the stream. -/

namespace Midnight.Chips.Usize
open Halo2 Halo2.FloorPlanner Midnight.Keygen

def W : Nat := 2 ^ 64

def wrap (x : Nat) : Nat := x % W

/-- `x as isize` for a `usize` `x`, and `isize` subtraction, both two's complement. -/
def isize (x : Nat) : Int := if x < 2 ^ 63 then x else (x : Int) - W

def isub (a b : Int) : Int := (a - b + 2 ^ 63) % (W : Int) - 2 ^ 63

/-- `RegionShape` with `row_count = max(row_count, offset + 1)` in `usize`: an operation at offset
`2^64 - 1` counts 0 rows. -/
def shape (index : Nat) (body : RegionOperations F) : RegionShape :=
  { measureRegion index body with
    rowCount := body.foldl (fun m op => max m (wrap (regionOperationRowExtent op))) 0 }

/-- Region starts, and the constants pass's `(value, column, row)` in Rust's order. `placed` is
false when a queued constant has no constants column (Simple) or position (V1):
`NotEnoughColumnsForConstants`. -/
structure Plan where
  starts : List Nat
  constants : List (Nat × Nat × Nat)
  placed : Bool

/-- `SingleChipLayouter::assign_region_impl` (single_pass.rs:176-235) in `usize`. -/
def simple (constant : Option Nat) (ops : Operations F) : Plan := Id.run do
  let mut columns : Std.HashMap RegionColumn Nat := {}
  let mut starts : Array Nat := #[]
  let mut constants : Array (Nat × Nat × Nat) := #[]
  let mut placed := true
  for (index, body) in (indexedRegions ops 0).1 do
    let s := shape index body
    let start := s.columns.foldl (fun row c => max row (columns.getD c 0)) 0
    starts := starts.push start
    for c in s.columns do columns := columns.insert c (wrap (start + s.rowCount))
    let values := regionConstantValues body
    match constant with
    | none => if !values.isEmpty then placed := false
    | some column =>
      let key := RegionColumn.column .fixed column
      let next := columns.getD key 0
      for (value, j) in values.zipIdx do
        constants := constants.push (scalarNat value, column, wrap (next + j))
      columns := columns.insert key (wrap (next + values.length))
  return ⟨starts.toList, constants.toList, placed⟩

/-! V1 (strategy.rs, v1.rs:79-138). A column's allocations are `(start, length)` sorted by start,
at most one per start: `AllocatedRegion` orders by start alone, so `BTreeSet::insert` keeps the
old interval at an equal start. Rust's panics are errors. -/

abbrev Allocations := Std.HashMap RegionColumn (List (Nat × Nat))

def insertAt (start length : Nat) : List (Nat × Nat) → List (Nat × Nat)
  | [] => [(start, length)]
  | head :: rest =>
    if start == head.1 then head :: rest
    else if start < head.1 then (start, length) :: head :: rest
    else head :: insertAt start length rest

/-- `free_intervals(start, end)` (strategy.rs:64-98). -/
def freeIntervals (allocated : List (Nat × Nat)) (start : Nat) (endRow : Option Nat) :
    List (Nat × Option Nat) := Id.run do
  let mut row := start
  let mut out : Array (Nat × Option Nat) := #[]
  for (s, l) in allocated do
    if endRow.any (s ≥ ·) then continue
    if row < s then out := out.push (row, some s)
    row := max row (wrap (s + l))
  if endRow.all (row < ·) then out := out.push (row, endRow)
  return out.toList

def unboundedStart (allocated : List (Nat × Nat)) : Nat :=
  match allocated.getLast? with
  | some (s, l) => wrap (s + l)
  | none => 0

/-- `first_fit_region` (strategy.rs:104-159); `fuel` is the number of columns left. -/
def firstFit : Nat → Allocations → List RegionColumn → Nat → Nat → Option Nat →
    Except String (Option Nat × Allocations)
  | _, m, [], _, start, _ => pure (some start, m)
  | 0, m, _ :: _, _, _, _ => pure (none, m)
  | fuel + 1, m, c :: rest, length, start, slack => do
    let endRow := slack.map fun s => wrap (start + length + s)
    let spaces := freeIntervals (m.getD c []) start endRow
    let mut m := m.insert c (m.getD c [])
    for (spaceStart, spaceEnd) in spaces do
      let spaceSlack := spaceEnd.map fun e => isub (isub (isize e) (isize spaceStart)) (isize length)
      match slack, spaceSlack with
      | some s, some ss => unless ss ≤ isize s do throw "V1 first_fit_region: s_slack <= slack fails (strategy.rs:129)"
      | _, _ => pure ()
      if spaceSlack.getD 0 ≥ 0 then
        let (row?, m') ← firstFit fuel m rest length spaceStart (spaceSlack.map Int.toNat)
        m := m'
        if let some row := row? then
          if let some e := endRow then
            unless wrap (row + length) ≤ e do throw "V1 first_fit_region: row + region_length <= end fails (strategy.rs:141)"
          return (some row, m.insert c (insertAt row length (m.getD c [])))
    return (none, m)

/-- `slot_in_biggest_advice_first` (strategy.rs:198-242): stable sort by the `usize` area, reversed,
then `slot_in`. Returns starts by region index and the allocations. -/
def slot (ops : Operations F) : Except String (List Nat × Allocations) := do
  let shapes := (indexedRegions ops 0).1.map fun (index, body) => shape index body
  let key := fun (s : RegionShape) => wrap ((s.columns.filter RegionColumn.isAdvice).length * s.rowCount)
  let sorted := (shapes.mergeSort fun a b => key a < key b || key a == key b && a.index ≤ b.index).reverse
  let mut m : Allocations := {}
  let mut pairs : Array (Nat × Nat) := #[]
  for s in sorted do
    let columns := sortRegionColumns s.columns
    let (row?, m') ← firstFit columns.length m columns s.rowCount 0 none
    let some row := row? | throw "V1 slot_in: no fit (strategy.rs:186)"
    m := m'
    pairs := pairs.push (s.index, row)
  return ((pairs.toList.mergeSort fun a b => a.1 ≤ b.1).map (·.2), m)

/-- V1's constants positions (v1.rs:84-110), at most `need` of them: Rust counts them all, which
only decides `need` against the count. -/
def v1Positions (columns : List Nat) (m : Allocations) (need : Nat) : List (Nat × Nat) := Id.run do
  let endRow := m.fold (fun r _ allocated => max r (unboundedStart allocated)) 0
  let mut out : Array (Nat × Nat) := #[]
  for column in columns do
    for (s, e?) in freeIntervals (m.getD (.column .fixed column) []) 0 (some endRow) do
      for i in [0:(e?.getD s) - s] do
        if out.size > need then return out.toList
        out := out.push (column, s + i)
  return out.toList

def v1 (columns : List Nat) (ops : Operations F) : Except String Plan := do
  let (starts, m) ← slot ops
  let sites := operationConstSites ops
  let positions := v1Positions columns m sites.length
  return ⟨starts, (positions.zip sites).map fun ((column, row), (_, value)) => (scalarNat value, column, row),
    decide (sites.length ≤ positions.length)⟩

def plan (planner : Layout.Planner) (constant : Option Nat) (ops : Operations F) : Except String Plan :=
  match planner with
  | .simple => pure (simple constant ops)
  | .v1 columns => v1 columns ops

/-- What synthesis hands keygen: fixed writes in stream order, selector activations and copies,
rows mod 2^64. -/
structure Lowered where
  plan : Plan
  fixedWrites : List LayoutLawful.Write
  activations : List (Nat × Nat)
  copies : List CopyLawful.ResolvedCopy

def lower (source : CS) (ops : Operations F) (k : Nat) (planner : Layout.Planner) :
    Except String Lowered := do
  let config := CertifiedCircuit.layoutConfig source k
  let p ← plan planner source.constantColumn ops
  let permutation := CertifiedCircuit.permutationColumns source
  let (writes, copies) := match planner with
    | .simple => (Layout.streamFixedWrites config.usableRows p.starts p.constants 0 ops,
        Halo2.Layout.SimpleFloorPlanner.copyList permutation p.starts ops p.constants)
    | .v1 _ => (Layout.streamFixedWrites config.usableRows p.starts [] 0 ops ++
        Halo2.Layout.constantsFixed p.constants,
        Halo2.Layout.V1.copyList permutation p.starts ops p.constants)
  return ⟨p, writes.map fun (c, r, v) => (c, wrap r, v),
    (Halo2.activations p.starts (indexedRegions ops 0).1).map fun (q, r) => (q, wrap r),
    copies.map fun (a, r, b, s) => (a, wrap r, b, wrap s)⟩

def Lowered.layout (l : Lowered) (source : CS) (k : Nat) : Layout.DerivedLayout :=
  let config := CertifiedCircuit.layoutConfig source k
  let fixed := (LayoutLawful.dense config.rows (config.numFixed + config.numSelectors)
    (l.fixedWrites ++ LayoutLawful.selectorWrites config.numFixed l.activations)).toArray.map
    List.toArray
  { regionStarts := l.plan.starts
    copies := l.copies
    fixed := fixed
    selectorRows := (Array.range config.numSelectors).map fun selector =>
      (Array.range config.rows).filter fun row =>
        ((fixed[config.numFixed + selector]?.bind fun values => values[row]?).getD 0) == 1 }

/-- The layout the key is derived from; empty when a planner panics, which `check` reports. -/
def layout (source : CS) (ops : Operations F) (k : Nat) (planner : Layout.Planner := .simple) :
    Layout.DerivedLayout :=
  match lower source ops k planner with
  | .ok l => l.layout source k
  | .error _ => ⟨[], [], #[], #[]⟩

/-- Every row and offset a stream names, which Rust holds in `usize`. -/
def offsets (ops : Operations F) : List Nat :=
  ops.flatMap fun
    | .region _ body => body.flatMap fun
      | .assignAdvice _ row _ | .assignFixed _ row _ | .enableGate _ row | .enableLookup _ _ row => [row]
      | .constrainEqual left right => [left.rowOffset, right.rowOffset]
      | .constrainConstant cell _ => [cell.rowOffset]
      | .constrainInstance cell _ row => [cell.rowOffset, row]
    | .constrainInstance cell _ row => [cell.rowOffset, row]
    | .loadTable _ values => [values.length]

/-- Keygen's bounds on the wrapped rows (keygen.rs:76, 116, 142): fixed writes, enables and copies
in usable rows and configured columns. -/
def check (source : CS) (ops : Operations F) (k : Nat) (planner : Layout.Planner := .simple) :
    Except String Unit := do
  let config := CertifiedCircuit.layoutConfig source k
  unless k ≤ 32 && config.blindingFactors + 3 ≤ config.rows do throw "domain too small"
  unless (offsets ops).all (· < W) do throw "an offset or row is 2^64 or more, which no usize holds"
  let l ← lower source ops k planner
  unless l.plan.placed do throw "a deferred constant has no position (NotEnoughColumnsForConstants)"
  let usable := config.usableRows
  for (column, row, _) in l.fixedWrites do
    unless column < config.numFixed && row < usable do
      throw s!"fixed write ({column}, {row}) outside {config.numFixed} columns, {usable} rows"
  for (sel, row) in l.activations do
    unless sel < config.numSelectors && row < usable do
      throw s!"selector {sel} enabled at row {row} out of bounds"
  let fixed := (l.layout source k).fixed
  for column in [config.numFixed:config.numFixed + config.numSelectors] do
    unless (fixed[column]?.getD #[]).all (· ≤ 1) do throw s!"selector column {column} not 0/1"
  for (lc, lr, rc, rr) in l.copies do
    unless lc < source.permutation.size && rc < source.permutation.size && lr < usable && rr < usable do
      throw s!"copy ({lc}, {lr}) = ({rc}, {rr}) outside the equality columns or usable rows"

end Midnight.Chips.Usize
