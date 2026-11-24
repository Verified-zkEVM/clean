import Midnight.Configuration
import Clean.Halo2.Configure.Extensions

/-! The Midnight backend: a Clean constraint system replayed into the `Keygen.ConfigM` builders,
so gates and lookups go through the Lean ports of Rust's `ConstraintSystem` methods. Counts, query
layouts, permutation and constants are assigned from Clean's lists. `rows` gates and unstated
lookups replay from their entries at their positions; handles compile to nothing. Lookups replay
before gates, so the builder scratch `currentQueries` ends as the last gate's closure: exact for
programs whose last event is a gate, as SHA-256 and Poseidon. Selector kinds come from each
selector's first use and reach only `selectorKinds`, not the key. Unused ones default to complex:
Clean's `ConstraintSystem` keeps no kinds, and Rust's key never reads an unused selector's kind. -/

namespace Midnight.Backend
open Halo2 (ConstraintSystem GateExtension LookupExtension GateMode Gate LookupArgument Selector)
open Keygen (E ConfigM)

private def pushError (message : String) : ConfigM Unit :=
  modify fun s => { s with errors := s.errors.push message }

/-- Rust's closure: query each recorded cell in order. -/
def queryCells (cells : List E) : ConfigM Unit := do
  for c in cells do
    if let .var q := c then Functor.discard (Keygen.query q)

private def selectorsOf (e : E) : List Selector :=
  e.queryAtoms.filterMap fun
    | .selector q => some q
    | _ => none

/-- Selectors in first-use order: gate owners and polynomials, then lookup masters and inputs. -/
def selectorUses (cs : ConstraintSystem F) : List Selector :=
  (cs.gates.flatMap fun g => g.selector :: g.constraints.flatMap fun c => selectorsOf c.poly) ++
    cs.lookups.flatMap fun l => l.masterSelector.toSelector :: l.inputs.flatMap selectorsOf

/-- `p` without the outer `q *` that `Gate.withSelector` builds. -/
def unselect (q : Selector) : E → Option E
  | .mul (.var (.selector s)) p => if s = q then some p else none
  | _ => none

/-- The gate's bodies when every polynomial is `q * p` for its own selector. -/
def stripped (g : Gate F) : Option (Array (String × E)) :=
  (g.constraints.mapM fun c => (c.name, ·) <$> unselect g.selector c.poly).map List.toArray

/-- One gate, by its entry's mode. An unmarked gate is `with_selector` when every polynomial
is `q * p`, else `without_selector`, so hand-built shapes such as `(q * x) * e` keep their AST.
`selectorCalls` are a `without_selector` entry's `query_selector` calls. -/
def replayGate (mode : Option GateMode) (g : Gate F) (selectorCalls : List Selector := []) :
    ConfigM Unit := do
  let before := (← get).gates.size
  let bodies := (g.constraints.map fun c => (c.name, c.poly)).toArray
  match mode with
  | some .additive =>
    match stripped g with
    | some parts =>
      Keygen.additiveGate g.name g.selector do
        queryCells g.queriedCells
        return parts
    | none => pushError s!"gate {g.name}: an additive shadow that is not q * c"
  | some .withoutSelector =>
    Keygen.gateWithoutSelector g.name (selectorCalls := selectorCalls.toArray) do
      queryCells g.queriedCells
      return bodies
  | some _ => pushError s!"gate {g.name}: a rows or handle entry on a shadow"
  | none =>
    match stripped g with
    | some parts =>
      Keygen.gate g.name g.selector do
        queryCells g.queriedCells
        return parts
    | none =>
      if g.constraints.all fun c => c.poly.queryAtoms.contains (.selector g.selector) then
        Keygen.gateWithoutSelector g.name do
          queryCells g.queriedCells
          return bodies
      else pushError s!"gate {g.name}: a polynomial without its selector"
  let s ← get
  if s.gates.size > before && (s.gates.back?.map (·.rows)).getD false then
    pushError s!"gate {g.name}: a shadow that compiles to a rows gate"

/-- A `rows` entry: `without_selector` over its recorded closure. -/
def replayRows (entry : GateExtension F) : ConfigM Unit := do
  let before := (← get).gates.size
  Keygen.gateWithoutSelector entry.name (selectorCalls := entry.queriedSelectors.toArray) do
    queryCells entry.queriedCells
    return (entry.constraints.map fun c => (c.name, c.poly)).toArray
  let s ← get
  unless s.gates.size > before && (s.gates.back?.map (·.rows)).getD false do
    pushError s!"gate {entry.name}: a rows entry that one selector owns"

/-- Gates in order, each preceded by the `rows` entries placed before it. A handle compiles to
nothing, and must state nothing. -/
def replayGates (cs : ConstraintSystem F) : ConfigM Unit := do
  let marks := cs.extensions.filterMap fun
    | .gate entry => some entry
    | _ => none
  let rows := marks.filter (·.mode == .rows)
  let shadows := marks.filter (·.mode != .rows)
  for (i, g) in (List.range cs.gates.length).zip cs.gates do
    for entry in rows.filter (·.position == i) do replayRows entry
    let shadow := shadows.find? (·.position == i)
    match shadow.map (·.mode) with
    | some GateMode.handle =>
      unless g.constraints.isEmpty do pushError s!"gate {g.name}: a handle with constraints"
    | mode => replayGate mode g ((shadow.map (·.queriedSelectors)).getD [])
  for entry in rows.filter (·.position == cs.gates.length) do replayRows entry
  let positions := shadows.map (·.position)
  unless positions.eraseDups.length == positions.length &&
      positions.all (fun p => decide (p < cs.gates.length)) &&
      rows.all (fun entry => decide (entry.position ≤ cs.gates.length)) do
    pushError "gate entries out of place"

/-- Shadow `j` of a batch entry, as `Clean.Halo2.batchedLookup` emits it. -/
def shadowMatches (entry : LookupExtension F) (q : Halo2.ComplexSelector) (j : Nat)
    (shadow : LookupArgument F) : Bool :=
  shadow.masterSelector == q &&
    shadow.inputs == entry.columns.filterMap (·.1[j]?) &&
    shadow.tables == entry.columns.filterMap fun c => c.1[j]?.map fun _ => c.2

/-- The entry's recorded closure is column queries and covers every input. -/
def closureCovers (entry : LookupExtension F) : Bool :=
  let calls := entry.queriedCells.filterMap fun
    | .var q => if Keygen.queryAtom q then some q else none
    | _ => none
  calls.length == entry.queriedCells.length &&
    entry.columns.all fun c => c.1.all (·.declared calls)

/-- Every column has the first column's number of inputs, so `LookupExtension.tuples`, which
pads and truncates to that width, reads the entry as written. -/
def rectangular (entry : LookupExtension F) : Bool :=
  let width := (entry.columns.head?.map (·.1.length)).getD 0
  entry.columns.all (·.1.length == width)

/-- A batch entry and its span of shadows: one `Keygen.batchedLookup` over the entry's recorded
closure, never the shadows' atoms (a closure may query a cell once and reuse it). -/
def replayBatch (entry : LookupExtension F) (shadows : List (LookupArgument F)) :
    ConfigM Unit := do
  let width := (entry.columns.head?.map (·.1.length)).getD 0
  match entry.selector, (entry.columns.mapM fun c => Keygen.tableColumn? c.2) with
  | some q, some tables =>
    if entry.any then
      pushError s!"lookup {entry.name}: a batched_lookup_any entry with shadows"
    else if !rectangular entry then
      pushError s!"lookup {entry.name}: columns with different numbers of inputs"
    else if !closureCovers entry then
      pushError s!"lookup {entry.name}: inputs use queries the recorded closure did not make"
    else if entry.shadows == 0 || entry.shadows != width || shadows.length != width ||
        !((List.range width).zip shadows).all fun (j, a) => shadowMatches entry q j a then
      pushError s!"lookup {entry.name}: an entry that does not match its shadows"
    else
      Keygen.batchedLookup entry.name (some q.toSelector) do
        queryCells entry.queriedCells
        return ((entry.columns.zip tables).map fun (c, t) => (c.1.toArray, t)).toArray
  | none, _ => pushError s!"lookup {entry.name}: an unselected entry with shadows"
  | _, none => pushError s!"lookup {entry.name}: a table that is not a fixed column"

/-- An unmarked Clean lookup: a batch of one tuple, unnamed. Its closure is taken to be its
inputs' atoms, which only the export fields read; no port uses this path. `LookupArgument.arity`
rules out the length error; it is checked so that `zip` never truncates. -/
def replayLookup (a : LookupArgument F) : ConfigM Unit := do
  match a.tables.mapM Keygen.tableColumn? with
  | some tables =>
    if a.inputs.length != tables.length then
      pushError "lookup: inputs and tables of different lengths"
    else
      Keygen.batchedLookup "" (some a.masterSelector.toSelector) do
        queryCells ((a.inputs.flatMap fun e => e.queryAtoms.filter Keygen.queryAtom).map (.var ·))
        return ((a.inputs.zip tables).map fun (x, t) => (#[x], t)).toArray
  | none => pushError "lookup: a table that is not a fixed column"

/-- A lookup entry with no shadows: `batched_lookup_any` over its recorded closure. -/
def replayUnstated (entry : LookupExtension F) : ConfigM Unit :=
  if !rectangular entry then
    pushError s!"lookup {entry.name}: columns with different numbers of inputs"
  else if entry.any then
    Keygen.batchedLookupAny entry.name (entry.selector.map (·.toSelector)) do
      queryCells entry.queriedCells
      return (entry.columns.map fun c => (c.1.toArray, c.2)).toArray
  else pushError s!"lookup {entry.name}: an unselected batched_lookup"

/-- Lookups in order, each preceded by the shadowless entries placed before it. -/
def replayLookups (cs : ConstraintSystem F) : ConfigM Unit := do
  let entries := cs.extensions.filterMap fun
    | .lookup entry => some entry
    | _ => none
  let unstated := entries.filter (·.shadows == 0)
  let batches := entries.filter (·.shadows != 0)
  let mut next := 0
  let mut consumed := 0
  for (i, a) in (List.range cs.lookups.length).zip cs.lookups do
    for entry in unstated.filter (·.position == i) do replayUnstated entry
    if i < next then continue
    match batches.find? (·.position == i) with
    | some entry =>
      replayBatch entry ((cs.lookups.drop i).take entry.shadows)
      next := i + entry.shadows
      consumed := consumed + 1
    | none => replayLookup a
  for entry in unstated.filter (·.position == cs.lookups.length) do replayUnstated entry
  unless consumed == batches.length &&
      unstated.all (fun entry => decide (entry.position ≤ cs.lookups.length)) do
    pushError "lookup entries out of place"

def replay (cs : ConstraintSystem F) : ConfigM Unit := do
  let uses := selectorUses cs
  modify fun s => { s with
    numAdvice := cs.numAdviceColumns
    numFixed := cs.numFixedColumns
    numInstance := cs.numInstanceColumns
    numSelectors := cs.numSelectors
    selectorKinds := ((List.range cs.numSelectors).map fun i =>
      ((uses.find? (·.index == i)).map (·.simple)).getD false).toArray
    adviceQueries := (cs.adviceQueries.map fun (c, r) => (c.index, r)).toArray
    fixedQueries := (cs.fixedQueries.map fun (c, r) => (c.index, r)).toArray
    instanceQueries := (cs.instanceQueries.map fun (c, r) => (c.index, r)).toArray
    permutation := cs.permutationColumns.toArray
    constantColumns := (cs.constants.map (·.index)).toArray }
  replayLookups cs
  replayGates cs
  for e in cs.extensions do
    match e with
    | .minimumDegree degree => Keygen.setMinimumDegree degree
    | .rejected message => pushError message
    | _ => pure ()

/-- The configuration a Clean configure program compiles to. -/
def compile (program : Halo2.Configure F Unit) : Keygen.CS :=
  ((replay (program.run {}).2).run {}).2

end Midnight.Backend
