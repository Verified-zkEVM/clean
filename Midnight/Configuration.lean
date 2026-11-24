import Midnight.Keygen.BatchedLookup
import Midnight.Keygen.Normalize
import Clean.Halo2.ConstraintSystem

namespace Midnight.Keygen
open Halo2 (Expression)

structure GateSpec where
  name : String
  selector : Halo2.Selector
  queries : Array Halo2.Query
  constraints : Array (String × E)
  /-- `Constraints::without_selector`: the constraints are the polynomials. Otherwise
  `Constraints::with_selector`, which multiplies each by `selector`. -/
  raw : Bool := false
  /-- Rust's meaning only, `RowGatesHold` on every row: no single enable states a body that
  queries no selector, several, or one inside a `with_selector` body. -/
  rows : Bool := false

/-- The compiled polynomials: Rust's `q * poly` for `with_selector`, the bodies verbatim for
`without_selector`. -/
def GateSpec.polynomials (g : GateSpec) : Array E :=
  g.constraints.map fun (_, p) => if g.raw then p else Halo2.querySelector g.selector * p

/-- The selectors the compiled polynomials query. -/
def GateSpec.selectorAtoms (g : GateSpec) : List Halo2.Selector :=
  g.polynomials.toList.flatMap fun p => p.queryAtoms.filterMap fun
    | .selector q => some q
    | _ => none

/-- The selectors the gate uses: its atoms for a `rows` gate, else its owner. -/
def GateSpec.selectorUses (g : GateSpec) : List Halo2.Selector :=
  if g.rows then g.selectorAtoms else [g.selector]

/-- Any fixed rotation: Rust's `query_fixed` takes one (circuit.rs:2329). -/
def queryAtom (q : Halo2.Query) : Bool :=
  match q with
  | .selector _ => false
  | _ => true

/-- A body enabling the gate states: selector-free, or of positive degree in `selector` alone. -/
def GateSpec.bodyValid (g : GateSpec) (p : E) : Bool :=
  if g.raw then (match p.selectorDegree g.selector with | some (_ + 1) => true | _ => false)
  else p.free

def GateSpec.valid (g : GateSpec) : Bool :=
  g.queries.toList.all queryAtom && g.constraints.toList.all fun (_, p) =>
    (g.rows || g.bodyValid p) && p.declared g.queries.toList

private theorem GateSpec.queriesValid (g : GateSpec) (h : g.valid = true) :
    (g.queries.toList.map (.var ·)).Forall (Halo2.Expression.QueryAtom (F := F)) := by
  rw [List.forall_iff_forall_mem]
  intro e he
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp he
  have hq' := (List.all_eq_true.mp (Bool.and_eq_true_iff.mp h).1) q hq
  cases q <;> simp_all [queryAtom, Halo2.Expression.QueryAtom]

private theorem GateSpec.bodyOf (g : GateSpec) (h : g.valid = true) {c : String × E}
    (hc : c ∈ g.constraints.toList) :
    (g.rows || g.bodyValid c.2) = true ∧ c.2.declared g.queries.toList = true :=
  Bool.and_eq_true_iff.mp ((List.all_eq_true.mp (Bool.and_eq_true_iff.mp h).2) c hc)

private theorem GateSpec.ownedBody (g : GateSpec) (h : g.valid = true) (hrows : g.rows = false)
    {c : String × E} (hc : c ∈ g.constraints.toList) : g.bodyValid c.2 = true := by
  simpa [hrows] using (g.bodyOf h hc).1

/-- A `rows` gate's Clean handle: enabling it activates its selector and states nothing, since
Rust's meaning of its polynomials is `RowGatesHold`. -/
def GateSpec.toCleanRows (g : GateSpec) (h : g.valid = true) : Halo2.Gate F where
  name := g.name
  selector := g.selector
  queriedCells := g.queries.toList.map (.var ·)
  constraints := []
  wellFormed := ⟨g.queriesValid h, trivial, trivial, by intro _ _ hc; simp at hc⟩

/-- A `without_selector` gate as a Clean gate owned by its selector: enabling it at a row is
Rust's evaluation there, up to the nonzero factor `eval_scale` gives. -/
def GateSpec.toCleanRaw (g : GateSpec) (h : g.valid = true) (hrows : g.rows = false)
    (hraw : g.raw = true) : Halo2.Gate F where
  name := g.name
  selector := g.selector
  queriedCells := g.queries.toList.map (.var ·)
  constraints := g.constraints.toList.map fun (name, p) => { name := name, poly := p }
  wellFormed := by
    have degree : ∀ c ∈ g.constraints.toList, ∃ d, c.2.selectorDegree g.selector = some (d + 1) :=
      fun c hc => by
        have hv := g.ownedBody h hrows hc
        rw [GateSpec.bodyValid, ite_eq_left hraw] at hv
        split at hv
        · rename_i d hd
          exact ⟨d, hd⟩
        · simp at hv
    refine ⟨g.queriesValid h, ?_, ?_, ?_⟩
    · rw [List.forall_iff_forall_mem]
      intro c hc
      obtain ⟨c', hc', rfl⟩ := List.mem_map.mp hc
      exact (Halo2.Expression.declared_iff c'.2 _).mp (g.bodyOf h hc').2
    · rw [List.forall_iff_forall_mem]
      intro c hc
      obtain ⟨c', hc', rfl⟩ := List.mem_map.mp hc
      obtain ⟨d, hd⟩ := degree c' hc'
      exact Halo2.Expression.selectorDegree_selectorsOwnedBy _ _ hd
    · intro _ c hc base scale hscale hzero
      obtain ⟨c', hc', rfl⟩ := List.mem_map.mp hc
      obtain ⟨d, hd⟩ := degree c' hc'
      rw [Halo2.Expression.eval_scale _ _ hd] at hzero
      exact (mul_eq_zero.mp hzero).resolve_left (pow_ne_zero _ hscale)

/-- The real Clean gate. The kernel-checked `valid` flag discharges Clean's local
structural obligations; the constraint polynomials are passed through unchanged, except for a
`rows` gate, whose handle states none. -/
def GateSpec.toClean (g : GateSpec) (h : g.valid = true) : Halo2.Gate F :=
  if hrows : g.rows then g.toCleanRows h else
  if hraw : g.raw then g.toCleanRaw h (by simpa using hrows) hraw else
  Halo2.Gate.withSelector g.name g.selector (g.queries.toList.map (.var ·)) g.constraints.toList
    (by
      rintro c hc
      simpa [GateSpec.bodyValid, hraw, Expression.free_iff] using
        g.ownedBody h (by simpa using hrows) hc)
    ⟨g.queriesValid h, by
      rw [List.forall_iff_forall_mem]
      intro c hc
      exact (Expression.declared_iff c.2 g.queries.toList).mp (g.bodyOf h hc).2⟩

/-- Handles on a `rows` gate's other selectors, so that each can be enabled as Rust's
`Selector::enable` does; like the owner's handle they state nothing. -/
def GateSpec.rowsHandles (g : GateSpec) (h : g.valid = true) : List (Halo2.Gate F) :=
  if hrows : g.rows then
    (g.selectorAtoms.eraseDups.filter (· != g.selector)).map fun q =>
      ({ g with selector := q } : GateSpec).toCleanRows (by simpa [GateSpec.valid, hrows] using h)
  else []

theorem GateSpec.rowsHandles_of_owned (g : GateSpec) (h : g.valid = true) (owned : g.rows = false) :
    g.rowsHandles h = [] := by
  simp [GateSpec.rowsHandles, owned]

def BatchedLookup.selectorIndex (l : BatchedLookup) : Nat :=
  match l.selector with
  | .var (.selector s) => s.index
  | _ => 0

/-- Rust's `selector`: `Some(q)` for a complex `q`, or `None`, which `BatchedArgument::new`
stores as `Constant(1)` (logup.rs:308). -/
def BatchedLookup.selectorValid (l : BatchedLookup) : Bool :=
  match l.selector with
  | .var (.selector s) => !s.simple
  | .const c => decide (c = 1)
  | _ => false

def BatchedLookup.valid (l : BatchedLookup) : Bool :=
  l.selectorValid && l.inputs.toList.all fun row => row.size == l.table.size

/-- The fixed column a table expression is, if it is a bare rotation-0 fixed query. -/
def tableColumn? : E → Option Nat
  | .var (.fixed c r) => if r = 0 then some c.index else none
  | _ => none

/-- Enabling `Some(q)` states the lookup, one `enableLookup` per tuple, only for selector-free
inputs over bare rotation-0 fixed columns: Clean's `env` pins no other table to Rust's values.
Otherwise the meaning is `RowLookupsHold` and `handles` enable the selectors. -/
def BatchedLookup.owned (l : BatchedLookup) : Bool :=
  (match l.selector with | .var (.selector s) => !s.simple | _ => false) && !l.inputs.isEmpty &&
  l.table.toList.all Expression.free && l.inputs.toList.all (fun row => row.toList.all Expression.free) &&
  l.table.toList.all fun e => (tableColumn? e).isSome

/-- The selectors a lookup uses: its `Some` selector, then those its expressions query. -/
def BatchedLookup.selectorAtoms (l : BatchedLookup) : List Halo2.Selector :=
  ((l.selector :: l.inputs.toList.flatMap Array.toList ++ l.table.toList).flatMap fun e =>
    e.queryAtoms.filterMap fun | .selector q => some q | _ => none).eraseDups

/-- A selected LogUp batch has the same active-row membership semantics as one
Clean lookup per tuple. Its protocol grouping remains in `BatchedLookup`, above. -/
def BatchedLookup.toClean (l : BatchedLookup) (h : l.valid = true) :
    List (Halo2.LookupArgument F) :=
  if ho : l.owned then
    have ho := Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp ho).1
    have ht := (Bool.and_eq_true_iff.mp ho.1).2
    l.inputs.toList.attach.map fun ⟨row, hrow⟩ =>
      have hp := (List.all_eq_true.mp ho.2) row hrow
      have hs := (List.all_eq_true.mp (Bool.and_eq_true_iff.mp h).2) row hrow
      { masterSelector := ⟨l.selectorIndex⟩
        inputs := row.toList
        tables := l.table.toList
        inputsNoSimpleSelectors := by
          rw [List.forall_iff_forall_mem]
          intro e he
          exact Expression.free_noSimpleSelectors e ((List.all_eq_true.mp hp) e he)
        tablesFree := by
          intro e he
          exact (Expression.free_iff e).mp ((List.all_eq_true.mp ht) e he)
        arity := by simpa using hs }
  else []

/-- A lookup that is not `owned` gets a constraint-free gate handle per selector it uses, so
each can be enabled as Rust's `Selector::enable` does; `RowLookupsHold` is its meaning. -/
def BatchedLookup.handles (l : BatchedLookup) : List (Halo2.Gate F) :=
  if l.owned then [] else l.selectorAtoms.map fun q =>
    ({ name := l.name, selector := q, queries := #[], constraints := #[], rows := true } : GateSpec).toCleanRows rfl

theorem BatchedLookup.handles_of_owned (l : BatchedLookup) (owned : l.owned = true) :
    l.handles = [] := by
  simp [BatchedLookup.handles, owned]

/-- Midnight configuration data, with query registration separate from expression
use order. Lookup batches and selectors remain explicit rather than being encoded
as Zcash's multiplicatively selected Plookup tuples. -/
structure CS where
  numFixed : Nat := 0
  numAdvice : Nat := 0
  numInstance : Nat := 0
  numSelectors : Nat := 0
  adviceQueries : Array (Nat × Int) := #[]
  fixedQueries : Array (Nat × Int) := #[]
  instanceQueries : Array (Nat × Int) := #[]
  permutation : Array Halo2.AnyColumn := #[]
  /-- Fixed columns enabled for deferred constants, in native configuration order. -/
  constantColumns : Array Nat := #[]
  gates : Array GateSpec := #[]
  lookups : Array BatchedLookup := #[]
  /-- `additiveGate` batches, stored without the selector multiplier. -/
  trashcans : Array GateSpec := #[]
  /-- Gate closure call order, reset on entry to each gate. -/
  currentQueries : Array Halo2.Query := #[]
  /-- Export only: each lookup's closure call order (Rust registers queries no expression uses)
  and whether it was `batchedLookupAny`, keyed by the lookup so editing `lookups` cannot
  misalign it. -/
  lookupClosures : Array (BatchedLookup × Array Halo2.Query × Bool) := #[]
  /-- Export only: batches `pushLookup` rejects, in Rust's form, so the replay can show Rust
  rejects them too. -/
  rejectedLookups : Array (String × E × Array (Array E × E) × Bool) := #[]
  /-- Export only: per gate or trash batch in call order, its name, its `queries`, the closure's
  own and whether `create_gate` walks it, so the replay leaves the rest to Rust's `query_cells`. -/
  gateClosures : Array (String × Array Halo2.Query × Array Halo2.Query × Bool) := #[]
  /-- Export only: a `without_selector` gate's explicit `query_selector` calls in order, repeats
  kept, by its index in `gates`; a gate that made none is absent. See `CS.queriedSelectors`. -/
  gateSelectorCalls : Array (Nat × Array Halo2.Selector) := #[]
  /-- Export only: each expression `pruneFolded` changed, with the tree the builder returned. -/
  prunedFrom : Array (E × E) := #[]
  /-- Export only: each selector's `simple` flag as created, so an unused one keeps its kind. -/
  selectorKinds : Array Bool := #[]
  /-- `set_minimum_degree`: a lower bound on `CS.degree`. -/
  minimumDegree : Option Nat := none
  selectorFixedStart : Option Nat := none
  /-- Malformed builder inputs are retained as errors for `validate`; they must
  never become silently repaired circuit definitions. Not part of the Rust CS. -/
  errors : Array String := #[]

abbrev ConfigM := StateM CS

def adviceColumn : ConfigM Nat := do
  let s ← get
  set { s with numAdvice := s.numAdvice + 1 }
  return s.numAdvice

def fixedColumn : ConfigM Nat := do
  let s ← get
  set { s with numFixed := s.numFixed + 1 }
  return s.numFixed

def instanceColumn : ConfigM Nat := do
  let s ← get
  set { s with numInstance := s.numInstance + 1 }
  return s.numInstance

def selector (simple : Bool := true) : ConfigM Halo2.Selector := do
  let s ← get
  set { s with numSelectors := s.numSelectors + 1, selectorKinds := s.selectorKinds.push simple }
  return ⟨s.numSelectors, simple⟩

private def insertUnique {α : Type} [BEq α] (xs : Array α) (x : α) : Array α :=
  if xs.contains x then xs else xs.push x

def query (q : Halo2.Query) : ConfigM E := do
  modify fun s =>
    let s := { s with currentQueries := s.currentQueries.push q }
    match q with
    | .advice c r => { s with adviceQueries := insertUnique s.adviceQueries (c.index, r) }
    | .fixed c r => { s with fixedQueries := insertUnique s.fixedQueries (c.index, r) }
    | .instance c r => { s with instanceQueries := insertUnique s.instanceQueries (c.index, r) }
    | .selector _ => s
  return .var q

/-- The query atoms Rust's `query_cells` visits, in order: those of the tree its operators build,
so a factor folded to `Constant(0)` contributes none. -/
def foldedAtoms (e : E) : List Halo2.Query :=
  if (Halo2.eraseExpr e {}).normalize = .constant 0 then [] else
  match e with
  | .var q => [q]
  | .const _ => []
  | .add a b | .mul a b => foldedAtoms a ++ foldedAtoms b

private def registerQuery : Halo2.Query → ConfigM Unit
  | .advice c r => modify fun s => { s with adviceQueries := insertUnique s.adviceQueries (c.index, r) }
  | .fixed c r => modify fun s => { s with fixedQueries := insertUnique s.fixedQueries (c.index, r) }
  | .instance c r => modify fun s => { s with instanceQueries := insertUnique s.instanceQueries (c.index, r) }
  | .selector _ => pure ()

/-- A gate's queries after its closure. For a body using queries made outside it, `create_gate`
registers them by walking the compiled polynomials (circuit.rs:1913-1919); additive gates are not
walked (circuit.rs:2380), so theirs must already be registered once `pruneBodies` has run. -/
private def closeGate (name : String) (polys : Array E) (walked : Bool) :
    ConfigM (Array Halo2.Query) := do
  let closure := (← get).currentQueries
  let queries ← if polys.all (·.declared closure.toList) then pure closure else do
    if walked then
      for p in polys do
        for q in foldedAtoms p do registerQuery q
    pure <| (polys.toList.flatMap Expression.queryAtoms).foldl (init := closure) fun acc q =>
      match q with
      | .selector _ => acc
      | q => insertUnique acc q
  modify fun s => { s with gateClosures := s.gateClosures.push (name, queries, closure, walked) }
  return queries

/-- `e`'s non-selector query atoms replaced by `2 + 0`, which erases to a `Sum` like no `.const`
pattern of `eraseExpr` and normalizes to `Constant(2)`. Rust's operators fold only on literal
`0` and `1`, so every node folds as before and keeps its selectors. -/
def eraseQueries : E → E
  | .var (.selector q) => .var (.selector q)
  | .var _ => .add (.const 2) (.const 0)
  | .add a b => .add (eraseQueries a) (eraseQueries b)
  | .mul a b => .mul (eraseQueries a) (eraseQueries b)
  | e => e

/-- `e` with each query-naming factor that folds to `Constant(0)` stripped of its queries (`0 + 0`,
or `eraseQueries` to keep its selectors). Rust folds such a factor before `query_cells` walks
the tree, so it never registers them; the normal form, and so the key, is unchanged. -/
def pruneFolded (e : E) : E :=
  if e.queryAtoms.any (fun | .selector _ => false | _ => true) &&
      (Halo2.eraseExpr e {}).normalize = .constant 0 then
    if e.free then .add (.const 0) (.const 0) else eraseQueries e else
  match e with
  | .add a b => .add (pruneFolded a) (pruneFolded b)
  | .mul a b => .mul (pruneFolded a) (pruneFolded b)
  | e => e

/-- `constraints` pruned when a body uses queries its closure did not make, so that every atom left
is one Rust's walk registers; the changed trees are recorded for the replay. -/
private def pruneBodies (constraints : Array (String × E)) : ConfigM (Array (String × E)) := do
  let closure := (← get).currentQueries.toList
  if constraints.all (·.2.declared closure) then return constraints
  constraints.mapM fun (name, p) => do
    let p' := pruneFolded p
    if p' != p then modify fun s => { s with prunedFrom := s.prunedFrom.push (p', p) }
    return (name, p')

def advice (column : Nat) (rotation : Int := 0) : ConfigM E :=
  query (.advice ⟨column⟩ rotation)

def fixed (column : Nat) (rotation : Int := 0) : ConfigM E :=
  query (.fixed ⟨column⟩ rotation)

def enableEquality (c : Halo2.AnyColumn) : ConfigM Unit := do
  let q := match c.kind with
    | .advice => Halo2.Query.advice ⟨c.index⟩ 0
    | .fixed => Halo2.Query.fixed ⟨c.index⟩ 0
    | .instance => Halo2.Query.instance ⟨c.index⟩ 0
  let _ ← query q
  modify fun s => { s with permutation := insertUnique s.permutation c }

/-- Port of `enable_constant` (`circuit.rs:1674`): the first enable appends the column to
`constants` and enables equality on it. -/
def enableConstant (column : Nat) : ConfigM Unit := do
  unless (← get).constantColumns.contains column do
    modify fun s => { s with constantColumns := s.constantColumns.push column }
    enableEquality ⟨.fixed, column⟩

/-- `constants[0]`, the column Rust's Simple planner assigns every deferred constant to. -/
def CS.constantColumn (s : CS) : Option Nat := s.constantColumns[0]?

def gate (name : String) (q : Halo2.Selector)
    (body : ConfigM (Array (String × E))) : ConfigM Unit := do
  modify fun s => { s with currentQueries := #[] }
  let constraints ← body
  if constraints.isEmpty then
    modify fun s => { s with errors := s.errors.push s!"gate {name}: expected a nonempty constraint body" }
    return
  let constraints ← pruneBodies constraints
  let rows := constraints.any fun (_, p) => !p.free
  let queries ← closeGate name (constraints.map fun (_, p) => Halo2.querySelector q * p) true
  modify fun s => { s with gates := s.gates.push ⟨name, q, queries, constraints, false, rows⟩ }

/-- `create_gate` returning `Constraints::with_additive_selector` (circuit.rs:2380): the batch
becomes a trash argument and the gate an empty entry, both with the closure's queries. -/
def additiveGate (name : String) (q : Halo2.Selector)
    (body : ConfigM (Array (String × E))) : ConfigM Unit := do
  modify fun s => { s with currentQueries := #[] }
  let constraints ← body
  if constraints.isEmpty then
    modify fun s => { s with errors := s.errors.push s!"gate {name}: expected a nonempty constraint body" }
    return
  let constraints ← pruneBodies constraints
  let rows := constraints.any fun (_, p) => !p.free
  let queries ← closeGate name (constraints.map (·.2)) false
  modify fun s => { s with
    gates := s.gates.push ⟨name, q, queries, #[], false, false⟩
    trashcans := s.trashcans.push ⟨name, q, queries, constraints, false, rows⟩ }

/-- `set_minimum_degree`. -/
def setMinimumDegree (degree : Nat) : ConfigM Unit :=
  modify fun s => { s with minimumDegree := some degree }

/-- `create_gate` returning `Constraints::without_selector`. Over one selector of which every
body has positive degree the gate is owned by it; otherwise it is a `rows` gate. `selectorCalls`
are the closure's `query_selector` calls. -/
def gateWithoutSelector (name : String) (body : ConfigM (Array (String × E)))
    (selectorCalls : Array Halo2.Selector := #[]) : ConfigM Unit := do
  modify fun s => { s with currentQueries := #[] }
  let constraints ← body
  if constraints.isEmpty then
    modify fun s => { s with errors := s.errors.push s!"gate {name}: expected a nonempty constraint body" }
    return
  let constraints ← pruneBodies constraints
  let owners := constraints.foldl (init := #[]) fun acc (_, p) =>
    p.queryAtoms.foldl (init := acc) fun acc q => match q with
      | .selector r => if acc.contains r then acc else acc.push r
      | _ => acc
  let q := owners[0]?.getD ⟨0, false⟩
  let spec : GateSpec := ⟨name, q, ← closeGate name (constraints.map (·.2)) true, constraints, true, false⟩
  let rows := owners.size != 1 || constraints.any fun (_, p) => !spec.bodyValid p
  modify fun s => { s with
    gates := s.gates.push { spec with rows := rows }
    gateSelectorCalls := if selectorCalls.isEmpty then s.gateSelectorCalls
      else s.gateSelectorCalls.push (s.gates.size, selectorCalls) }

/-- Rust's `Gate::queried_selectors` for gate `i`: its closure's `query_selector` calls, then
each selector the walk of its polynomials meets that is not yet listed (circuit.rs:2324,1916,744).
A `with_selector` or additive closure queries its owner to apply it (circuit.rs:2369), so that
owner stands for its calls, even when the walk finds nothing. -/
def CS.queriedSelectors (s : CS) (i : Nat) : Array Halo2.Selector :=
  match s.gates[i]? with
  | none => #[]
  | some g =>
    let calls := if g.raw then ((s.gateSelectorCalls.find? (·.1 == i)).map (·.2)).getD #[]
      else #[g.selector]
    (g.polynomials.toList.flatMap foldedAtoms).foldl (init := calls) fun acc q => match q with
      | .selector r => if acc.contains r then acc else acc.push r
      | _ => acc

/-- Rust's lookup `selector`: `None` is `Constant(1)` (logup.rs:308). -/
def lookupSelector : Option Halo2.Selector → E
  | some q => .var (.selector q)
  | none => .const 1

private def pushLookup (name : String) (q : Option Halo2.Selector) (any : Bool)
    (queries : Array Halo2.Query) (columns : Array (Array E × E)) : ConfigM Unit := do
  let parallel := (columns[0]?.map fun p => p.1.size).getD 0
  -- Rust indexes the first column and asserts the rest have its length (logup.rs:296-303).
  if columns.isEmpty || columns.any (fun (xs, _) => xs.size != parallel) then
    let message := s!"lookup {name}: expected a nonempty rectangular batch"
    modify fun s => { s with errors := s.errors.push message
                             rejectedLookups := s.rejectedLookups.push (name, lookupSelector q, columns, any) }
    return
  -- `batched_lookup_any` runs `query_cells` on each tuple's inputs, then its table
  -- (circuit.rs:1757-1771), registering queries no closure made.
  let s ← get
  let known : Halo2.Query → Bool
    | .advice c r => s.adviceQueries.contains (c.index, r)
    | .fixed c r => s.fixedQueries.contains (c.index, r)
    | .instance c r => s.instanceQueries.contains (c.index, r)
    | .selector _ => true
  let columns ← if columns.all fun (xs, t) => (xs.push t).all (·.queryAtoms.all known) then
      pure columns else do
    for (xs, t) in columns do
      for e in xs.push t do
        for atom in foldedAtoms e do registerQuery atom
    let prune := fun (e : E) => (do
      let e' := pruneFolded e
      if e' != e then modify fun s => { s with prunedFrom := s.prunedFrom.push (e', e) }
      return e' : ConfigM E)
    columns.mapM fun (xs, t) => return (← xs.mapM prune, ← prune t)
  let inputs := (Array.range parallel).map fun i =>
    columns.map fun (xs, _) => xs[i]?.getD (.const 0)
  let lookup : BatchedLookup := ⟨name, lookupSelector q, inputs, columns.map (·.2)⟩
  modify fun s => { s with
    lookups := s.lookups.push lookup
    lookupClosures := s.lookupClosures.push (lookup, queries, any) }

/-- Port of `batched_lookup`: query closure first, then query table columns,
then transpose from [width][parallel] to [parallel][width]. -/
def batchedLookup (name : String) (q : Option Halo2.Selector)
    (body : ConfigM (Array (Array E × Nat))) : ConfigM Unit := do
  let before := (← get).currentQueries.size
  let columns ← body
  let queries := (← get).currentQueries.extract before
  let table ← columns.mapM fun (_, c) => fixed c
  pushLookup name q false queries ((columns.zip table).map fun ((xs, _), t) => (xs, t))

/-- Port of `batched_lookup_any`: the table side is any expressions the closure builds, so every
query is registered in closure order (circuit.rs:1750-1780). -/
def batchedLookupAny (name : String) (q : Option Halo2.Selector)
    (body : ConfigM (Array (Array E × E))) : ConfigM Unit := do
  let before := (← get).currentQueries.size
  let columns ← body
  pushLookup name q true ((← get).currentQueries.extract before) columns

/-- Port of `lookup_any`: one input per table expression. -/
def lookupAny (name : String) (q : Option Halo2.Selector) (body : ConfigM (Array (E × E))) :
    ConfigM Unit :=
  batchedLookupAny name q do return (← body).map fun (x, t) => (#[x], t)

end Midnight.Keygen
