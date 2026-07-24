import Clean.Halo2.Expression
import Clean.Halo2.Tactics.SelectorFree

/-!
# Halo2 configure layer — DESIGN SKETCH

The configure layer defines the constraint system: custom gates, lookup arguments,
column allocation, equality-enabled columns. Chip `configure` functions are ported
verbatim from Rust.

**Why a monad**: column indices, selector indices, and gate *order* in the real
constraint system are execution-order artifacts of the Rust `configure()` calls.
Executing verbatim-ported configure code in a small state monad reproduces them by
construction; hand-maintaining them (10 advice + 29 fixed columns, 56 selectors,
gate order across all chips) would be unmaintainable and un-checkable.

**Why gate bodies are pure, and where query indices come from**: `Query` atoms carry no
query index, so `meta.query_advice` ports as the pure function `queryAdvice` and
`create_gate` closures become pure `Expression` terms — no `VirtualCells` state. But
query indices in Rust are execution-order artifacts of `configure()`: `query_*` register
`(column, rotation)` first-encounter *at closure call time*, i.e. in the closure's
`let`-order — which no walk over the finished polynomial AST can recover (let-order ≠
use-order, and unused atoms still register). So each `Gate` carries its atoms in
closure-call order (`queriedCells`, mirroring Rust's `Gate::queried_cells`,
`circuit.rs:894-901`), and the `Configure` actions perform the registration into
`cs.{advice,fixed,instance}Queries` — `createGate`/`enableEquality`/`enableConstant`/
`lookup` interleaved in execution order exactly as in Rust
(`query_*_index`, `circuit.rs:1081-1136`). See `query-registration-design.md`.

**Proofs never look inside `Configure`**: it is a data-construction device, run once to
produce config structs and the `ConstraintSystem`. The proof surface is the synthesize
layer (`Basic.lean`), which references gates as data. Formal gate packages
(`FormalAssertion` analogues binding a `Spec` to a gate) come with the formal-circuit
port.

Rust reference: `halo2_proofs/src/plonk/circuit.rs` (`ConstraintSystem`,
`create_gate`, `VirtualCells`, `Constraints::with_selector`).
-/

namespace Halo2

variable {F : Type}

/-!
## Pure query helpers

Verbatim-port counterparts of Rust `meta.query_*` inside `create_gate` closures.
-/

@[circuit_norm] def querySelector (s : Selector) : Expression F Query := var (.selector s)
/-- Rust `query_fixed` takes no rotation in this halo2 version (always the current row);
the `Query.fixed` constructor keeps a rotation for generality of the compiled CS. -/
@[circuit_norm, selector_free]
def queryFixed (c : Column .fixed) : Expression F Query := var (.fixed c 0)
@[circuit_norm, selector_free]
def queryAdvice (c : Column .advice) (rot : Rotation) : Expression F Query := var (.advice c rot)
@[circuit_norm, selector_free]
def queryInstance (c : Column .instance) (rot : Rotation) : Expression F Query := var (.instance c rot)

/--
An expression contains no simple selector. Halo 2 permits complex selectors in
lookup inputs but rejects simple selectors during lookup registration.
-/
@[circuit_norm]
def Expression.NoSimpleSelectors : Expression F Query → Prop
  | .var (.selector selector) => selector.simple = false
  | .var _ => True
  | .const _ => True
  | .add left right =>
      left.NoSimpleSelectors ∧ right.NoSimpleSelectors
  | .mul left right =>
      left.NoSimpleSelectors ∧ right.NoSimpleSelectors

/-- One named constraint of a custom gate. Rust: `Constraint<F>`. -/
structure Constraint (F : Type) where
  name : String := ""
  poly : Expression F Query

/-- A custom gate.

`constraints` are the **compiled** polynomials, verbatim as the Rust source builds them
— usually `Constraints.withSelector` shapes `q * poly`, but e.g. `witness_point` builds
`(q * x) * curve_eqn` manually for pinned-VK AST reasons. `selector` is the gate's
activation handle: per the selector survey (`halo2-selector-survey.md`), every gate in
scope is activated by exactly one simple `Selector`, and genuine selectors never occur
in a foreign gate's polynomials — so the semantics of enabling the gate at a row is
"all compiled polys vanish there under the valuation `selector ↦ 1`"
(see `FlatRegionOperation.Constraints`). The bridge to the CS view "`∀` rows, poly = 0 with the
actual 0/1 activation table" is a once-per-circuit lemma at the VK boundary.
-/
structure Gate (F : Type) where
  name : String
  selector : Selector
  /-- The gate closure's query atoms in Rust *call order* (`let`-order), mirroring
  `Gate::queried_cells` (`circuit.rs:894-901`) — the registration order for
  `cs.{advice,fixed,instance}Queries`, which the finished `constraints` AST does not
  determine. Entries are the same pure atoms the constraints use. Selector atoms do NOT
  belong here (selectors get no query index). Deliberately no default value: every gate
  author must transcribe the order from the Rust chip's `create_gate` closure. -/
  queriedCells : List (Expression F Query)
  constraints : List (Constraint F)

/-- Rust: `Constraints::with_selector(q, [(name, poly), …])` — multiplies every
constraint by the selector, building exactly the Rust AST `q * poly`. The defaulted
third argument requires every ungated polynomial to be selector-free; `selector_free`
discharges ordinary gate syntax, so call sites retain Rust's two-argument spelling.
`@[circuit_norm]`: part of the gate-reduction normal form, so proofs need not list this
combinator to reduce an enabled gate's constraint list. -/
@[circuit_norm]
def Constraints.withSelector (s : Selector)
    (constraints : List (String × Expression F Query))
    (_h : ∀ constraint ∈ constraints, constraint.2.SelectorFree := by
      selector_free) :
    List (Constraint F) :=
  constraints.map fun (name, poly) => { name, poly := querySelector s * poly }

/-- A lookup argument. Rust: `lookup::Argument<F>`
(`halo2_proofs/src/plonk/lookup.rs:7-11`): a tuple of input expressions and a tuple of
table expressions; the enforced relation is per-row membership of the input tuple in the
multiset of table rows (`lookup/prover.rs:565-628`; see `lookup-design.md` §1.2).

Both sides are `Expression F Query`. Rust registers `(Expression, TableColumn)` pairs but
immediately wraps each `TableColumn` with `query_fixed` (rotation 0)
(`circuit.rs:1068`), so the stored table side is always a rotation-0 fixed query — hence
`tables` is a `List (Expression F Query)`, matching ironwood's
`lookupTableExprs : Fin numLookups → List (Expr F)`. This is the pinned-CS form used for
VK comparison. SKETCH: the satisfaction *semantics* (an `enableLookup` region op + table
loading) is TBD with the lookup port — see `lookup-design.md`. -/
structure LookupArgument (F : Type) where
  inputs : List (Expression F Query)
  tables : List (Expression F Query)
  /-- Halo 2 rejects simple selectors in lookup input expressions. -/
  inputsNoSimpleSelectors :
    ∀ input ∈ inputs, input.NoSimpleSelectors
  /-- Halo 2 constructs the table side solely from lookup-table columns. -/
  tablesFree : ∀ table ∈ tables, table.SelectorFree
  /-- `lookup` receives pairs and unzips them, so both tuple sides have equal arity. -/
  arity : inputs.length = tables.length

deriving instance DecidableEq for Constraint
deriving instance DecidableEq for Gate
deriving instance DecidableEq for LookupArgument

/--
The constraint system under construction: the state of the `Configure` monad, mirroring
the builder role of Rust's `ConstraintSystem<F>`. Allocation counters plus accumulated
gates/lookups/permutation data, in creation order.
-/
structure ConstraintSystem (F : Type) where
  numAdviceColumns : ℕ := 0
  numFixedColumns : ℕ := 0
  numInstanceColumns : ℕ := 0
  numSelectors : ℕ := 0
  gates : List (Gate F) := []
  lookups : List (LookupArgument F) := []
  /-- Equality-enabled columns (the permutation argument's columns), in call order. -/
  permutationColumns : List AnyColumn := []
  /-- Columns that constants are assigned into (`enable_constant`). -/
  constants : List (Column .fixed) := []
  /-- Registered advice queries in first-encounter order, mirroring
  `cs.advice_queries` (`query_advice_index`, `circuit.rs:1096-1114`). Per-column counts
  give `num_advice_queries` (the input to `blinding_factors`). -/
  adviceQueries : List (Column .advice × Rotation) := []
  /-- Registered fixed queries, mirroring `cs.fixed_queries` (`circuit.rs:1081-1094`).
  Registration always inserts rotation 0 (`query_fixed` takes no rotation in this halo2
  version, `circuit.rs:1495-1503`); the `Rotation` field maps directly onto the pinned
  `fixedQueryLayout`. -/
  fixedQueries : List (Column .fixed × Rotation) := []
  /-- Registered instance queries, mirroring `cs.instance_queries`
  (`circuit.rs:1116-1126`). -/
  instanceQueries : List (Column .instance × Rotation) := []
  /-- Ill-formed `Gate.queriedCells`/`lookup` entries encountered during registration
  (owner name + description of the offending atom). Must stay `[]`; VK fixture tests
  `#guard` this. A poison list rather than `panic!` because `panic!` reduces silently to
  `default` under kernel evaluation (`#guard`/`decide`), which would hide the error in
  exactly the places that check the query layouts. -/
  invalidQueriedCells : List String := []

/-!
## Query registration

Internal first-encounter registration, mirroring Rust's `query_*_index`
(`circuit.rs:1081-1136`): return the existing index if `(column, rotation)` is already
present, else append. Gate authors never call these; they run inside `createGate`,
`enableEquality`, `enableConstant` and `lookup`.
-/

/-- Rust: `query_advice_index` (`circuit.rs:1096-1114`). -/
def ConstraintSystem.queryAdviceIndex (cs : ConstraintSystem F) (c : Column .advice)
    (rot : Rotation) : ConstraintSystem F :=
  if (c, rot) ∈ cs.adviceQueries then cs
  else { cs with adviceQueries := cs.adviceQueries ++ [(c, rot)] }

/-- Rust: `query_fixed_index` (`circuit.rs:1081-1094`); registration is always at
rotation 0 (§1 of `query-registration-design.md`). -/
def ConstraintSystem.queryFixedIndex (cs : ConstraintSystem F) (c : Column .fixed) :
    ConstraintSystem F :=
  if (c, (0 : Rotation)) ∈ cs.fixedQueries then cs
  else { cs with fixedQueries := cs.fixedQueries ++ [(c, 0)] }

/-- Rust: `query_instance_index` (`circuit.rs:1116-1126`). -/
def ConstraintSystem.queryInstanceIndex (cs : ConstraintSystem F) (c : Column .instance)
    (rot : Rotation) : ConstraintSystem F :=
  if (c, rot) ∈ cs.instanceQueries then cs
  else { cs with instanceQueries := cs.instanceQueries ++ [(c, rot)] }

/-- Rust: `query_any_index` at `Rotation::cur()` (`circuit.rs:1127-1136`), as used by
`enable_equality`. -/
def ConstraintSystem.queryAnyIndex (cs : ConstraintSystem F) (c : AnyColumn) :
    ConstraintSystem F :=
  match c with
  | ⟨.advice, i⟩ => cs.queryAdviceIndex ⟨i⟩ 0
  | ⟨.fixed, i⟩ => cs.queryFixedIndex ⟨i⟩
  | ⟨.instance, i⟩ => cs.queryInstanceIndex ⟨i⟩ 0

/-- Register one `queriedCells` entry. Only bare query atoms are well-formed; a selector
atom or a compound expression poisons `invalidQueriedCells` instead of being skipped. -/
def ConstraintSystem.registerQueriedCell (cs : ConstraintSystem F) (owner : String) :
    Expression F Query → ConstraintSystem F
  | var (.advice c rot) => cs.queryAdviceIndex c rot
  | var (.fixed c _) => cs.queryFixedIndex c
  | var (.instance c rot) => cs.queryInstanceIndex c rot
  | var (.selector _) => { cs with invalidQueriedCells := cs.invalidQueriedCells ++
      [s!"{owner}: selector atom in queriedCells (selectors get no query index)"] }
  | _ => { cs with invalidQueriedCells := cs.invalidQueriedCells ++
      [s!"{owner}: non-atom expression in queriedCells"] }

def ConstraintSystem.registerQueriedCells (cs : ConstraintSystem F) (owner : String)
    (cells : List (Expression F Query)) : ConstraintSystem F :=
  cells.foldl (fun cs e => cs.registerQueriedCell owner e) cs

/--
The configure monad: threads the `ConstraintSystem` being built. Mirrors passing
`meta : &mut ConstraintSystem<F>` through Rust configure code.
-/
abbrev Configure (F : Type) := StateM (ConstraintSystem F)

/-- Rust: `meta.advice_column()`. -/
def adviceColumn : Configure F (Column .advice) :=
  fun cs => (⟨cs.numAdviceColumns⟩, { cs with numAdviceColumns := cs.numAdviceColumns + 1 })

/-- Rust: `meta.fixed_column()`. -/
def fixedColumn : Configure F (Column .fixed) :=
  fun cs => (⟨cs.numFixedColumns⟩, { cs with numFixedColumns := cs.numFixedColumns + 1 })

/-- Rust: `meta.instance_column()`. -/
def instanceColumn : Configure F (Column .instance) :=
  fun cs => (⟨cs.numInstanceColumns⟩, { cs with numInstanceColumns := cs.numInstanceColumns + 1 })

/-- Rust: `meta.selector()` (a simple selector). -/
def selector : Configure F Selector :=
  fun cs => (⟨cs.numSelectors, true⟩, { cs with numSelectors := cs.numSelectors + 1 })

/-- Rust: `meta.complex_selector()`. -/
def complexSelector : Configure F Selector :=
  fun cs => (⟨cs.numSelectors, false⟩, { cs with numSelectors := cs.numSelectors + 1 })

/-- Rust: `meta.enable_equality(column)`. Idempotent, exactly like Rust's
`permutation::Argument::add_column` (`permutation.rs:61-65`: `if !columns.contains`),
which matters for VK-faithful permutation-column order when a column is
equality-enabled twice (e.g. `mul_fixed`'s `window`: once by `mul_fixed::configure`,
once by `RunningSumConfig::configure`).

Also registers a cur-rotation query on the column *before* the permutation append
(`circuit.rs:1046-1050`) — unconditionally, not gated on the column being new to the
permutation (idempotence comes from the `query_*_index` dedup). -/
def enableEquality (c : AnyColumn) : Configure F Unit :=
  fun cs =>
    let cs := cs.queryAnyIndex c
    ((), { cs with permutationColumns :=
      if c ∈ cs.permutationColumns then cs.permutationColumns
      else cs.permutationColumns ++ [c] })

/-- Rust: `meta.enable_constant(column)` (`circuit.rs:1038-1044`): registers the
constants column and enables equality on it (constants are enforced via copies into this
column) — including `enable_equality`'s cur fixed-query registration. -/
def enableConstant (col : Column .fixed) : Configure F Unit :=
  fun cs =>
    let cs := cs.queryFixedIndex col
    ((),
      { cs with
        constants := cs.constants ++ [col]
        permutationColumns :=
          if col.toAny ∈ cs.permutationColumns then cs.permutationColumns
          else cs.permutationColumns ++ [col.toAny] })

/-- Rust: `meta.lookup_table_column()`. -/
def lookupTableColumn : Configure F TableColumn := do
  return { inner := ← fixedColumn }

/-- Rust: `meta.create_gate(name, |meta| Constraints::with_selector(guard, [...]))`.
Registers the gate's `queriedCells` in list order (the closure's queries all execute
before the gate is pushed, `circuit.rs:1195-1229`), then appends the gate. -/
def createGate (gate : Gate F) : Configure F Unit :=
  fun cs =>
    let cs := cs.registerQueriedCells gate.name gate.queriedCells
    ((), { cs with gates := cs.gates ++ [gate] })

/-- Rust: `meta.lookup(|meta| table_map)` (`circuit.rs:1056-1079`). `table_map` is a list
of `(input, tableColumn)` pairs; each table column is wrapped as a rotation-0 fixed query
(`cells.query_fixed(table.inner())`) and the pairs are unzipped into the argument's
`inputs`/`tables`. Registered in call order (VK-relevant).

Rust also `panic!`s if any input contains a *simple* selector (`circuit.rs:1064`); that is
a well-formedness condition checked at the VK boundary, not enforced here (proofs never
depend on it). SKETCH: semantics (satisfaction) TBD with the lookup port.

`queriedCells` (mandatory, like `Gate.queriedCells`) is the table-map closure's query
atoms in call order; they register first (the closure runs before the pairs are
processed), then each pair's table column registers a cur fixed query
(`cells.query_fixed(table.inner())`, `circuit.rs:1068`). -/
def lookup (queriedCells : List (Expression F Query))
    (tableMap : List (Expression F Query × TableColumn))
    (_inputsNoSimpleSelectors :
      ∀ input ∈ tableMap.map Prod.fst,
        input.NoSimpleSelectors := by
      simp [Expression.NoSimpleSelectors]) :
    Configure F Unit :=
  let inputs := tableMap.map Prod.fst
  let tables : List (Expression F Query) :=
    tableMap.map fun (_, tbl) => queryFixed tbl.inner
  have tablesFree : ∀ table : Expression F Query,
      table ∈ tables → table.SelectorFree := by
    intro table htable
    obtain ⟨⟨_, tableColumn⟩, _, rfl⟩ := List.mem_map.mp htable
    simp [Expression.SelectorFree, queryFixed]
  have arity : inputs.length = tables.length := by
    simp [inputs, tables]
  fun cs =>
    let cs := cs.registerQueriedCells "lookup" queriedCells
    let cs := tableMap.foldl (fun cs (_, tbl) => cs.queryFixedIndex tbl.inner) cs
    ((), { cs with lookups :=
      cs.lookups ++ [{
        inputs
        tables
        inputsNoSimpleSelectors := by
          simpa only [inputs] using _inputsNoSimpleSelectors
        tablesFree
        arity }] })

end Halo2
