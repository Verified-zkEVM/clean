import Clean.Halo2.Expression
import Clean.Halo2.Tactics.SelectorFree
import Clean.Halo2.Tactics.QueryCorrect
import Clean.Halo2.ConfigureAttr
import Mathlib.Data.List.Dedup
import Mathlib.Data.List.MinMax

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

@[circuit_norm, query_correct]
def querySelector (s : Selector) : Expression F Query := var (.selector s)
/-- Rust `query_fixed` takes no rotation in this halo2 version (always the current row);
the `Query.fixed` constructor keeps a rotation for generality of the compiled CS. -/
@[circuit_norm, selector_free, query_correct]
def queryFixed (c : Column .fixed) : Expression F Query := var (.fixed c 0)
@[circuit_norm, selector_free, query_correct]
def queryAdvice (c : Column .advice) (rot : Rotation) : Expression F Query := var (.advice c rot)
@[circuit_norm, selector_free, query_correct]
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

/--
The local laws required of every custom gate.

Every selector atom in a constraint must name the gate's distinguished selector. At an
enabled row, selector compression replaces that selector by a nonzero field value; if
the resulting verifier-side polynomial vanishes, the same compiled polynomial must
vanish under Clean's selector-one valuation. No converse or exact scaling equation is
required.
-/
structure Gate.WellFormed
    (selector : Selector)
    (queriedCells : List (Expression F Query))
    (constraints : List (Constraint F)) : Prop where
  queriedCellsValid : queriedCells.Forall Expression.QueryAtom
  constraintQueriesDeclared :
    constraints.Forall fun constraint =>
      constraint.poly.QueriesDeclared queriedCells
  selectorsOwned :
    constraints.Forall fun constraint =>
      constraint.poly.selectorsCovered
        (fun index => decide (index = selector.index)) = true
  compressionSound :
    ∀ [Field F] (constraint : Constraint F), constraint ∈ constraints →
      ∀ (base : Query → F) (scale : F), scale ≠ 0 →
        constraint.poly.eval
            (Expression.replaceSelectorValue selector scale base) = 0 →
          constraint.poly.eval
            (Expression.enabledGateValuation selector base) = 0

/-- A custom gate.

`constraints` are the **compiled** polynomials, verbatim as the Rust source builds them
— usually `Gate.withSelector` shapes `q * poly`, but e.g. `witness_point` builds
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
  /-- Selector compression preserves vanishing in the direction required for
  verifier-to-Clean soundness. -/
  wellFormed : Gate.WellFormed selector queriedCells constraints

/--
Construct a gate in the standard Halo 2 form: multiply every selector-free ungated
polynomial by the gate selector, building exactly the Rust AST `q * poly`.

The defaulted proof is discharged by `selector_free`, so ordinary call sites carry no
proof boilerplate. The stronger selector-free construction rule implies the gate's
weaker one-sided `WellFormed` law automatically.
-/
@[circuit_norm]
def Gate.withSelector
    [Field F]
    (name : String) (selector : Selector)
    (queriedCells : List (Expression F Query))
    (constraints : List (String × Expression F Query))
    (hfree : ∀ constraint ∈ constraints, constraint.2.SelectorFree := by
      selector_free)
    (hqueries :
      queriedCells.Forall Expression.QueryAtom ∧
        constraints.Forall fun constraint =>
          constraint.2.QueriesDeclared queriedCells := by
      query_correct) :
    Gate F where
  name := name
  selector := selector
  queriedCells := queriedCells
  constraints :=
    constraints.map fun (constraintName, poly) =>
      { name := constraintName, poly := querySelector selector * poly }
  wellFormed := by
    refine ⟨hqueries.1, ?_, ?_, ?_⟩
    · rw [List.forall_iff_forall_mem]
      intro constraint hconstraint
      obtain ⟨⟨constraintName, poly⟩, hsource, rfl⟩ :=
        List.mem_map.mp hconstraint
      simp only [querySelector, Expression.QueriesDeclared, true_and]
      exact (List.forall_iff_forall_mem.mp hqueries.2)
        (constraintName, poly) hsource
    · rw [List.forall_iff_forall_mem]
      intro constraint hconstraint
      obtain ⟨⟨constraintName, poly⟩, hsource, rfl⟩ :=
        List.mem_map.mp hconstraint
      simp only [querySelector, Expression.selectorsCovered,
        decide_true, Bool.true_and]
      exact Expression.selectorsCovered_of_selectorFree
        (fun index => decide (index = selector.index))
        poly (hfree (constraintName, poly) hsource)
    · intro _ constraint hconstraint
      obtain ⟨⟨constraintName, poly⟩, hsource, rfl⟩ :=
        List.mem_map.mp hconstraint
      intro base scale hscale hzero
      have hpolyFree : poly.SelectorFree :=
        hfree (constraintName, poly) hsource
      have hpolyEval :
          poly.eval
              (Expression.replaceSelectorValue selector scale base) =
            poly.eval
              (Expression.enabledGateValuation selector base) := by
        apply Expression.eval_eq_of_selectorFree poly hpolyFree
        · intro _ _
          rfl
        · intro _ _
          rfl
        · intro _ _
          rfl
      simp only [querySelector, Expression.eval,
        Expression.replaceSelectorValue, if_pos] at hzero
      simp only [querySelector, Expression.eval,
        Expression.enabledGateValuation, if_pos, one_mul]
      rw [← hpolyEval]
      exact (mul_eq_zero.mp hzero).resolve_left hscale

@[simp] theorem Gate.withSelector_selector
    [Field F]
    (name : String) (selector : Selector)
    (queriedCells : List (Expression F Query))
    (constraints : List (String × Expression F Query))
    (hfree : ∀ constraint ∈ constraints,
      constraint.2.SelectorFree)
    (hqueries :
      queriedCells.Forall Expression.QueryAtom ∧
        constraints.Forall fun constraint =>
          constraint.2.QueriesDeclared queriedCells) :
    (Gate.withSelector name selector queriedCells constraints hfree hqueries).selector =
      selector :=
  rfl

open Lean Meta Simp in
/-- Reduce only a named gate's selector projection, without unfolding its constraints. -/
def foldGateSelectorProc : Simproc := fun expression => do
  unless expression.isAppOf ``Gate.selector do
    return .continue
  try
    let reduced ← withTransparency .default (whnf expression)
    if reduced == expression then
      return .continue
    let proof ← mkExpectedTypeHint
      (← mkEqRefl expression) (← mkEq expression reduced)
    return .visit { expr := reduced, proof? := some proof }
  catch _ =>
    return .continue

simproc foldGateSelector (Gate.selector _) := foldGateSelectorProc
attribute [configure_selector_norm] foldGateSelector

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

/--
The instance columns whose polynomials participate in verifier queries, preserving
their first-query order while forgetting duplicate rotations.
-/
def ConstraintSystem.queriedInstanceColumns
    (cs : ConstraintSystem F) : List (Column .instance) :=
  (cs.instanceQueries.map Prod.fst).dedup

@[simp] theorem ConstraintSystem.queriedInstanceColumns_nodup
    (cs : ConstraintSystem F) :
    cs.queriedInstanceColumns.Nodup :=
  List.nodup_dedup _

/-- A derived queried instance column has at least one registered rotation. -/
theorem ConstraintSystem.exists_rotation_mem_instanceQueries_of_mem_queriedInstanceColumns
    (cs : ConstraintSystem F) (column : Column .instance)
    (hcolumn : column ∈ cs.queriedInstanceColumns) :
    ∃ rotation, (column, rotation) ∈ cs.instanceQueries := by
  rw [queriedInstanceColumns, List.mem_dedup, List.mem_map] at hcolumn
  obtain ⟨⟨foundColumn, rotation⟩, hquery, hcolumn⟩ := hcolumn
  simp only at hcolumn
  subst foundColumn
  exact ⟨rotation, hquery⟩

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

theorem ConstraintSystem.mem_instanceQueries_queryInstanceIndex_of_mem
    (cs : ConstraintSystem F) (column : Column .instance)
    (rotation : Rotation) (query : Column .instance × Rotation)
    (hquery : query ∈ cs.instanceQueries) :
    query ∈ (cs.queryInstanceIndex column rotation).instanceQueries := by
  unfold queryInstanceIndex
  split <;> simp_all

theorem ConstraintSystem.mem_instanceQueries_queryAdviceIndex_of_mem
    (cs : ConstraintSystem F) (column : Column .advice)
    (rotation : Rotation) (query : Column .instance × Rotation)
    (hquery : query ∈ cs.instanceQueries) :
    query ∈ (cs.queryAdviceIndex column rotation).instanceQueries := by
  unfold queryAdviceIndex
  split <;> simp_all

theorem ConstraintSystem.mem_instanceQueries_queryFixedIndex_of_mem
    (cs : ConstraintSystem F) (column : Column .fixed)
    (query : Column .instance × Rotation)
    (hquery : query ∈ cs.instanceQueries) :
    query ∈ (cs.queryFixedIndex column).instanceQueries := by
  unfold queryFixedIndex
  split <;> simp_all

theorem ConstraintSystem.mem_instanceQueries_registerQueriedCell_of_mem
    (cs : ConstraintSystem F) (owner : String)
    (cell : Expression F Query)
    (query : Column .instance × Rotation)
    (hquery : query ∈ cs.instanceQueries) :
    query ∈ (cs.registerQueriedCell owner cell).instanceQueries := by
  cases cell with
  | var queried =>
      cases queried with
      | selector =>
          exact hquery
      | fixed column _ =>
          exact cs.mem_instanceQueries_queryFixedIndex_of_mem
            column query hquery
      | advice column rotation =>
          exact cs.mem_instanceQueries_queryAdviceIndex_of_mem
            column rotation query hquery
      | «instance» column rotation =>
          exact cs.mem_instanceQueries_queryInstanceIndex_of_mem
            column rotation query hquery
  | const =>
      exact hquery
  | add =>
      exact hquery
  | mul =>
      exact hquery

theorem ConstraintSystem.mem_instanceQueries_registerQueriedCells_of_mem
    (cs : ConstraintSystem F) (owner : String)
    (cells : List (Expression F Query))
    (query : Column .instance × Rotation)
    (hquery : query ∈ cs.instanceQueries) :
    query ∈ (cs.registerQueriedCells owner cells).instanceQueries := by
  induction cells generalizing cs with
  | nil =>
      exact hquery
  | cons cell cells ih =>
      rw [registerQueriedCells, List.foldl_cons]
      apply ih
      exact cs.mem_instanceQueries_registerQueriedCell_of_mem
        owner cell query hquery

/-- Allocation counters threaded through configure programs. -/
structure ConfigureCounts where
  numAdviceColumns : ℕ := 0
  numFixedColumns : ℕ := 0
  numInstanceColumns : ℕ := 0
  numSelectors : ℕ := 0

/-- Componentwise growth of configure allocation counters. -/
structure ConfigureCounts.ComponentwiseLE
    (source target : ConfigureCounts) : Prop where
  numAdviceColumns : source.numAdviceColumns ≤ target.numAdviceColumns
  numFixedColumns : source.numFixedColumns ≤ target.numFixedColumns
  numInstanceColumns : source.numInstanceColumns ≤ target.numInstanceColumns
  numSelectors : source.numSelectors ≤ target.numSelectors

/-- Query atoms may only refer to columns already allocated at their configure point. -/
def Expression.QueryAllocated (counts : ConfigureCounts) :
    Expression F Query → Prop
  | .var (.advice column _) => column.index < counts.numAdviceColumns
  | .var (.fixed column _) => column.index < counts.numFixedColumns
  | .var (.instance column _) => column.index < counts.numInstanceColumns
  | _ => False

@[simp] theorem Expression.queryAllocated_queryAdvice
    (counts : ConfigureCounts) (column : Column .advice) (rotation : Rotation) :
    (queryAdvice (F := F) column rotation).QueryAllocated counts ↔
      column.index < counts.numAdviceColumns :=
  Iff.rfl

@[simp] theorem Expression.queryAllocated_queryFixed
    (counts : ConfigureCounts) (column : Column .fixed) :
    (queryFixed (F := F) column).QueryAllocated counts ↔
      column.index < counts.numFixedColumns :=
  Iff.rfl

@[simp] theorem Expression.queryAllocated_queryInstance
    (counts : ConfigureCounts) (column : Column .instance) (rotation : Rotation) :
    (queryInstance (F := F) column rotation).QueryAllocated counts ↔
      column.index < counts.numInstanceColumns :=
  Iff.rfl

/-- A type-erased column reference is allocated at a configure point. -/
def AnyColumn.Allocated (counts : ConfigureCounts) (column : AnyColumn) : Prop :=
  match column with
  | ⟨.advice, index⟩ => index < counts.numAdviceColumns
  | ⟨.fixed, index⟩ => index < counts.numFixedColumns
  | ⟨.instance, index⟩ => index < counts.numInstanceColumns

theorem ConfigureCounts.ComponentwiseLE.trans
    {first second third : ConfigureCounts}
    (hfirst : first.ComponentwiseLE second)
    (hsecond : second.ComponentwiseLE third) :
    first.ComponentwiseLE third where
  numAdviceColumns := hfirst.numAdviceColumns.trans hsecond.numAdviceColumns
  numFixedColumns := hfirst.numFixedColumns.trans hsecond.numFixedColumns
  numInstanceColumns := hfirst.numInstanceColumns.trans hsecond.numInstanceColumns
  numSelectors := hfirst.numSelectors.trans hsecond.numSelectors

theorem Expression.QueryAllocated.mono
    {source target : ConfigureCounts} {expression : Expression F Query}
    (hquery : expression.QueryAllocated source)
    (hcounts : source.ComponentwiseLE target) :
    expression.QueryAllocated target := by
  cases expression with
  | var query =>
      cases query with
      | selector => simp_all [Expression.QueryAllocated]
      | fixed =>
          exact hquery.trans_le hcounts.numFixedColumns
      | advice =>
          exact hquery.trans_le hcounts.numAdviceColumns
      | «instance» =>
          exact hquery.trans_le hcounts.numInstanceColumns
  | const | add | mul =>
      simp_all [Expression.QueryAllocated]

/--
The additive allocation contribution of a configure program.

Unlike a freely returned final `ConfigureCounts`, this representation makes decreasing
an allocation counter unrepresentable.
-/
structure ConfigureCountDelta where
  numAdviceColumns : ℕ := 0
  numFixedColumns : ℕ := 0
  numInstanceColumns : ℕ := 0
  numSelectors : ℕ := 0

def ConfigureCountDelta.apply
    (delta : ConfigureCountDelta) (initial : ConfigureCounts) :
    ConfigureCounts where
  numAdviceColumns :=
    initial.numAdviceColumns + delta.numAdviceColumns
  numFixedColumns :=
    initial.numFixedColumns + delta.numFixedColumns
  numInstanceColumns :=
    initial.numInstanceColumns + delta.numInstanceColumns
  numSelectors :=
    initial.numSelectors + delta.numSelectors

/-- Applying an append-only allocation delta can only increase counters. -/
theorem ConfigureCountDelta.componentwiseLE_apply
    (delta : ConfigureCountDelta) (initial : ConfigureCounts) :
    initial.ComponentwiseLE (delta.apply initial) := by
  constructor <;> simp [ConfigureCountDelta.apply]

def ConfigureCountDelta.append
    (left right : ConfigureCountDelta) : ConfigureCountDelta where
  numAdviceColumns :=
    left.numAdviceColumns + right.numAdviceColumns
  numFixedColumns :=
    left.numFixedColumns + right.numFixedColumns
  numInstanceColumns :=
    left.numInstanceColumns + right.numInstanceColumns
  numSelectors :=
    left.numSelectors + right.numSelectors

@[simp] theorem ConfigureCountDelta.apply_append
    (left right : ConfigureCountDelta) (initial : ConfigureCounts) :
    (left.append right).apply initial =
      right.apply (left.apply initial) := by
  cases initial
  cases left
  cases right
  simp [ConfigureCountDelta.append, ConfigureCountDelta.apply,
    Nat.add_assoc]

theorem ConfigureCountDelta.numSelectors_le_apply
    (delta : ConfigureCountDelta) (initial : ConfigureCounts) :
    initial.numSelectors ≤ (delta.apply initial).numSelectors := by
  simp only [ConfigureCountDelta.apply]
  omega

def ConfigureCounts.ofConstraintSystem (cs : ConstraintSystem F) :
    ConfigureCounts where
  numAdviceColumns := cs.numAdviceColumns
  numFixedColumns := cs.numFixedColumns
  numInstanceColumns := cs.numInstanceColumns
  numSelectors := cs.numSelectors

@[simp] theorem ConfigureCounts.ofConstraintSystem_empty :
    ConfigureCounts.ofConstraintSystem ({} : ConstraintSystem F) = {} :=
  rfl

/--
The append-only contribution of a configure program.

Lists contain raw requests in program order. The final interpreter performs Halo2's
first-encounter deduplication against the initial constraint system.
-/
structure ConfigureDelta (F : Type) where
  gates : List (Gate F) := []
  lookups : List (LookupArgument F) := []
  permutationRequests : List AnyColumn := []
  constants : List (Column .fixed) := []
  adviceQueries : List (Column .advice × Rotation) := []
  fixedQueries : List (Column .fixed × Rotation) := []
  instanceQueries : List (Column .instance × Rotation) := []
  invalidQueriedCells : List String := []

/-- An ordinary query is registered by this configure contribution. Selectors are
allocated separately and therefore do not occupy a query-layout slot. -/
def ConfigureDelta.RegistersQuery
    (delta : ConfigureDelta F) : Query → Prop
  | .selector _ => True
  | .advice column rotation => (column, rotation) ∈ delta.adviceQueries
  | .fixed column rotation => (column, rotation) ∈ delta.fixedQueries
  | .instance column rotation => (column, rotation) ∈ delta.instanceQueries

/-- Every ordinary query used by an expression is registered by the configure
contribution that emits the expression. -/
def Expression.QueriesRegistered
    (delta : ConfigureDelta F) : Expression F Query → Prop
  | .var query => delta.RegistersQuery query
  | .const _ => True
  | .add left right =>
      left.QueriesRegistered delta ∧ right.QueriesRegistered delta
  | .mul left right =>
      left.QueriesRegistered delta ∧ right.QueriesRegistered delta

/-- All expressions of a gate resolve against the configure contribution's query
layout. -/
def Gate.QueriesRegistered (delta : ConfigureDelta F) (gate : Gate F) : Prop :=
  gate.constraints.Forall fun constraint =>
    constraint.poly.QueriesRegistered delta

/-- Every query atom declared by a gate was registered by the configure program that
emitted the gate. This is stronger than expression coverage in the useful direction:
parents can reason directly from the gate-local query declaration. -/
def Gate.QueriedCellsRegistered (delta : ConfigureDelta F) (gate : Gate F) : Prop :=
  gate.queriedCells.Forall (·.QueriesRegistered delta)

/-- Both sides of a lookup resolve against the configure contribution's query
layout. -/
def LookupArgument.QueriesRegistered
    (delta : ConfigureDelta F) (lookup : LookupArgument F) : Prop :=
  lookup.inputs.Forall (·.QueriesRegistered delta) ∧
    lookup.tables.Forall (·.QueriesRegistered delta)

/-- The rotation-zero query needed to evaluate a permutation column is present in
this configure contribution. -/
def ConfigureDelta.RegistersPermutationColumn
    (delta : ConfigureDelta F) : AnyColumn → Prop
  | ⟨.advice, index⟩ => (⟨index⟩, 0) ∈ delta.adviceQueries
  | ⟨.fixed, index⟩ => (⟨index⟩, 0) ∈ delta.fixedQueries
  | ⟨.instance, index⟩ => (⟨index⟩, 0) ∈ delta.instanceQueries

def ConfigureDelta.append (left right : ConfigureDelta F) : ConfigureDelta F where
  gates := left.gates ++ right.gates
  lookups := left.lookups ++ right.lookups
  permutationRequests :=
    left.permutationRequests ++ right.permutationRequests
  constants := left.constants ++ right.constants
  adviceQueries := left.adviceQueries ++ right.adviceQueries
  fixedQueries := left.fixedQueries ++ right.fixedQueries
  instanceQueries := left.instanceQueries ++ right.instanceQueries
  invalidQueriedCells :=
    left.invalidQueriedCells ++ right.invalidQueriedCells

theorem ConfigureDelta.RegistersQuery.append_left
    {left right : ConfigureDelta F} {query : Query}
    (hquery : left.RegistersQuery query) :
    (left.append right).RegistersQuery query := by
  cases query with
  | selector => trivial
  | advice | fixed | «instance» =>
      simpa [ConfigureDelta.RegistersQuery, ConfigureDelta.append] using
        List.mem_append_left _ hquery

theorem ConfigureDelta.RegistersQuery.append_right
    {left right : ConfigureDelta F} {query : Query}
    (hquery : right.RegistersQuery query) :
    (left.append right).RegistersQuery query := by
  cases query with
  | selector => trivial
  | advice | fixed | «instance» =>
      simpa [ConfigureDelta.RegistersQuery, ConfigureDelta.append] using
        List.mem_append_right _ hquery

theorem ConfigureDelta.RegistersPermutationColumn.append_left
    {left right : ConfigureDelta F} {column : AnyColumn}
    (hcolumn : left.RegistersPermutationColumn column) :
    (left.append right).RegistersPermutationColumn column := by
  rcases column with ⟨kind, index⟩
  cases kind <;>
    simpa [ConfigureDelta.RegistersPermutationColumn,
      ConfigureDelta.append] using List.mem_append_left _ hcolumn

theorem ConfigureDelta.RegistersPermutationColumn.append_right
    {left right : ConfigureDelta F} {column : AnyColumn}
    (hcolumn : right.RegistersPermutationColumn column) :
    (left.append right).RegistersPermutationColumn column := by
  rcases column with ⟨kind, index⟩
  cases kind <;>
    simpa [ConfigureDelta.RegistersPermutationColumn,
      ConfigureDelta.append] using List.mem_append_right _ hcolumn

theorem Expression.QueriesRegistered.append_left
    {left right : ConfigureDelta F} {expression : Expression F Query}
    (hqueries : expression.QueriesRegistered left) :
    expression.QueriesRegistered (left.append right) := by
  induction expression with
  | var query =>
      exact ConfigureDelta.RegistersQuery.append_left hqueries
  | const => trivial
  | add _ _ ihLeft ihRight | mul _ _ ihLeft ihRight =>
      exact ⟨ihLeft hqueries.1, ihRight hqueries.2⟩

theorem Expression.QueriesRegistered.append_right
    {left right : ConfigureDelta F} {expression : Expression F Query}
    (hqueries : expression.QueriesRegistered right) :
    expression.QueriesRegistered (left.append right) := by
  induction expression with
  | var query =>
      exact ConfigureDelta.RegistersQuery.append_right hqueries
  | const => trivial
  | add _ _ ihLeft ihRight | mul _ _ ihLeft ihRight =>
      exact ⟨ihLeft hqueries.1, ihRight hqueries.2⟩

theorem Gate.QueriesRegistered.append_left
    {left right : ConfigureDelta F} {gate : Gate F}
    (hqueries : gate.QueriesRegistered left) :
    gate.QueriesRegistered (left.append right) := by
  exact hqueries.imp fun _ hconstraint => hconstraint.append_left

theorem Gate.QueriesRegistered.append_right
    {left right : ConfigureDelta F} {gate : Gate F}
    (hqueries : gate.QueriesRegistered right) :
    gate.QueriesRegistered (left.append right) := by
  exact hqueries.imp fun _ hconstraint => hconstraint.append_right

theorem Gate.QueriedCellsRegistered.append_left
    {left right : ConfigureDelta F} {gate : Gate F}
    (hqueries : gate.QueriedCellsRegistered left) :
    gate.QueriedCellsRegistered (left.append right) := by
  exact hqueries.imp fun _ hquery => hquery.append_left

theorem Gate.QueriedCellsRegistered.append_right
    {left right : ConfigureDelta F} {gate : Gate F}
    (hqueries : gate.QueriedCellsRegistered right) :
    gate.QueriedCellsRegistered (left.append right) := by
  exact hqueries.imp fun _ hquery => hquery.append_right

theorem LookupArgument.QueriesRegistered.append_left
    {left right : ConfigureDelta F} {lookup : LookupArgument F}
    (hqueries : lookup.QueriesRegistered left) :
    lookup.QueriesRegistered (left.append right) := by
  exact ⟨hqueries.1.imp fun _ hinput => hinput.append_left,
    hqueries.2.imp fun _ htable => htable.append_left⟩

theorem LookupArgument.QueriesRegistered.append_right
    {left right : ConfigureDelta F} {lookup : LookupArgument F}
    (hqueries : lookup.QueriesRegistered right) :
    lookup.QueriesRegistered (left.append right) := by
  exact ⟨hqueries.1.imp fun _ hinput => hinput.append_right,
    hqueries.2.imp fun _ htable => htable.append_right⟩

private def appendFirstEncounters {α : Type} [DecidableEq α]
    (initial requests : List α) : List α :=
  requests.foldl
    (fun accumulated request =>
      if request ∈ accumulated then accumulated
      else accumulated ++ [request])
    initial

theorem mem_appendFirstEncounters {α : Type} [DecidableEq α]
    (value : α) (initial requests : List α) :
    value ∈ appendFirstEncounters initial requests ↔
      value ∈ initial ∨ value ∈ requests := by
  induction requests generalizing initial with
  | nil =>
      simp [appendFirstEncounters]
  | cons request requests ih =>
      rw [appendFirstEncounters, List.foldl_cons]
      change
        value ∈ appendFirstEncounters
            (if request ∈ initial then initial
              else initial ++ [request])
            requests ↔
          value ∈ initial ∨ value ∈ request :: requests
      rw [ih]
      by_cases hrequest : request ∈ initial
      · simp only [hrequest, if_pos, List.mem_cons]
        constructor
        · intro h
          exact h.elim Or.inl (fun htail => Or.inr (Or.inr htail))
        · rintro (hinitial | heq | htail)
          · exact Or.inl hinitial
          · subst value
            exact Or.inl hrequest
          · exact Or.inr htail
      · simp [hrequest, or_assoc, or_left_comm]

def ConfigureDelta.apply (delta : ConfigureDelta F)
    (initial : ConstraintSystem F) (counts : ConfigureCounts) :
    ConstraintSystem F where
  numAdviceColumns := counts.numAdviceColumns
  numFixedColumns := counts.numFixedColumns
  numInstanceColumns := counts.numInstanceColumns
  numSelectors := counts.numSelectors
  gates := initial.gates ++ delta.gates
  lookups := initial.lookups ++ delta.lookups
  permutationColumns :=
    appendFirstEncounters initial.permutationColumns
      delta.permutationRequests
  constants := initial.constants ++ delta.constants
  adviceQueries :=
    appendFirstEncounters initial.adviceQueries delta.adviceQueries
  fixedQueries :=
    appendFirstEncounters initial.fixedQueries delta.fixedQueries
  instanceQueries :=
    appendFirstEncounters initial.instanceQueries delta.instanceQueries
  invalidQueriedCells :=
    initial.invalidQueriedCells ++ delta.invalidQueriedCells

/--
The configure monad, in the same append-only style as `Circuit`.

Allocation counters are threaded state; every other constraint-system contribution is
written to `ConfigureDelta`. The `CoeFun` instance preserves the existing `program cs`
interface by interpreting that delta at the boundary.
-/
structure Configure (F : Type) (α : Type) where
  plan : ConfigureCounts →
    α × ConfigureDelta F × ConfigureCountDelta

namespace Configure

variable {α β : Type}

def output (program : Configure F α) (counts : ConfigureCounts) : α :=
  (program.plan counts).1

def delta (program : Configure F α) (counts : ConfigureCounts) :
    ConfigureDelta F :=
  (program.plan counts).2.1

theorem delta_permutationRequests (program : Configure F α)
    (counts : ConfigureCounts) :
    (program.delta counts).permutationRequests =
      (program.plan counts).2.1.permutationRequests :=
  rfl

def countDelta (program : Configure F α) (counts : ConfigureCounts) :
    ConfigureCountDelta :=
  (program.plan counts).2.2

def finalCounts (program : Configure F α) (counts : ConfigureCounts) :
    ConfigureCounts :=
  (program.countDelta counts).apply counts

theorem finalCounts_numAdviceColumns
    (program : Configure F α) (counts : ConfigureCounts) :
    (program.finalCounts counts).numAdviceColumns =
      counts.numAdviceColumns +
        (program.countDelta counts).numAdviceColumns :=
  rfl

theorem finalCounts_numFixedColumns
    (program : Configure F α) (counts : ConfigureCounts) :
    (program.finalCounts counts).numFixedColumns =
      counts.numFixedColumns +
        (program.countDelta counts).numFixedColumns :=
  rfl

theorem finalCounts_numInstanceColumns
    (program : Configure F α) (counts : ConfigureCounts) :
    (program.finalCounts counts).numInstanceColumns =
      counts.numInstanceColumns +
        (program.countDelta counts).numInstanceColumns :=
  rfl

theorem finalCounts_numSelectors
    (program : Configure F α) (counts : ConfigureCounts) :
    (program.finalCounts counts).numSelectors =
      counts.numSelectors + (program.countDelta counts).numSelectors :=
  rfl

/-- Configure programs can only increase allocation counters. -/
theorem counts_componentwiseLE_finalCounts
    (program : Configure F α) (counts : ConfigureCounts) :
    counts.ComponentwiseLE (program.finalCounts counts) :=
  ConfigureCountDelta.componentwiseLE_apply
    (program.countDelta counts) counts

/-- Configure programs can only increase the selector allocation count. -/
theorem numSelectors_le_finalCounts
    (program : Configure F α) (counts : ConfigureCounts) :
    counts.numSelectors ≤ (program.finalCounts counts).numSelectors :=
  (program.counts_componentwiseLE_finalCounts counts).numSelectors

def run (program : Configure F α) (initial : ConstraintSystem F) :
    α × ConstraintSystem F :=
  let counts := ConfigureCounts.ofConstraintSystem initial
  let (output, delta, countDelta) := program.plan counts
  (output, delta.apply initial (countDelta.apply counts))

@[simp] theorem run_numAdviceColumns
    (program : Configure F α) (initial : ConstraintSystem F) :
    (program.run initial).2.numAdviceColumns =
      (program.finalCounts
        (ConfigureCounts.ofConstraintSystem initial)).numAdviceColumns :=
  rfl

@[simp] theorem run_numFixedColumns
    (program : Configure F α) (initial : ConstraintSystem F) :
    (program.run initial).2.numFixedColumns =
      (program.finalCounts
        (ConfigureCounts.ofConstraintSystem initial)).numFixedColumns :=
  rfl

@[simp] theorem run_numInstanceColumns
    (program : Configure F α) (initial : ConstraintSystem F) :
    (program.run initial).2.numInstanceColumns =
      (program.finalCounts
      (ConfigureCounts.ofConstraintSystem initial)).numInstanceColumns :=
  rfl

theorem mem_adviceQueries_run_iff
    (program : Configure F α) (initial : ConstraintSystem F)
    (query : Column .advice × Rotation) :
    query ∈ (program.run initial).2.adviceQueries ↔
      query ∈ initial.adviceQueries ∨
        query ∈
          (program.delta
            (ConfigureCounts.ofConstraintSystem initial)).adviceQueries := by
  simp only [run, delta, ConfigureDelta.apply, mem_appendFirstEncounters]

theorem mem_instanceQueries_run_iff
    (program : Configure F α) (initial : ConstraintSystem F)
    (query : Column .instance × Rotation) :
    query ∈ (program.run initial).2.instanceQueries ↔
      query ∈ initial.instanceQueries ∨
        query ∈
          (program.delta
            (ConfigureCounts.ofConstraintSystem initial)).instanceQueries := by
  simp only [run, delta, ConfigureDelta.apply, mem_appendFirstEncounters]

theorem mem_fixedQueries_run_iff
    (program : Configure F α) (initial : ConstraintSystem F)
    (query : Column .fixed × Rotation) :
    query ∈ (program.run initial).2.fixedQueries ↔
      query ∈ initial.fixedQueries ∨
        query ∈
          (program.delta
            (ConfigureCounts.ofConstraintSystem initial)).fixedQueries := by
  simp only [run, delta, ConfigureDelta.apply, mem_appendFirstEncounters]

theorem mem_permutationColumns_run_iff
    (program : Configure F α) (initial : ConstraintSystem F)
    (column : AnyColumn) :
    column ∈ (program.run initial).2.permutationColumns ↔
      column ∈ initial.permutationColumns ∨
        column ∈
          (program.delta
            (ConfigureCounts.ofConstraintSystem initial)).permutationRequests := by
  simp only [run, delta, ConfigureDelta.apply, mem_appendFirstEncounters]

instance : CoeFun (Configure F α)
    (fun _ => ConstraintSystem F → α × ConstraintSystem F) where
  coe := run

instance : Monad (Configure F) where
  pure value := ⟨fun _ => (value, {}, {})⟩
  bind program next := ⟨fun counts =>
    let (output, delta, countDelta) := program.plan counts
    let nextCounts := countDelta.apply counts
    let (nextOutput, nextDelta, nextCountDelta) :=
      (next output).plan nextCounts
    (nextOutput, delta.append nextDelta,
      countDelta.append nextCountDelta)⟩

end Configure

def ConfigureDelta.queryAny (column : AnyColumn) : ConfigureDelta F :=
  match column with
  | ⟨.advice, index⟩ =>
      { adviceQueries := [(⟨index⟩, 0)] }
  | ⟨.fixed, index⟩ =>
      { fixedQueries := [(⟨index⟩, 0)] }
  | ⟨.instance, index⟩ =>
      { instanceQueries := [(⟨index⟩, 0)] }

@[simp]
theorem ConfigureDelta.gates_queryAny (column : AnyColumn) :
    (ConfigureDelta.queryAny (F := F) column).gates = [] := by
  rcases column with ⟨kind, index⟩
  cases kind <;> rfl

@[simp]
theorem ConfigureDelta.lookups_queryAny (column : AnyColumn) :
    (ConfigureDelta.queryAny (F := F) column).lookups = [] := by
  rcases column with ⟨kind, index⟩
  cases kind <;> rfl

theorem ConfigureDelta.permutationRequests_queryAny (column : AnyColumn) :
    (ConfigureDelta.queryAny (F := F) column).permutationRequests = [] := by
  rcases column with ⟨kind, index⟩
  cases kind <;> rfl

def ConfigureDelta.queriedCell (owner : String) :
    Expression F Query → ConfigureDelta F
  | .var (.advice column rotation) =>
      { adviceQueries := [(column, rotation)] }
  | .var (.fixed column _) =>
      { fixedQueries := [(column, 0)] }
  | .var (.instance column rotation) =>
      { instanceQueries := [(column, rotation)] }
  | .var (.selector _) =>
      { invalidQueriedCells :=
        [s!"{owner}: selector atom in queriedCells (selectors get no query index)"] }
  | _ =>
      { invalidQueriedCells :=
        [s!"{owner}: non-atom expression in queriedCells"] }

def ConfigureDelta.queriedCells (owner : String)
    (cells : List (Expression F Query)) : ConfigureDelta F :=
  cells.foldl
    (fun delta cell => delta.append (.queriedCell owner cell)) {}

/-- Rotation-zero fixed-query requests emitted by lookup table columns, in program
order. -/
def ConfigureDelta.fixedQueriesOfColumns
    (columns : List TableColumn) : ConfigureDelta F :=
  columns.foldl
    (fun delta column =>
      delta.append { fixedQueries := [(column.inner, 0)] }) {}

theorem ConfigureDelta.queriedCell_registersQuery
    (owner : String) {query : Query}
    (hvalid : (Expression.var query : Expression F Query).QueryAtom) :
    (ConfigureDelta.queriedCell (F := F) owner (.var query)).RegistersQuery query := by
  cases query with
  | selector => trivial
  | advice | «instance» =>
      simp [ConfigureDelta.queriedCell, ConfigureDelta.RegistersQuery]
  | fixed column rotation =>
      simp only [Expression.QueryAtom] at hvalid
      subst rotation
      simp [ConfigureDelta.queriedCell, ConfigureDelta.RegistersQuery]

/-- Every valid query declaration is registered by the delta produced from the full
declaration list. -/
theorem ConfigureDelta.queriedCells_registersQuery_of_mem
    (owner : String) {cells : List (Expression F Query)} {query : Query}
    (hvalid : cells.Forall Expression.QueryAtom)
    (hquery : (Expression.var query : Expression F Query) ∈ cells) :
    (ConfigureDelta.queriedCells owner cells).RegistersQuery query := by
  unfold ConfigureDelta.queriedCells
  have aux (remaining : List (Expression F Query))
      (initial : ConfigureDelta F)
      (hremaining : remaining.Forall Expression.QueryAtom)
      (hquery : initial.RegistersQuery query ∨
        (Expression.var query : Expression F Query) ∈ remaining) :
      (remaining.foldl
        (fun delta cell => delta.append (.queriedCell owner cell))
        initial).RegistersQuery query := by
    induction remaining generalizing initial with
    | nil => simpa using hquery
    | cons cell remaining ih =>
        rw [List.foldl_cons]
        rw [List.forall_cons] at hremaining
        apply ih
        · exact hremaining.2
        · rcases hquery with hregistered | hquery
          · exact Or.inl hregistered.append_left
          · rw [List.mem_cons] at hquery
            rcases hquery with rfl | hquery
            · exact Or.inl
                (ConfigureDelta.queriedCell_registersQuery
                  owner hremaining.1).append_right
            · exact Or.inr hquery
  exact aux cells {} hvalid (Or.inr hquery)

/-- Every valid atom in a gate's query declaration is registered by the declaration
writer itself. -/
theorem ConfigureDelta.queriedCells_queriesRegistered
    (owner : String) {cells : List (Expression F Query)}
    (hvalid : cells.Forall Expression.QueryAtom) :
    cells.Forall
      (·.QueriesRegistered (ConfigureDelta.queriedCells owner cells)) := by
  rw [List.forall_iff_forall_mem]
  intro cell hcell
  have hatom := List.forall_iff_forall_mem.mp hvalid cell hcell
  cases cell with
  | var query =>
      cases query with
      | selector => simp [Expression.QueryAtom] at hatom
      | advice | «instance» =>
          exact ConfigureDelta.queriedCells_registersQuery_of_mem
            owner hvalid hcell
      | fixed column rotation =>
          simp only [Expression.QueryAtom] at hatom
          subst rotation
          exact ConfigureDelta.queriedCells_registersQuery_of_mem
            owner hvalid hcell
  | const | add | mul => simp [Expression.QueryAtom] at hatom

/-- Syntactic query declaration entails semantic registration by the corresponding
configure delta. -/
theorem Expression.QueriesDeclared.queriesRegistered_queriedCells
    (owner : String) {cells : List (Expression F Query)}
    {expression : Expression F Query}
    (hvalid : cells.Forall Expression.QueryAtom)
    (hdeclared : expression.QueriesDeclared cells) :
    expression.QueriesRegistered (ConfigureDelta.queriedCells owner cells) := by
  induction expression with
  | var query =>
      cases query with
      | selector => trivial
      | advice | fixed | «instance» =>
          exact ConfigureDelta.queriedCells_registersQuery_of_mem
            owner hvalid hdeclared
  | const => trivial
  | add _ _ ihLeft ihRight | mul _ _ ihLeft ihRight =>
      exact ⟨ihLeft hdeclared.1, ihRight hdeclared.2⟩

theorem ConfigureDelta.fixedQueriesOfColumns_registersQuery_of_mem
    {columns : List TableColumn} {column : TableColumn}
    (hcolumn : column ∈ columns) :
    (ConfigureDelta.fixedQueriesOfColumns (F := F) columns).RegistersQuery
      (.fixed column.inner 0) := by
  unfold ConfigureDelta.fixedQueriesOfColumns
  have aux (remaining : List TableColumn)
      (initial : ConfigureDelta F)
      (hcolumn : initial.RegistersQuery (.fixed column.inner 0) ∨
        column ∈ remaining) :
      (remaining.foldl
        (fun delta column =>
          delta.append { fixedQueries := [(column.inner, 0)] })
        initial).RegistersQuery (.fixed column.inner 0) := by
    induction remaining generalizing initial with
    | nil => simpa using hcolumn
    | cons head remaining ih =>
        rw [List.foldl_cons]
        apply ih
        rcases hcolumn with hregistered | hcolumn
        · exact Or.inl hregistered.append_left
        · rw [List.mem_cons] at hcolumn
          rcases hcolumn with rfl | hcolumn
          · exact Or.inl (by
              simp [ConfigureDelta.RegistersQuery,
                ConfigureDelta.append])
          · exact Or.inr hcolumn
  exact aux columns {} (Or.inr hcolumn)

/-- Instance-query requests among a gate or lookup's declared query atoms. -/
def ConfigureDelta.instanceQueriesOfCells
    (cells : List (Expression F Query)) :
    List (Column .instance × Rotation) :=
  cells.flatMap fun cell =>
    match cell with
    | .var (.instance column rotation) => [(column, rotation)]
    | _ => []

/-- Rust: `meta.advice_column()`. -/
def adviceColumn : Configure F (Column .advice) :=
  ⟨fun counts =>
    (⟨counts.numAdviceColumns⟩, {},
      { numAdviceColumns := 1 })⟩

/-- Rust: `meta.fixed_column()`. -/
def fixedColumn : Configure F (Column .fixed) :=
  ⟨fun counts =>
    (⟨counts.numFixedColumns⟩, {},
      { numFixedColumns := 1 })⟩

/-- Rust: `meta.instance_column()`. -/
def instanceColumn : Configure F (Column .instance) :=
  ⟨fun counts =>
    (⟨counts.numInstanceColumns⟩, {},
      { numInstanceColumns := 1 })⟩

@[simp] theorem Configure.delta_adviceColumn
    (counts : ConfigureCounts) :
    (adviceColumn : Configure F (Column .advice)).delta counts = {} :=
  rfl

@[simp] theorem Configure.delta_fixedColumn
    (counts : ConfigureCounts) :
    (fixedColumn : Configure F (Column .fixed)).delta counts = {} :=
  rfl

@[simp] theorem Configure.delta_instanceColumn
    (counts : ConfigureCounts) :
    (instanceColumn : Configure F (Column .instance)).delta counts = {} :=
  rfl

/-- Rust: `meta.selector()` (a simple selector). -/
def selector : Configure F Selector :=
  ⟨fun counts =>
    (⟨counts.numSelectors, true⟩, {},
      { numSelectors := 1 })⟩

/-- Rust: `meta.complex_selector()`. -/
def complexSelector : Configure F Selector :=
  ⟨fun counts =>
    (⟨counts.numSelectors, false⟩, {},
      { numSelectors := 1 })⟩

/-- Rust: `meta.enable_equality(column)`. Idempotent, exactly like Rust's
`permutation::Argument::add_column` (`permutation.rs:61-65`: `if !columns.contains`),
which matters for VK-faithful permutation-column order when a column is
equality-enabled twice (e.g. `mul_fixed`'s `window`: once by `mul_fixed::configure`,
once by `RunningSumConfig::configure`).

Also registers a cur-rotation query on the column *before* the permutation append
(`circuit.rs:1046-1050`) — unconditionally, not gated on the column being new to the
permutation (idempotence comes from the `query_*_index` dedup). -/
def enableEquality (c : AnyColumn) : Configure F Unit :=
  ⟨fun _ =>
    ((), (ConfigureDelta.queryAny c).append
      { permutationRequests := [c] }, {})⟩

@[simp]
theorem Configure.delta_enableEquality_gates
    (column : AnyColumn) (counts : ConfigureCounts) :
    ((enableEquality (F := F) column).delta counts).gates = [] := by
  rcases column with ⟨kind, index⟩
  cases kind <;> rfl

@[simp]
theorem Configure.delta_enableEquality_lookups
    (column : AnyColumn) (counts : ConfigureCounts) :
    ((enableEquality (F := F) column).delta counts).lookups = [] := by
  rcases column with ⟨kind, index⟩
  cases kind <;> rfl

theorem Configure.delta_enableEquality_permutationRequests
    (column : AnyColumn) (counts : ConfigureCounts) :
    ((enableEquality (F := F) column).delta counts).permutationRequests = [column] := by
  rcases column with ⟨kind, index⟩
  cases kind <;> rfl

theorem Configure.plan_enableEquality_permutationRequests
    (column : AnyColumn) (counts : ConfigureCounts) :
    ((enableEquality (F := F) column).plan counts).2.1.permutationRequests = [column] := by
  rcases column with ⟨kind, index⟩
  cases kind <;> rfl

/-- Rust: `meta.enable_constant(column)` (`circuit.rs:1038-1044`): registers the
constants column and enables equality on it (constants are enforced via copies into this
column) — including `enable_equality`'s cur fixed-query registration. -/
def enableConstant (col : Column .fixed) : Configure F Unit :=
  ⟨fun _ =>
    ((), {
      fixedQueries := [(col, 0)]
      constants := [col]
      permutationRequests := [col.toAny]
    }, {})⟩

/-- Rust: `meta.lookup_table_column()`. -/
def lookupTableColumn : Configure F TableColumn := do
  return { inner := ← fixedColumn }

/-- Rust: `meta.create_gate(name, |meta| Constraints::with_selector(guard, [...]))`.
Registers the gate's `queriedCells` in list order (the closure's queries all execute
before the gate is pushed, `circuit.rs:1195-1229`), then appends the gate. -/
def createGate (gate : Gate F) : Configure F Unit :=
  ⟨fun _ =>
    ((), (ConfigureDelta.queriedCells gate.name gate.queriedCells).append
      { gates := [gate] }, {})⟩

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
@[query_correct]
def LookupQueriesDeclared
    (queriedCells : List (Expression F Query))
    (tableMap : List (Expression F Query × TableColumn)) : Prop :=
  queriedCells.Forall Expression.QueryAtom ∧
    (tableMap.map Prod.fst).Forall fun expression =>
      expression.QueriesDeclared queriedCells

def lookup (queriedCells : List (Expression F Query))
    (tableMap : List (Expression F Query × TableColumn))
    (_hqueries : LookupQueriesDeclared queriedCells tableMap := by
      query_correct) : Configure F Unit :=
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
  ⟨fun _ =>
    let queryDelta := ConfigureDelta.queriedCells "lookup" queriedCells
    let tableDelta := ConfigureDelta.fixedQueriesOfColumns
      (tableMap.map Prod.snd)
    ((), queryDelta.append tableDelta |>.append
      { lookups := [{ inputs, tables, tablesFree, arity }] }, {})⟩

@[simp] theorem ConfigureDelta.gates_append
    (left right : ConfigureDelta F) :
    (left.append right).gates = left.gates ++ right.gates :=
  rfl

@[simp] theorem ConfigureDelta.lookups_append
    (left right : ConfigureDelta F) :
    (left.append right).lookups = left.lookups ++ right.lookups :=
  rfl

theorem ConfigureDelta.permutationRequests_append
    (left right : ConfigureDelta F) :
    (left.append right).permutationRequests =
      left.permutationRequests ++ right.permutationRequests :=
  rfl

/-! ## Selector allocation -/

/-- Every query emitted by a configure delta names an allocated column, every declared
query cell is valid, and every gate/lookup expression resolves against the emitted query
layout. -/
structure ConfigureDelta.QueriesLawful
    (delta : ConfigureDelta F) (counts : ConfigureCounts) : Prop where
  adviceQueries_fst_lt_numAdviceColumns :
    delta.adviceQueries.Forall fun query =>
      query.1.index < counts.numAdviceColumns
  fixedQueries_fst_lt_numFixedColumns :
    delta.fixedQueries.Forall fun query =>
      query.1.index < counts.numFixedColumns
  instanceQueries_fst_lt_numInstanceColumns :
    delta.instanceQueries.Forall fun query =>
      query.1.index < counts.numInstanceColumns
  invalidQueriedCells_eq_nil : delta.invalidQueriedCells = []
  gates_queriesRegistered :
    delta.gates.Forall (·.QueriesRegistered delta)
  gates_queriedCellsRegistered :
    delta.gates.Forall (·.QueriedCellsRegistered delta)
  lookups_queriesRegistered :
    delta.lookups.Forall (·.QueriesRegistered delta)
  permutationRequests_registered :
    delta.permutationRequests.Forall delta.RegistersPermutationColumn
  /-- `enableConstant` also enables equality on its constants column. -/
  constants_permutationRequests :
    delta.constants.Forall fun column =>
      column.toAny ∈ delta.permutationRequests

/-- Query allocation remains true when the available allocation counts grow. -/
theorem ConfigureDelta.QueriesLawful.mono
    {delta : ConfigureDelta F} {source target : ConfigureCounts}
    (hlawful : delta.QueriesLawful source)
    (hcounts : source.ComponentwiseLE target) :
    delta.QueriesLawful target where
  adviceQueries_fst_lt_numAdviceColumns :=
    hlawful.adviceQueries_fst_lt_numAdviceColumns.imp fun _ hquery =>
      hquery.trans_le hcounts.numAdviceColumns
  fixedQueries_fst_lt_numFixedColumns :=
    hlawful.fixedQueries_fst_lt_numFixedColumns.imp fun _ hquery =>
      hquery.trans_le hcounts.numFixedColumns
  instanceQueries_fst_lt_numInstanceColumns :=
    hlawful.instanceQueries_fst_lt_numInstanceColumns.imp fun _ hquery =>
      hquery.trans_le hcounts.numInstanceColumns
  invalidQueriedCells_eq_nil := hlawful.invalidQueriedCells_eq_nil
  gates_queriesRegistered := hlawful.gates_queriesRegistered
  gates_queriedCellsRegistered := hlawful.gates_queriedCellsRegistered
  lookups_queriesRegistered := hlawful.lookups_queriesRegistered
  permutationRequests_registered := hlawful.permutationRequests_registered
  constants_permutationRequests := hlawful.constants_permutationRequests

/-- A gate-local declaration can be consumed directly once the compiler has emitted
that gate into a lawful configure delta. -/
theorem ConfigureDelta.QueriesLawful.queriedCell_registered
    {delta : ConfigureDelta F} {counts : ConfigureCounts}
    (hlawful : delta.QueriesLawful counts) {gate : Gate F}
    (hgate : gate ∈ delta.gates) {cell : Expression F Query}
    (hcell : cell ∈ gate.queriedCells) :
    cell.QueriesRegistered delta := by
  exact List.forall_iff_forall_mem.mp
    (List.forall_iff_forall_mem.mp
      hlawful.gates_queriedCellsRegistered gate hgate)
    cell hcell

theorem ConfigureDelta.QueriesLawful.lookupInput_registered
    {delta : ConfigureDelta F} {counts : ConfigureCounts}
    (hlawful : delta.QueriesLawful counts) {argument : LookupArgument F}
    (hargument : argument ∈ delta.lookups) {input : Expression F Query}
    (hinput : input ∈ argument.inputs) :
    input.QueriesRegistered delta := by
  exact List.forall_iff_forall_mem.mp
    ((List.forall_iff_forall_mem.mp
      hlawful.lookups_queriesRegistered argument hargument).1)
    input hinput

theorem ConfigureDelta.QueriesLawful.lookupTable_registered
    {delta : ConfigureDelta F} {counts : ConfigureCounts}
    (hlawful : delta.QueriesLawful counts) {argument : LookupArgument F}
    (hargument : argument ∈ delta.lookups) {table : Expression F Query}
    (htable : table ∈ argument.tables) :
    table.QueriesRegistered delta := by
  exact List.forall_iff_forall_mem.mp
    ((List.forall_iff_forall_mem.mp
      hlawful.lookups_queriesRegistered argument hargument).2)
    table htable

/-- The empty configure contribution emits no queries. -/
theorem ConfigureDelta.QueriesLawful.empty (counts : ConfigureCounts) :
    ({} : ConfigureDelta F).QueriesLawful counts := by
  constructor <;> simp

/-- Query lawfulness composes across append-only configure deltas. -/
theorem ConfigureDelta.QueriesLawful.append
    {left right : ConfigureDelta F} {counts : ConfigureCounts}
    (hleft : left.QueriesLawful counts)
    (hright : right.QueriesLawful counts) :
    (left.append right).QueriesLawful counts := by
  constructor
  · simpa [ConfigureDelta.append] using
      And.intro hleft.adviceQueries_fst_lt_numAdviceColumns
        hright.adviceQueries_fst_lt_numAdviceColumns
  · simpa [ConfigureDelta.append] using
      And.intro hleft.fixedQueries_fst_lt_numFixedColumns
        hright.fixedQueries_fst_lt_numFixedColumns
  · simpa [ConfigureDelta.append] using
      And.intro hleft.instanceQueries_fst_lt_numInstanceColumns
        hright.instanceQueries_fst_lt_numInstanceColumns
  · simp [ConfigureDelta.append, hleft.invalidQueriedCells_eq_nil,
      hright.invalidQueriedCells_eq_nil]
  · rw [ConfigureDelta.gates_append, List.forall_append]
    exact ⟨hleft.gates_queriesRegistered.imp fun _ hgate => hgate.append_left,
      hright.gates_queriesRegistered.imp fun _ hgate => hgate.append_right⟩
  · rw [ConfigureDelta.gates_append, List.forall_append]
    exact ⟨hleft.gates_queriedCellsRegistered.imp fun _ hgate => hgate.append_left,
      hright.gates_queriedCellsRegistered.imp fun _ hgate => hgate.append_right⟩
  · rw [ConfigureDelta.lookups_append, List.forall_append]
    exact ⟨hleft.lookups_queriesRegistered.imp fun _ hlookup => hlookup.append_left,
      hright.lookups_queriesRegistered.imp fun _ hlookup => hlookup.append_right⟩
  · rw [ConfigureDelta.append, List.forall_append]
    exact
      ⟨hleft.permutationRequests_registered.imp fun _ hcolumn =>
          hcolumn.append_left,
        hright.permutationRequests_registered.imp fun _ hcolumn =>
          hcolumn.append_right⟩
  · rw [ConfigureDelta.append, List.forall_append]
    exact ⟨hleft.constants_permutationRequests.imp fun column hcolumn =>
      List.mem_append_left _ hcolumn,
      hright.constants_permutationRequests.imp fun column hcolumn =>
        List.mem_append_right _ hcolumn⟩

/-- Registering one valid query atom preserves query allocation. -/
theorem ConfigureDelta.queriedCell_queriesLawful
    (owner : String) (counts : ConfigureCounts)
    {cell : Expression F Query} (hcell : cell.QueryAllocated counts) :
    (ConfigureDelta.queriedCell owner cell).QueriesLawful counts := by
  cases cell with
  | var query =>
      cases query with
      | selector => simp_all [Expression.QueryAllocated]
      | fixed | advice | «instance» =>
          constructor <;>
            simp_all [Expression.QueryAllocated,
              ConfigureDelta.queriedCell]
  | const | add | mul =>
      simp_all [Expression.QueryAllocated]

/-- Registering a list of valid query atoms preserves query allocation. -/
theorem ConfigureDelta.queriedCells_queriesLawful
    (owner : String) (counts : ConfigureCounts)
    {cells : List (Expression F Query)}
    (hcells : cells.Forall (·.QueryAllocated counts)) :
    (ConfigureDelta.queriedCells owner cells).QueriesLawful counts := by
  unfold ConfigureDelta.queriedCells
  have aux (remaining : List (Expression F Query))
      (initial : ConfigureDelta F)
      (hremaining : remaining.Forall (·.QueryAllocated counts))
      (hinitial : initial.QueriesLawful counts) :
      (remaining.foldl
        (fun delta cell => delta.append (.queriedCell owner cell))
        initial).QueriesLawful counts := by
    induction remaining generalizing initial with
    | nil =>
        exact hinitial
    | cons cell remaining ih =>
        rw [List.foldl_cons]
        rw [List.forall_cons] at hremaining
        apply ih
        · exact hremaining.2
        · exact hinitial.append
            (ConfigureDelta.queriedCell_queriesLawful
              owner counts hremaining.1)
  exact aux cells {} hcells (ConfigureDelta.QueriesLawful.empty counts)

/-- Lookup table columns emit allocated rotation-zero fixed queries. -/
theorem ConfigureDelta.fixedQueriesOfColumns_queriesLawful
    (counts : ConfigureCounts) {columns : List TableColumn}
    (hcolumns : columns.Forall fun column =>
      column.inner.index < counts.numFixedColumns) :
    (ConfigureDelta.fixedQueriesOfColumns (F := F) columns).QueriesLawful counts := by
  unfold ConfigureDelta.fixedQueriesOfColumns
  have aux (remaining : List TableColumn)
      (initial : ConfigureDelta F)
      (hremaining : remaining.Forall fun column =>
        column.inner.index < counts.numFixedColumns)
      (hinitial : initial.QueriesLawful counts) :
      (remaining.foldl
        (fun delta column =>
          delta.append { fixedQueries := [(column.inner, 0)] })
        initial).QueriesLawful counts := by
    induction remaining generalizing initial with
    | nil => exact hinitial
    | cons column remaining ih =>
        rw [List.foldl_cons, List.forall_cons] at *
        apply ih
        · exact hremaining.2
        · apply hinitial.append
          constructor <;> simp_all
  exact aux columns {} hcolumns (ConfigureDelta.QueriesLawful.empty counts)

/-- Equality registration emits an allocated query when its input column exists. -/
theorem ConfigureDelta.queryAny_queriesLawful
    (counts : ConfigureCounts) {column : AnyColumn}
    (hcolumn : column.Allocated counts) :
    (ConfigureDelta.queryAny (F := F) column).QueriesLawful counts := by
  rcases column with ⟨kind, index⟩
  cases kind <;>
    constructor <;>
      simp_all [AnyColumn.Allocated, ConfigureDelta.queryAny]

/-- One past the largest selector index occurring in an expression. -/
def Expression.selectorBound : Expression F Query → ℕ
  | .var (.selector selector) => selector.index + 1
  | .var _ => 0
  | .const _ => 0
  | .add left right
  | .mul left right => max left.selectorBound right.selectorBound

@[simp] theorem Expression.selectorBound_querySelector (selector : Selector) :
    (querySelector (F := F) selector).selectorBound = selector.index + 1 :=
  rfl

@[simp] theorem Expression.selectorBound_queryAdvice
    (column : Column .advice) (rotation : Rotation) :
    (queryAdvice (F := F) column rotation).selectorBound = 0 :=
  rfl

@[simp] theorem Expression.selectorBound_queryFixed
    (column : Column .fixed) :
    (queryFixed (F := F) column).selectorBound = 0 :=
  rfl

@[simp] theorem Expression.selectorBound_queryInstance
    (column : Column .instance) (rotation : Rotation) :
    (queryInstance (F := F) column rotation).selectorBound = 0 :=
  rfl

/-- One past every selector index occurring in a lookup's input tuple. -/
def LookupArgument.inputSelectorBound (argument : LookupArgument F) : ℕ :=
  (argument.inputs.map Expression.selectorBound).foldr max 0

/-- One past every input-selector index occurring in a lookup list. -/
def lookupInputSelectorBound (arguments : List (LookupArgument F)) : ℕ :=
  (arguments.map LookupArgument.inputSelectorBound).foldr max 0

private theorem foldr_max_append (left right : List ℕ) :
    (left ++ right).foldr max 0 =
      max (left.foldr max 0) (right.foldr max 0) := by
  induction left with
  | nil =>
      simp
  | cons value left ih =>
      simp only [List.cons_append, List.foldr_cons, ih]
      exact (max_assoc value (left.foldr max 0)
        (right.foldr max 0)).symm

@[simp] theorem lookupInputSelectorBound_append
    (left right : List (LookupArgument F)) :
    lookupInputSelectorBound (left ++ right) =
      max (lookupInputSelectorBound left)
        (lookupInputSelectorBound right) := by
  simp only [lookupInputSelectorBound, List.map_append,
    foldr_max_append]

/-- A selected lookup input expression lies below the whole lookup-list bound. -/
theorem Expression.selectorBound_le_lookupInputSelectorBound
    {arguments : List (LookupArgument F)} {argument : LookupArgument F}
    (hargument : argument ∈ arguments)
    {expression : Expression F Query} (hexpression : expression ∈ argument.inputs) :
    expression.selectorBound ≤ lookupInputSelectorBound arguments := by
  apply List.le_max_of_le' 0
    (List.mem_map.mpr ⟨argument, hargument, rfl⟩)
  apply List.le_max_of_le' 0
    (List.mem_map.mpr ⟨expression, hexpression, rfl⟩)
  exact le_rfl

/--
Every gate selector and lookup-input selector emitted by a configure delta lies below
the final allocated selector count. Gate well-formedness then gives the same bound for
every selector atom in each gate constraint.
-/
structure ConfigureDelta.SelectorsAllocated
    (delta : ConfigureDelta F) (numSelectors : ℕ) : Prop where
  gates :
    delta.gates.Forall fun gate => gate.selector.index < numSelectors
  lookups :
    lookupInputSelectorBound delta.lookups ≤ numSelectors

/-- Selector allocation remains true when the available count grows. -/
theorem ConfigureDelta.SelectorsAllocated.mono
    {delta : ConfigureDelta F} {source target : ℕ}
    (hallocated : delta.SelectorsAllocated source)
    (hcount : source ≤ target) :
    delta.SelectorsAllocated target where
  gates := hallocated.gates.imp fun _ hgate => hgate.trans_le hcount
  lookups := hallocated.lookups.trans hcount

/-- The empty configure contribution allocates no selectors. -/
theorem ConfigureDelta.SelectorsAllocated.empty (numSelectors : ℕ) :
    ({} : ConfigureDelta F).SelectorsAllocated numSelectors := by
  constructor
  · simp
  · simp [lookupInputSelectorBound]

/-- Allocation laws compose across append-only configure deltas. -/
theorem ConfigureDelta.SelectorsAllocated.append
    {left right : ConfigureDelta F} {numSelectors : ℕ}
    (hleft : left.SelectorsAllocated numSelectors)
    (hright : right.SelectorsAllocated numSelectors) :
    (left.append right).SelectorsAllocated numSelectors where
  gates := by
    simpa only [ConfigureDelta.gates_append, List.forall_append] using
      And.intro hleft.gates hright.gates
  lookups := by
    simp only [ConfigureDelta.lookups_append,
      lookupInputSelectorBound_append]
    exact max_le hleft.lookups hright.lookups

@[simp] theorem ConfigureDelta.gates_queriedCells
    (owner : String) (cells : List (Expression F Query)) :
    (ConfigureDelta.queriedCells owner cells).gates = [] := by
  unfold ConfigureDelta.queriedCells
  have aux :
      ∀ (remaining : List (Expression F Query)) (delta : ConfigureDelta F),
        (remaining.foldl
          (fun current cell =>
            current.append (ConfigureDelta.queriedCell owner cell))
          delta).gates = delta.gates := by
    intro remaining
    induction remaining with
    | nil =>
        intro delta
        rfl
    | cons cell remaining ih =>
        intro delta
        rw [List.foldl_cons, ih]
        cases cell with
        | var query =>
            cases query <;>
              simp [ConfigureDelta.append, ConfigureDelta.queriedCell]
        | const
        | add
        | mul =>
            simp [ConfigureDelta.append, ConfigureDelta.queriedCell]
  exact aux cells {}

@[simp] theorem ConfigureDelta.lookups_queriedCells
    (owner : String) (cells : List (Expression F Query)) :
    (ConfigureDelta.queriedCells owner cells).lookups = [] := by
  unfold ConfigureDelta.queriedCells
  have aux :
      ∀ (remaining : List (Expression F Query)) (delta : ConfigureDelta F),
        (remaining.foldl
          (fun current cell =>
            current.append (ConfigureDelta.queriedCell owner cell))
          delta).lookups = delta.lookups := by
    intro remaining
    induction remaining with
    | nil =>
        intro delta
        rfl
    | cons cell remaining ih =>
        intro delta
        rw [List.foldl_cons, ih]
        cases cell with
        | var query =>
            cases query <;>
              simp [ConfigureDelta.append, ConfigureDelta.queriedCell]
        | const
        | add
        | mul =>
            simp [ConfigureDelta.append, ConfigureDelta.queriedCell]
  exact aux cells {}

theorem ConfigureDelta.permutationRequests_queriedCells
    (owner : String) (cells : List (Expression F Query)) :
    (ConfigureDelta.queriedCells owner cells).permutationRequests = [] := by
  unfold ConfigureDelta.queriedCells
  have aux :
      ∀ (remaining : List (Expression F Query)) (delta : ConfigureDelta F),
        (remaining.foldl
          (fun current cell =>
            current.append (ConfigureDelta.queriedCell owner cell))
          delta).permutationRequests = delta.permutationRequests := by
    intro remaining
    induction remaining with
    | nil =>
        intro delta
        rfl
    | cons cell remaining ih =>
        intro delta
        rw [List.foldl_cons, ih]
        cases cell with
        | var query =>
            cases query <;>
              simp [ConfigureDelta.append, ConfigureDelta.queriedCell]
        | const
        | add
        | mul =>
            simp [ConfigureDelta.append, ConfigureDelta.queriedCell]
  exact aux cells {}

private theorem foldlTableDelta_gates
    (tables : List TableColumn) (delta : ConfigureDelta F) :
    (tables.foldl
      (fun current table =>
        current.append { fixedQueries := [(table.inner, 0)] })
      delta).gates = delta.gates := by
  induction tables generalizing delta with
  | nil => rfl
  | cons table tables ih =>
      rw [List.foldl_cons, ih]
      simp [ConfigureDelta.append]

private theorem foldlTableDelta_lookups
    (tables : List TableColumn) (delta : ConfigureDelta F) :
    (tables.foldl
      (fun current table =>
        current.append { fixedQueries := [(table.inner, 0)] })
      delta).lookups = delta.lookups := by
  induction tables generalizing delta with
  | nil => rfl
  | cons table tables ih =>
      rw [List.foldl_cons, ih]
      simp [ConfigureDelta.append]

@[simp] theorem Configure.delta_lookup_gates
    (queriedCells : List (Expression F Query))
    (tableMap : List (Expression F Query × TableColumn))
    (hqueries : LookupQueriesDeclared queriedCells tableMap)
    (counts : ConfigureCounts) :
    ((lookup queriedCells tableMap hqueries).delta counts).gates = [] := by
  unfold Configure.delta lookup
  simp [ConfigureDelta.fixedQueriesOfColumns, foldlTableDelta_gates]

@[simp] theorem Configure.lookupInputSelectorBound_delta_lookup
    (queriedCells : List (Expression F Query))
    (tableMap : List (Expression F Query × TableColumn))
    (hqueries : LookupQueriesDeclared queriedCells tableMap)
    (counts : ConfigureCounts) :
    lookupInputSelectorBound
        ((lookup queriedCells tableMap hqueries).delta counts).lookups =
      ((tableMap.map Prod.fst).map Expression.selectorBound).foldr max 0 := by
  unfold Configure.delta lookup lookupInputSelectorBound
    LookupArgument.inputSelectorBound
  simp [ConfigureDelta.fixedQueriesOfColumns, foldlTableDelta_lookups]

namespace Configure

variable {α β : Type}

@[simp] theorem delta_pure (value : α) (counts : ConfigureCounts) :
    delta (pure value : Configure F α) counts = {} :=
  rfl

@[simp] theorem countDelta_pure
    (value : α) (counts : ConfigureCounts) :
    countDelta (pure value : Configure F α) counts = {} :=
  rfl

@[simp] theorem output_pure (value : α) (counts : ConfigureCounts) :
    output (pure value : Configure F α) counts = value :=
  rfl

@[simp] theorem finalCounts_pure (value : α) (counts : ConfigureCounts) :
    finalCounts (pure value : Configure F α) counts = counts :=
  rfl

@[simp] theorem delta_selector (counts : ConfigureCounts) :
    delta (selector : Configure F Selector) counts = {} :=
  rfl

@[simp] theorem delta_complexSelector (counts : ConfigureCounts) :
    delta (complexSelector : Configure F Selector) counts = {} :=
  rfl

@[simp] theorem delta_createGate
    (gate : Gate F) (counts : ConfigureCounts) :
    delta (createGate gate) counts =
      (ConfigureDelta.queriedCells gate.name gate.queriedCells).append
        { gates := [gate] } :=
  rfl

@[simp] theorem delta_bind
    (program : Configure F α) (next : α → Configure F β)
    (counts : ConfigureCounts) :
    delta (program >>= next) counts =
      (program.delta counts).append
        ((next (program.output counts)).delta
          (program.finalCounts counts)) :=
  rfl

@[simp] theorem countDelta_bind
    (program : Configure F α) (next : α → Configure F β)
    (counts : ConfigureCounts) :
    countDelta (program >>= next) counts =
      (program.countDelta counts).append
        ((next (program.output counts)).countDelta
          (program.finalCounts counts)) :=
  rfl

@[simp] theorem output_bind
    (program : Configure F α) (next : α → Configure F β)
    (counts : ConfigureCounts) :
    output (program >>= next) counts =
      (next (program.output counts)).output
        (program.finalCounts counts) :=
  rfl

@[simp] theorem finalCounts_bind
    (program : Configure F α) (next : α → Configure F β)
    (counts : ConfigureCounts) :
    finalCounts (program >>= next) counts =
      (next (program.output counts)).finalCounts
        (program.finalCounts counts) :=
  by simp [finalCounts]

@[simp] theorem output_adviceColumn (counts : ConfigureCounts) :
    output (adviceColumn : Configure F (Column .advice)) counts =
      ⟨counts.numAdviceColumns⟩ :=
  rfl

@[simp] theorem finalCounts_adviceColumn (counts : ConfigureCounts) :
    finalCounts (adviceColumn : Configure F (Column .advice)) counts =
      { counts with numAdviceColumns := counts.numAdviceColumns + 1 } :=
  rfl

@[simp] theorem output_fixedColumn (counts : ConfigureCounts) :
    output (fixedColumn : Configure F (Column .fixed)) counts =
      ⟨counts.numFixedColumns⟩ :=
  rfl

@[simp] theorem finalCounts_fixedColumn (counts : ConfigureCounts) :
    finalCounts (fixedColumn : Configure F (Column .fixed)) counts =
      { counts with numFixedColumns := counts.numFixedColumns + 1 } :=
  rfl

@[simp] theorem output_instanceColumn (counts : ConfigureCounts) :
    output (instanceColumn : Configure F (Column .instance)) counts =
      ⟨counts.numInstanceColumns⟩ :=
  rfl

@[simp] theorem finalCounts_instanceColumn (counts : ConfigureCounts) :
    finalCounts (instanceColumn : Configure F (Column .instance)) counts =
      { counts with numInstanceColumns := counts.numInstanceColumns + 1 } :=
  rfl

@[simp] theorem output_selector (counts : ConfigureCounts) :
    output (selector : Configure F Selector) counts =
      ⟨counts.numSelectors, true⟩ :=
  rfl

@[simp] theorem finalCounts_selector (counts : ConfigureCounts) :
    finalCounts (selector : Configure F Selector) counts =
      { counts with numSelectors := counts.numSelectors + 1 } :=
  rfl

@[simp] theorem output_complexSelector (counts : ConfigureCounts) :
    output (complexSelector : Configure F Selector) counts =
      ⟨counts.numSelectors, false⟩ :=
  rfl

@[simp] theorem finalCounts_complexSelector (counts : ConfigureCounts) :
    finalCounts (complexSelector : Configure F Selector) counts =
      { counts with numSelectors := counts.numSelectors + 1 } :=
  rfl

@[simp] theorem output_enableEquality
    (column : AnyColumn) (counts : ConfigureCounts) :
    output (enableEquality (F := F) column) counts = () :=
  rfl

@[simp] theorem finalCounts_enableEquality
    (column : AnyColumn) (counts : ConfigureCounts) :
    finalCounts (enableEquality (F := F) column) counts = counts :=
  rfl

@[simp] theorem output_enableConstant
    (column : Column .fixed) (counts : ConfigureCounts) :
    output (enableConstant (F := F) column) counts = () :=
  rfl

@[simp] theorem finalCounts_enableConstant
    (column : Column .fixed) (counts : ConfigureCounts) :
    finalCounts (enableConstant (F := F) column) counts = counts :=
  rfl

@[simp] theorem output_createGate
    (gate : Gate F) (counts : ConfigureCounts) :
    output (createGate gate) counts = () :=
  rfl

@[simp] theorem finalCounts_createGate
    (gate : Gate F) (counts : ConfigureCounts) :
    finalCounts (createGate gate) counts = counts :=
  rfl

@[simp] theorem output_lookup
    (queriedCells : List (Expression F Query))
    (tableMap : List (Expression F Query × TableColumn))
    (hqueries : LookupQueriesDeclared queriedCells tableMap)
    (counts : ConfigureCounts) :
    output (lookup queriedCells tableMap hqueries) counts = () :=
  rfl

@[simp] theorem finalCounts_lookup
    (queriedCells : List (Expression F Query))
    (tableMap : List (Expression F Query × TableColumn))
    (hqueries : LookupQueriesDeclared queriedCells tableMap)
    (counts : ConfigureCounts) :
    finalCounts (lookup queriedCells tableMap hqueries) counts = counts :=
  rfl

end Configure

@[simp] theorem ConfigureDelta.instanceQueries_append
    (left right : ConfigureDelta F) :
    (left.append right).instanceQueries =
      left.instanceQueries ++ right.instanceQueries :=
  rfl

@[simp] theorem ConfigureDelta.adviceQueries_append
    (left right : ConfigureDelta F) :
    (left.append right).adviceQueries =
      left.adviceQueries ++ right.adviceQueries :=
  rfl

@[simp] theorem ConfigureDelta.fixedQueries_append
    (left right : ConfigureDelta F) :
    (left.append right).fixedQueries =
      left.fixedQueries ++ right.fixedQueries :=
  rfl

@[simp] theorem ConfigureDelta.invalidQueriedCells_append
    (left right : ConfigureDelta F) :
    (left.append right).invalidQueriedCells =
      left.invalidQueriedCells ++ right.invalidQueriedCells :=
  rfl

@[simp] theorem ConfigureDelta.queryAny_instanceQueries
    (column : AnyColumn) :
    (ConfigureDelta.queryAny (F := F) column).instanceQueries =
      match column with
      | ⟨.instance, index⟩ => [(⟨index⟩, 0)]
      | _ => [] := by
  cases column with
  | mk kind index =>
      cases kind <;> rfl

@[simp] theorem ConfigureDelta.queriedCell_instanceQueries
    (owner : String) (cell : Expression F Query) :
    (ConfigureDelta.queriedCell owner cell).instanceQueries =
      match cell with
      | .var (.instance column rotation) => [(column, rotation)]
      | _ => [] := by
  cases cell with
  | var query =>
      cases query <;> rfl
  | const value =>
      rfl
  | add left right =>
      rfl
  | mul left right =>
      rfl

private theorem ConfigureDelta.queriedCells_instanceQueries_aux
    (owner : String) (cells : List (Expression F Query))
    (initial : ConfigureDelta F) :
    (cells.foldl
      (fun delta cell => delta.append (.queriedCell owner cell))
      initial).instanceQueries =
        initial.instanceQueries ++
          cells.flatMap fun cell =>
            match cell with
            | .var (.instance column rotation) => [(column, rotation)]
            | _ => [] := by
  induction cells generalizing initial with
  | nil =>
      simp
  | cons cell cells ih =>
      rw [List.foldl_cons, ih]
      simp only [ConfigureDelta.instanceQueries_append,
        ConfigureDelta.queriedCell_instanceQueries, List.flatMap_cons,
        List.append_assoc]

@[simp] theorem ConfigureDelta.queriedCells_instanceQueries
    (owner : String) (cells : List (Expression F Query)) :
    (ConfigureDelta.queriedCells owner cells).instanceQueries =
      ConfigureDelta.instanceQueriesOfCells cells := by
  rw [ConfigureDelta.queriedCells]
  simpa [ConfigureDelta.instanceQueriesOfCells] using
    ConfigureDelta.queriedCells_instanceQueries_aux
      (F := F) owner cells {}

@[simp] theorem Configure.delta_adviceColumn_instanceQueries
    (counts : ConfigureCounts) :
    (Configure.delta (adviceColumn : Configure F (Column .advice))
      counts).instanceQueries = [] :=
  rfl

@[simp] theorem Configure.delta_fixedColumn_instanceQueries
    (counts : ConfigureCounts) :
    (Configure.delta (fixedColumn : Configure F (Column .fixed))
      counts).instanceQueries = [] :=
  rfl

@[simp] theorem Configure.delta_instanceColumn_instanceQueries
    (counts : ConfigureCounts) :
    (Configure.delta (instanceColumn : Configure F (Column .instance))
      counts).instanceQueries = [] :=
  rfl

@[simp] theorem Configure.delta_selector_instanceQueries
    (counts : ConfigureCounts) :
    (Configure.delta (selector : Configure F Selector)
      counts).instanceQueries = [] :=
  rfl

@[simp] theorem Configure.delta_complexSelector_instanceQueries
    (counts : ConfigureCounts) :
    (Configure.delta (complexSelector : Configure F Selector)
      counts).instanceQueries = [] :=
  rfl

theorem Configure.delta_enableEquality_instanceQueries
    (column : AnyColumn) (counts : ConfigureCounts) :
    (Configure.delta (enableEquality (F := F) column)
      counts).instanceQueries =
        match column with
        | ⟨.instance, index⟩ => [(⟨index⟩, 0)]
        | _ => [] := by
  simp only [Configure.delta, enableEquality,
    ConfigureDelta.instanceQueries_append,
    ConfigureDelta.queryAny_instanceQueries]
  cases column with
  | mk kind index =>
      cases kind <;> rfl

@[simp] theorem Configure.delta_enableEquality_advice_instanceQueries
    (column : Column .advice) (counts : ConfigureCounts) :
    (Configure.delta (enableEquality (F := F) column.toAny)
      counts).instanceQueries = [] :=
  rfl

@[simp] theorem Configure.delta_enableEquality_fixed_instanceQueries
    (column : Column .fixed) (counts : ConfigureCounts) :
    (Configure.delta (enableEquality (F := F) column.toAny)
      counts).instanceQueries = [] :=
  rfl

@[simp] theorem Configure.delta_enableEquality_instance_instanceQueries
    (column : Column .instance) (counts : ConfigureCounts) :
    (Configure.delta (enableEquality (F := F) column.toAny)
      counts).instanceQueries = [(column, 0)] :=
  rfl

@[simp] theorem Configure.delta_enableConstant_instanceQueries
    (column : Column .fixed) (counts : ConfigureCounts) :
    (Configure.delta (enableConstant (F := F) column)
      counts).instanceQueries = [] :=
  rfl

@[simp] theorem Configure.delta_createGate_instanceQueries
    (gate : Gate F) (counts : ConfigureCounts) :
    (Configure.delta (createGate gate) counts).instanceQueries =
      ConfigureDelta.instanceQueriesOfCells gate.queriedCells := by
  simp only [Configure.delta, createGate,
    ConfigureDelta.instanceQueries_append,
    ConfigureDelta.queriedCells_instanceQueries, List.append_nil]

@[simp] theorem Configure.delta_lookup_instanceQueries
    (queriedCells : List (Expression F Query))
    (tableMap : List (Expression F Query × TableColumn))
    (hqueries : LookupQueriesDeclared queriedCells tableMap)
    (counts : ConfigureCounts) :
    (Configure.delta (lookup queriedCells tableMap hqueries) counts).instanceQueries =
      ConfigureDelta.instanceQueriesOfCells queriedCells := by
  simp only [Configure.delta, lookup,
    ConfigureDelta.instanceQueries_append,
    ConfigureDelta.queriedCells_instanceQueries]
  have htables
      (tables : List TableColumn) (initial : ConfigureDelta F) :
      (tables.foldl
        (fun delta table =>
          delta.append { fixedQueries := [(table.inner, 0)] })
        initial).instanceQueries = initial.instanceQueries := by
    induction tables generalizing initial with
    | nil =>
        rfl
    | cons table tables ih =>
        rw [List.foldl_cons, ih]
        simp only [ConfigureDelta.instanceQueries_append,
          List.append_nil]
  unfold ConfigureDelta.fixedQueriesOfColumns
  rw [htables]
  simp

/-- Fixed-query requests among a gate or lookup's declared query atoms. -/
def ConfigureDelta.fixedQueriesOfCells
    (cells : List (Expression F Query)) :
    List (Column .fixed × Rotation) :=
  cells.flatMap fun cell =>
    match cell with
    | .var (.fixed column _) => [(column, 0)]
    | _ => []

@[simp] theorem ConfigureDelta.queriedCell_fixedQueries
    (owner : String) (cell : Expression F Query) :
    (ConfigureDelta.queriedCell owner cell).fixedQueries =
      match cell with
      | .var (.fixed column _) => [(column, 0)]
      | _ => [] := by
  cases cell with
  | var query =>
      cases query <;> rfl
  | const | add | mul => rfl

private theorem ConfigureDelta.queriedCells_fixedQueries_aux
    (owner : String) (cells : List (Expression F Query))
    (initial : ConfigureDelta F) :
    (cells.foldl
      (fun delta cell => delta.append (.queriedCell owner cell))
      initial).fixedQueries =
        initial.fixedQueries ++ ConfigureDelta.fixedQueriesOfCells cells := by
  induction cells generalizing initial with
  | nil => simp [ConfigureDelta.fixedQueriesOfCells]
  | cons cell cells ih =>
      rw [List.foldl_cons, ih]
      simp only [ConfigureDelta.fixedQueries_append,
        ConfigureDelta.queriedCell_fixedQueries, List.flatMap_cons,
        List.append_assoc, ConfigureDelta.fixedQueriesOfCells]

@[simp] theorem ConfigureDelta.queriedCells_fixedQueries
    (owner : String) (cells : List (Expression F Query)) :
    (ConfigureDelta.queriedCells owner cells).fixedQueries =
      ConfigureDelta.fixedQueriesOfCells cells := by
  rw [ConfigureDelta.queriedCells]
  simpa using ConfigureDelta.queriedCells_fixedQueries_aux
    (F := F) owner cells {}

@[simp] theorem ConfigureDelta.fixedQueriesOfColumns_fixedQueries
    (columns : List TableColumn) :
    (ConfigureDelta.fixedQueriesOfColumns (F := F) columns).fixedQueries =
      columns.map fun column => (column.inner, 0) := by
  unfold ConfigureDelta.fixedQueriesOfColumns
  have aux (remaining : List TableColumn) (initial : ConfigureDelta F) :
      (remaining.foldl
        (fun delta column =>
          delta.append { fixedQueries := [(column.inner, 0)] })
        initial).fixedQueries =
          initial.fixedQueries ++
            remaining.map fun column => (column.inner, 0) := by
    induction remaining generalizing initial with
    | nil => simp
    | cons column remaining ih =>
        rw [List.foldl_cons, ih]
        simp [ConfigureDelta.fixedQueries_append, List.append_assoc]
  simpa using aux columns {}

@[simp] theorem Configure.delta_adviceColumn_fixedQueries
    (counts : ConfigureCounts) :
    ((adviceColumn : Configure F (Column .advice)).delta counts).fixedQueries = [] :=
  rfl

@[simp] theorem Configure.delta_fixedColumn_fixedQueries
    (counts : ConfigureCounts) :
    ((fixedColumn : Configure F (Column .fixed)).delta counts).fixedQueries = [] :=
  rfl

@[simp] theorem Configure.delta_instanceColumn_fixedQueries
    (counts : ConfigureCounts) :
    ((instanceColumn : Configure F (Column .instance)).delta counts).fixedQueries = [] :=
  rfl

@[simp] theorem Configure.delta_selector_fixedQueries
    (counts : ConfigureCounts) :
    ((selector : Configure F Selector).delta counts).fixedQueries = [] :=
  rfl

@[simp] theorem Configure.delta_complexSelector_fixedQueries
    (counts : ConfigureCounts) :
    ((complexSelector : Configure F Selector).delta counts).fixedQueries = [] :=
  rfl

@[simp] theorem Configure.delta_enableEquality_advice_fixedQueries
    (column : Column .advice) (counts : ConfigureCounts) :
    ((enableEquality (F := F) column.toAny).delta counts).fixedQueries = [] :=
  rfl

@[simp] theorem Configure.delta_enableEquality_fixed_fixedQueries
    (column : Column .fixed) (counts : ConfigureCounts) :
    ((enableEquality (F := F) column.toAny).delta counts).fixedQueries =
      [(column, 0)] :=
  rfl

@[simp] theorem Configure.delta_enableEquality_instance_fixedQueries
    (column : Column .instance) (counts : ConfigureCounts) :
    ((enableEquality (F := F) column.toAny).delta counts).fixedQueries = [] :=
  rfl

@[simp] theorem Configure.delta_enableConstant_fixedQueries
    (column : Column .fixed) (counts : ConfigureCounts) :
    ((enableConstant (F := F) column).delta counts).fixedQueries =
      [(column, 0)] :=
  rfl

@[simp] theorem Configure.delta_createGate_fixedQueries
    (gate : Gate F) (counts : ConfigureCounts) :
    ((createGate gate).delta counts).fixedQueries =
      ConfigureDelta.fixedQueriesOfCells gate.queriedCells := by
  simp only [Configure.delta, createGate,
    ConfigureDelta.fixedQueries_append,
    ConfigureDelta.queriedCells_fixedQueries, List.append_nil]

@[simp] theorem Configure.delta_lookup_fixedQueries
    (queriedCells : List (Expression F Query))
    (tableMap : List (Expression F Query × TableColumn))
    (hqueries : LookupQueriesDeclared queriedCells tableMap)
    (counts : ConfigureCounts) :
    ((lookup queriedCells tableMap hqueries).delta counts).fixedQueries =
      ConfigureDelta.fixedQueriesOfCells queriedCells ++
        (tableMap.map Prod.snd).map fun column => (column.inner, 0) := by
  simp only [Configure.delta, lookup, ConfigureDelta.fixedQueries_append,
    ConfigureDelta.queriedCells_fixedQueries,
    ConfigureDelta.fixedQueriesOfColumns_fixedQueries,
    List.append_nil]

open Lean Meta Simp in
/-- Reduce only the fixed-query projection of a named gate or lookup. -/
def foldConfigureFixedQueriesProc : Simproc := fun expression => do
  unless expression.isAppOf ``ConfigureDelta.fixedQueriesOfCells do
    return .continue
  try
    let reduced ← withTransparency .default (whnf expression)
    if reduced == expression then
      return .continue
    let proof ← mkExpectedTypeHint
      (← mkEqRefl expression) (← mkEq expression reduced)
    return .visit { expr := reduced, proof? := some proof }
  catch _ =>
    return .continue

simproc foldConfigureFixedQueries
    (ConfigureDelta.fixedQueriesOfCells _) :=
  foldConfigureFixedQueriesProc
attribute [simp] foldConfigureFixedQueries

open Lean Meta Simp in
/-- Fold a named configure program only through its fixed-query projection. -/
def foldConfigureFixedQueryProjectionProc : Simproc := fun expression => do
  unless expression.getAppFn.isConstOf ``ConfigureDelta.fixedQueries do
    return .continue
  try
    let reduced ← withTransparency .default (whnf expression)
    if reduced == expression then
      return .continue
    let proof ← mkExpectedTypeHint
      (← mkEqRefl expression) (← mkEq expression reduced)
    return .visit { expr := reduced, proof? := some proof }
  catch _ =>
    return .continue

simproc foldConfigureFixedQueryProjection
    ((Configure.delta _ _).fixedQueries) :=
  foldConfigureFixedQueryProjectionProc
attribute [simp] foldConfigureFixedQueryProjection

open Lean Meta Simp in
/--
Reduce only the query-list projection of a named gate or lookup. This gives the
configure normalizer an opacity boundary: it can discover that a large named gate has
no instance queries without unfolding its constraints or any unrelated configure data.
-/
def foldConfigureInstanceQueriesProc : Simproc := fun expression => do
  unless expression.isAppOf ``ConfigureDelta.instanceQueriesOfCells do
    return .continue
  try
    let reduced ← withTransparency .default (whnf expression)
    if reduced == expression then
      return .continue
    let proof ← mkExpectedTypeHint
      (← mkEqRefl expression) (← mkEq expression reduced)
    return .visit { expr := reduced, proof? := some proof }
  catch _ =>
    return .continue

simproc foldConfigureInstanceQueries
    (ConfigureDelta.instanceQueriesOfCells _) :=
  foldConfigureInstanceQueriesProc
attribute [simp] foldConfigureInstanceQueries

open Lean Elab Tactic in
/--
Normalize the instance-query projection of a transparent configure program.

The tactic unfolds only the outer configure definition, then follows the append-only
writer through monadic composition. Unrelated gates, lookups, columns, and selector
state are discarded by projection rather than materialized as a full constraint system.
-/
elab "configure_norm" : tactic => withMainContext do
  try
    evalTactic (← `(tactic| rfl))
  catch _ =>
    pure ()
  if (← getGoals).isEmpty then
    return
  let initialTarget ← instantiateMVars (← getMainTarget)
  if initialTarget.isForall then
    evalTactic (← `(tactic| intro counts))
  let target ← instantiateMVars (← getMainTarget)
  let some deltaApp := target.find? fun expression =>
      expression.getAppFn.isConstOf ``Configure.delta
    | throwError "configure_norm: no Configure.delta projection in target"
  let arguments := deltaApp.getAppArgs
  if arguments.size < 2 then
    throwError "configure_norm: malformed Configure.delta application"
  let program := arguments[arguments.size - 2]!
  let some head := program.getAppFn.constName?
    | throwError "configure_norm: configure program has no unfoldable head"
  evalTactic (← `(tactic| unfold $(mkIdent head)))
  evalTactic (← `(tactic|
    simp only [
      Configure.output, Configure.finalCounts,
      Configure.delta_bind, Configure.delta_pure,
      Configure.output_bind, Configure.output_pure,
      Configure.finalCounts_bind, Configure.finalCounts_pure,
      ConfigureDelta.instanceQueries_append,
      Configure.delta_adviceColumn_instanceQueries,
      Configure.delta_fixedColumn_instanceQueries,
      Configure.delta_instanceColumn_instanceQueries,
      Configure.delta_selector_instanceQueries,
      Configure.delta_complexSelector_instanceQueries,
      Configure.delta_enableEquality_advice_instanceQueries,
      Configure.delta_enableEquality_fixed_instanceQueries,
      Configure.delta_enableEquality_instance_instanceQueries,
      Configure.delta_enableConstant_instanceQueries,
      Configure.delta_createGate_instanceQueries,
      Configure.delta_lookup_instanceQueries,
      ConfigureDelta.queriedCells_instanceQueries,
      ConfigureDelta.fixedQueries_append,
      Configure.delta_adviceColumn_fixedQueries,
      Configure.delta_fixedColumn_fixedQueries,
      Configure.delta_instanceColumn_fixedQueries,
      Configure.delta_selector_fixedQueries,
      Configure.delta_complexSelector_fixedQueries,
      Configure.delta_enableEquality_advice_fixedQueries,
      Configure.delta_enableEquality_fixed_fixedQueries,
      Configure.delta_enableEquality_instance_fixedQueries,
      Configure.delta_enableConstant_fixedQueries,
      Configure.delta_createGate_fixedQueries,
      Configure.delta_lookup_fixedQueries,
      ConfigureDelta.queriedCells_fixedQueries,
      ConfigureDelta.fixedQueriesOfColumns_fixedQueries,
      lookupTableColumn,
      List.foldl_nil, List.foldl_cons, List.map, List.append_nil,
      List.nil_append, List.append_assoc]))
  if !(← getGoals).isEmpty then
    try
      evalTactic (← `(tactic| simp))
    catch _ =>
      pure ()
  if !(← getGoals).isEmpty then
    evalTactic (← `(tactic| rfl))

variable {α : Type}

/--
Reduced configure metadata used by parent circuits.

`instanceQueries` is the ordered list of instance-query requests emitted by this
program, before the constraint system's first-encounter deduplication. It is a function
of the initial state because a program may allocate an instance column and then query
that freshly allocated column. Most reusable child configurations emit no instance
queries, so the metadata and its proof both default to the empty list.
-/
class ElaboratedConfigure (program : Configure F α) where
  instanceQueries :
    ConfigureCounts → List (Column .instance × Rotation) := fun _ => []
  instanceQueries_eq : ∀ counts,
    (program.delta counts).instanceQueries =
      instanceQueries counts := by
    configure_norm
  /--
  Selector allocation required from the incoming configure state. Primitive gate and
  lookup registration expose requirements; monadic bind composes them.
  -/
  selectorRequirements : ConfigureCounts → Prop := fun _ => True
  selectorsAllocated : ∀ counts, selectorRequirements counts →
    (program.delta counts).SelectorsAllocated
      (program.finalCounts counts).numSelectors
  /-- Query allocation required from the incoming configure state. Gate and lookup
  registration expose the columns they reference; monadic bind composes them. -/
  queryRequirements : ConfigureCounts → Prop := fun counts =>
    (program.delta counts).QueriesLawful (program.finalCounts counts)
  queriesLawful : ∀ counts, queryRequirements counts →
    (program.delta counts).QueriesLawful
      (program.finalCounts counts) := by
    intro _ hqueries
    exact hqueries

@[simp] theorem ElaboratedConfigure.delta_instanceQueries
    (program : Configure F α) [elaborated : ElaboratedConfigure program]
    (counts : ConfigureCounts) :
    (program.delta counts).instanceQueries =
      elaborated.instanceQueries counts :=
  elaborated.instanceQueries_eq counts

instance ElaboratedConfigure.pure (value : α) :
    ElaboratedConfigure (pure value : Configure F α) where
  instanceQueries_eq := by
    intro counts
    rfl
  selectorRequirements _ := True
  selectorsAllocated := by
    intro counts _
    exact ConfigureDelta.SelectorsAllocated.empty counts.numSelectors
  queryRequirements _ := True
  queriesLawful := by
    intro counts _
    exact ConfigureDelta.QueriesLawful.empty counts

instance ElaboratedConfigure.bind {β : Type}
    (program : Configure F α) [programElaborated : ElaboratedConfigure program]
    (next : α → Configure F β)
    [nextElaborated : ∀ value, ElaboratedConfigure (next value)] :
    ElaboratedConfigure (program >>= next) where
  instanceQueries counts :=
    programElaborated.instanceQueries counts ++
      (nextElaborated (program.output counts)).instanceQueries
        (program.finalCounts counts)
  instanceQueries_eq := by
    intro counts
    rw [Configure.delta_bind, ConfigureDelta.instanceQueries_append,
      programElaborated.instanceQueries_eq,
      (nextElaborated (program.output counts)).instanceQueries_eq]
  selectorRequirements counts :=
    programElaborated.selectorRequirements counts ∧
      (nextElaborated (program.output counts)).selectorRequirements
        (program.finalCounts counts)
  selectorsAllocated := by
    intro counts hrequirements
    rw [Configure.delta_bind, Configure.finalCounts_bind]
    apply ConfigureDelta.SelectorsAllocated.append
    · exact
        (programElaborated.selectorsAllocated counts hrequirements.1).mono
          ((next (program.output counts)).numSelectors_le_finalCounts
            (program.finalCounts counts))
    · exact
        (nextElaborated (program.output counts)).selectorsAllocated
          (program.finalCounts counts) hrequirements.2
  queryRequirements counts :=
    programElaborated.queryRequirements counts ∧
      (nextElaborated (program.output counts)).queryRequirements
        (program.finalCounts counts)
  queriesLawful := by
    intro counts hrequirements
    rw [Configure.delta_bind, Configure.finalCounts_bind]
    apply ConfigureDelta.QueriesLawful.append
    · exact
        (programElaborated.queriesLawful counts hrequirements.1).mono
          ((next (program.output counts)).counts_componentwiseLE_finalCounts
            (program.finalCounts counts))
    · exact
        (nextElaborated (program.output counts)).queriesLawful
          (program.finalCounts counts) hrequirements.2

instance ElaboratedConfigure.adviceColumn :
    ElaboratedConfigure (adviceColumn : Configure F (Column .advice)) where
  instanceQueries_eq := Configure.delta_adviceColumn_instanceQueries
  selectorRequirements _ := True
  selectorsAllocated := by
    intro counts _
    exact ConfigureDelta.SelectorsAllocated.empty counts.numSelectors
  queryRequirements _ := True
  queriesLawful := by
    intro counts _
    exact ConfigureDelta.QueriesLawful.empty _

instance ElaboratedConfigure.fixedColumn :
    ElaboratedConfigure (fixedColumn : Configure F (Column .fixed)) where
  instanceQueries_eq := Configure.delta_fixedColumn_instanceQueries
  selectorRequirements _ := True
  selectorsAllocated := by
    intro counts _
    exact ConfigureDelta.SelectorsAllocated.empty counts.numSelectors
  queryRequirements _ := True
  queriesLawful := by
    intro counts _
    exact ConfigureDelta.QueriesLawful.empty _

instance ElaboratedConfigure.instanceColumn :
    ElaboratedConfigure (instanceColumn : Configure F (Column .instance)) where
  instanceQueries_eq := Configure.delta_instanceColumn_instanceQueries
  selectorRequirements _ := True
  selectorsAllocated := by
    intro counts _
    exact ConfigureDelta.SelectorsAllocated.empty counts.numSelectors
  queryRequirements _ := True
  queriesLawful := by
    intro counts _
    exact ConfigureDelta.QueriesLawful.empty _

instance ElaboratedConfigure.selector :
    ElaboratedConfigure (selector : Configure F Selector) where
  instanceQueries_eq := Configure.delta_selector_instanceQueries
  selectorRequirements _ := True
  selectorsAllocated := by
    intro counts _
    exact ConfigureDelta.SelectorsAllocated.empty
      (counts.numSelectors + 1)
  queryRequirements _ := True
  queriesLawful := by
    intro counts _
    exact ConfigureDelta.QueriesLawful.empty _

instance ElaboratedConfigure.complexSelector :
    ElaboratedConfigure (complexSelector : Configure F Selector) where
  instanceQueries_eq := Configure.delta_complexSelector_instanceQueries
  selectorRequirements _ := True
  selectorsAllocated := by
    intro counts _
    exact ConfigureDelta.SelectorsAllocated.empty
      (counts.numSelectors + 1)
  queryRequirements _ := True
  queriesLawful := by
    intro counts _
    exact ConfigureDelta.QueriesLawful.empty _

instance ElaboratedConfigure.enableEquality (column : AnyColumn) :
    ElaboratedConfigure (enableEquality (F := F) column) where
  instanceQueries _ :=
    match column with
    | ⟨.instance, index⟩ => [(⟨index⟩, 0)]
    | _ => []
  instanceQueries_eq :=
    Configure.delta_enableEquality_instanceQueries column
  selectorRequirements _ := True
  selectorsAllocated := by
    intro counts _
    rcases column with ⟨kind, index⟩
    cases kind
    all_goals
      constructor
      · simp [Configure.delta, Configure.finalCounts,
          Configure.countDelta, ConfigureCountDelta.apply,
          Halo2.enableEquality, ConfigureDelta.queryAny]
      · simp [Configure.delta, Configure.finalCounts,
          Configure.countDelta, ConfigureCountDelta.apply,
          Halo2.enableEquality, ConfigureDelta.queryAny,
          lookupInputSelectorBound]
  queryRequirements counts := column.Allocated counts
  queriesLawful := by
    intro counts hcolumn
    rcases column with ⟨kind, index⟩
    cases kind <;>
      constructor <;>
        simp_all [AnyColumn.Allocated, Configure.delta,
          Configure.finalCounts, Configure.countDelta,
          ConfigureCountDelta.apply, Halo2.enableEquality,
          ConfigureDelta.queryAny,
          ConfigureDelta.RegistersPermutationColumn,
          ConfigureDelta.append]

instance ElaboratedConfigure.enableConstant (column : Column .fixed) :
    ElaboratedConfigure (enableConstant (F := F) column) where
  instanceQueries_eq :=
    Configure.delta_enableConstant_instanceQueries column
  selectorRequirements _ := True
  selectorsAllocated := by
    intro counts _
    constructor
    · simp [Configure.delta, Configure.finalCounts,
        Configure.countDelta, ConfigureCountDelta.apply,
        Halo2.enableConstant]
    · simp [Configure.delta, Configure.finalCounts,
        Configure.countDelta, ConfigureCountDelta.apply,
        Halo2.enableConstant, lookupInputSelectorBound]
  queryRequirements counts := column.index < counts.numFixedColumns
  queriesLawful := by
    intro counts hcolumn
    rcases column with ⟨index⟩
    constructor <;>
      simp_all [Configure.delta, Configure.finalCounts,
        Configure.countDelta, ConfigureCountDelta.apply,
        Halo2.enableConstant,
        Column.toAny,
        ConfigureDelta.RegistersPermutationColumn]

instance ElaboratedConfigure.createGate (gate : Gate F) :
    ElaboratedConfigure (createGate gate) where
  instanceQueries := fun _ =>
    ConfigureDelta.instanceQueriesOfCells gate.queriedCells
  instanceQueries_eq :=
    Configure.delta_createGate_instanceQueries gate
  selectorRequirements counts :=
    gate.selector.index < counts.numSelectors
  selectorsAllocated := by
    intro counts hselector
    constructor
    · simpa [Configure.delta_createGate] using hselector
    · simp [Configure.delta_createGate, lookupInputSelectorBound]
  queryRequirements counts :=
    gate.queriedCells.Forall (·.QueryAllocated counts)
  queriesLawful := by
    intro counts hqueries
    let queryDelta := ConfigureDelta.queriedCells
      (F := F) gate.name gate.queriedCells
    have hqueryDelta : queryDelta.QueriesLawful counts :=
      ConfigureDelta.queriedCells_queriesLawful
        gate.name counts hqueries
    have hgateQueries : gate.QueriesRegistered queryDelta :=
      gate.wellFormed.constraintQueriesDeclared.imp fun _ hconstraint =>
        hconstraint.queriesRegistered_queriedCells
          gate.name gate.wellFormed.queriedCellsValid
    have hcombined :
        (queryDelta.append { gates := [gate] }).QueriesLawful counts := by
      constructor
      · simpa [ConfigureDelta.append] using
          hqueryDelta.adviceQueries_fst_lt_numAdviceColumns
      · simpa [ConfigureDelta.append] using
          hqueryDelta.fixedQueries_fst_lt_numFixedColumns
      · simpa [ConfigureDelta.append] using
          hqueryDelta.instanceQueries_fst_lt_numInstanceColumns
      · simpa [ConfigureDelta.append] using
          hqueryDelta.invalidQueriedCells_eq_nil
      · simpa [queryDelta] using
          (Gate.QueriesRegistered.append_left
            (right := ({ gates := [gate] } : ConfigureDelta F)) hgateQueries)
      · simpa [queryDelta] using
          (Gate.QueriedCellsRegistered.append_left
            (right := ({ gates := [gate] } : ConfigureDelta F))
            (ConfigureDelta.queriedCells_queriesRegistered
              gate.name gate.wellFormed.queriedCellsValid))
      · simp [queryDelta, ConfigureDelta.append]
      · simpa [ConfigureDelta.append] using
          hqueryDelta.permutationRequests_registered.imp
            (fun _ hcolumn => hcolumn.append_left
              (right := ({ gates := [gate] } : ConfigureDelta F)))
      · simpa [ConfigureDelta.append] using
          hqueryDelta.constants_permutationRequests
    simpa [Configure.delta, Configure.finalCounts,
      Configure.countDelta, ConfigureCountDelta.apply,
      Halo2.createGate, queryDelta] using hcombined

instance ElaboratedConfigure.lookup
    (queriedCells : List (Expression F Query))
    (tableMap : List (Expression F Query × TableColumn))
    (hqueries : LookupQueriesDeclared queriedCells tableMap) :
    ElaboratedConfigure (lookup queriedCells tableMap hqueries) where
  instanceQueries := fun _ =>
    ConfigureDelta.instanceQueriesOfCells queriedCells
  instanceQueries_eq :=
    Configure.delta_lookup_instanceQueries queriedCells tableMap hqueries
  selectorRequirements counts :=
    (Configure.delta
        (Halo2.lookup queriedCells tableMap hqueries) counts).gates = [] ∧
      lookupInputSelectorBound
        ((Halo2.lookup queriedCells tableMap hqueries).delta counts).lookups ≤
          counts.numSelectors
  selectorsAllocated := by
    intro counts hselectors
    constructor
    · rw [hselectors.1]
      trivial
    · simpa using hselectors.2
  queryRequirements counts :=
    queriedCells.Forall (·.QueryAllocated counts) ∧
      (tableMap.map Prod.snd).Forall fun table =>
        table.inner.index < counts.numFixedColumns
  queriesLawful := by
    intro counts hrequirements
    let queryDelta := ConfigureDelta.queriedCells
      (F := F) "lookup" queriedCells
    let tableDelta := ConfigureDelta.fixedQueriesOfColumns
      (F := F) (tableMap.map Prod.snd)
    have hqueryDelta : queryDelta.QueriesLawful counts :=
      ConfigureDelta.queriedCells_queriesLawful
        "lookup" counts hrequirements.1
    have htableDelta : tableDelta.QueriesLawful counts :=
      ConfigureDelta.fixedQueriesOfColumns_queriesLawful
        counts hrequirements.2
    have hcombined := hqueryDelta.append htableDelta
    constructor
    · simpa [Configure.delta, Configure.finalCounts,
        Configure.countDelta, ConfigureCountDelta.apply,
        Halo2.lookup, queryDelta, tableDelta] using
        hcombined.adviceQueries_fst_lt_numAdviceColumns
    · simpa [Configure.delta, Configure.finalCounts,
        Configure.countDelta, ConfigureCountDelta.apply,
        Halo2.lookup, queryDelta, tableDelta] using
        hcombined.fixedQueries_fst_lt_numFixedColumns
    · simpa [Configure.delta, Configure.finalCounts,
        Configure.countDelta, ConfigureCountDelta.apply,
        Halo2.lookup, queryDelta, tableDelta] using
        hcombined.instanceQueries_fst_lt_numInstanceColumns
    · simpa [Configure.delta, Configure.finalCounts,
        Configure.countDelta, ConfigureCountDelta.apply,
        Halo2.lookup, queryDelta, tableDelta] using
        hcombined.invalidQueriedCells_eq_nil
    · rw [Configure.delta_lookup_gates]
      simp
    · rw [Configure.delta_lookup_gates]
      simp
    · unfold Configure.delta Halo2.lookup
      simp only [ConfigureDelta.lookups_append,
        ConfigureDelta.lookups_queriedCells, List.nil_append,
        ConfigureDelta.fixedQueriesOfColumns,
        foldlTableDelta_lookups, List.append_nil,
        List.forall_cons]
      simp only [LookupArgument.QueriesRegistered]
      constructor
      · constructor
        · rw [List.forall_iff_forall_mem]
          intro expression hexpression
          have hdeclared :=
            (List.forall_iff_forall_mem.mp hqueries.2)
              expression hexpression
          exact (hdeclared.queriesRegistered_queriedCells
            "lookup" hqueries.1).append_left.append_left
        · rw [List.forall_iff_forall_mem]
          intro expression hexpression
          obtain ⟨⟨input, table⟩, hentry, rfl⟩ := List.mem_map.mp hexpression
          exact (ConfigureDelta.fixedQueriesOfColumns_registersQuery_of_mem
            (F := F) (List.mem_map.mpr
              ⟨(input, table), hentry, rfl⟩)).append_right.append_left
      · simp
    · simpa [Configure.delta, Halo2.lookup, queryDelta, tableDelta,
        ConfigureDelta.RegistersPermutationColumn,
        ConfigureDelta.append] using
          hcombined.permutationRequests_registered
    · simpa [Configure.delta, Halo2.lookup, queryDelta, tableDelta,
        ConfigureDelta.append] using
          hcombined.constants_permutationRequests

instance ElaboratedConfigure.lookupTableColumn :
    ElaboratedConfigure (lookupTableColumn : Configure F TableColumn) := by
  unfold Halo2.lookupTableColumn
  infer_instance

attribute [configure_selector_norm] ElaboratedConfigure.pure ElaboratedConfigure.bind
attribute [configure_query_norm] ElaboratedConfigure.pure ElaboratedConfigure.bind

open Lean Meta Simp in
/-- Fold the selector requirements stored in an inferred configure elaboration. -/
def foldElaboratedConfigureSelectorRequirementsProc : Simproc := fun expression => do
  unless expression.getAppFn.isConstOf ``ElaboratedConfigure.selectorRequirements do
    return .continue
  try
    let reduced ← withTransparency .all (whnf expression)
    if reduced == expression then
      return .continue
    let proof ← mkExpectedTypeHint
      (← mkEqRefl expression) (← mkEq expression reduced)
    return .visit { expr := reduced, proof? := some proof }
  catch _ =>
    return .continue

simproc foldElaboratedConfigureSelectorRequirements
    (ElaboratedConfigure.selectorRequirements _ _) :=
  foldElaboratedConfigureSelectorRequirementsProc
attribute [configure_selector_norm] foldElaboratedConfigureSelectorRequirements

open Lean Meta Simp in
/-- Fold the query requirements stored in an inferred configure elaboration. -/
def foldElaboratedConfigureQueryRequirementsProc : Simproc := fun expression => do
  unless expression.getAppFn.isConstOf ``ElaboratedConfigure.queryRequirements do
    return .continue
  try
    let reduced ← withTransparency .all (whnf expression)
    if reduced == expression then
      return .continue
    let proof ← mkExpectedTypeHint
      (← mkEqRefl expression) (← mkEq expression reduced)
    return .visit { expr := reduced, proof? := some proof }
  catch _ =>
    return .continue

simproc foldElaboratedConfigureQueryRequirements
    (ElaboratedConfigure.queryRequirements _ _) :=
  foldElaboratedConfigureQueryRequirementsProc
attribute [configure_query_norm] foldElaboratedConfigureQueryRequirements

open Lean Meta Simp in
/--
Fold an elaborated configure program's declared instance-query summary.

This is the compositional opacity boundary used by `configure_norm`: a parent may use
the summary packaged by a child `FormalCircuit` without unfolding the child's configure
program. Reducing the class projection unfolds only the instance and the circuit
structure far enough to select `elaborated.configureInfo`; it does not inspect
synthesis or proof fields.
-/
def foldElaboratedConfigureInstanceQueriesProc : Simproc := fun expression => do
  unless expression.getAppFn.isConstOf ``ElaboratedConfigure.instanceQueries do
    return .continue
  try
    let reduced ← withTransparency .all (whnf expression)
    if reduced == expression then
      return .continue
    let proof ← mkExpectedTypeHint
      (← mkEqRefl expression) (← mkEq expression reduced)
    return .visit { expr := reduced, proof? := some proof }
  catch _ =>
    return .continue

simproc foldElaboratedConfigureInstanceQueries
    (ElaboratedConfigure.instanceQueries _ _) :=
  foldElaboratedConfigureInstanceQueriesProc
attribute [simp] foldElaboratedConfigureInstanceQueries

end Halo2
