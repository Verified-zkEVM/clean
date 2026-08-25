import Clean.Halo2.Expression
import Clean.Halo2.Tactics.SelectorFree
import Clean.Halo2.Tactics.QueryCorrect
import Clean.Halo2.ConfigureAttr
import Clean.Halo2.KeygenAttr
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

-- TODO HALO2 these should probably return `Query`, and there should be the necessary TC machinery
-- for just using `Query` as part of an Expression.

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

/-- Halo 2's expression degree: queries have degree one, constants degree zero,
sums take the maximum, and products add. -/
def Expression.degree {F L : Type} : Expression F L → ℕ
  | .var _ => 1
  | .const _ => 0
  | .add left right => max left.degree right.degree
  | .mul left right => left.degree + right.degree

@[circuit_norm, keygen_norm]
theorem Expression.noSimpleSelectors_queryComplexSelector
    (selector : ComplexSelector) :
  (querySelector (F := F) (selector : Selector)).NoSimpleSelectors := by
  simp [querySelector, Expression.NoSimpleSelectors,
    ComplexSelector.toSelector_simple]

@[circuit_norm, keygen_norm]
theorem Expression.noSimpleSelectors_queryAdvice
    (column : Column .advice) (rotation : Rotation) :
    (queryAdvice (F := F) column rotation).NoSimpleSelectors := by
  simp [queryAdvice, Expression.NoSimpleSelectors]

@[circuit_norm, keygen_norm]
theorem Expression.noSimpleSelectors_queryFixed
    (column : Column .fixed) :
    (queryFixed (F := F) column).NoSimpleSelectors := by
  simp [queryFixed, Expression.NoSimpleSelectors]

@[circuit_norm, keygen_norm]
theorem Expression.noSimpleSelectors_queryInstance
    (column : Column .instance) (rotation : Rotation) :
    (queryInstance (F := F) column rotation).NoSimpleSelectors := by
  simp [queryInstance, Expression.NoSimpleSelectors]

/-- Every selector atom is the gate's distinguished selector, including its simple
versus complex kind. -/
@[circuit_norm]
def Expression.SelectorsOwnedBy
    (owner : Selector) : Expression F Query → Prop
  | .var (.selector selector) => selector = owner
  | .var _ => True
  | .const _ => True
  | .add left right
  | .mul left right =>
      left.SelectorsOwnedBy owner ∧ right.SelectorsOwnedBy owner

theorem Expression.selectorsOwnedBy_of_selectorFree
    (owner : Selector) (expression : Expression F Query)
    (hfree : expression.SelectorFree) :
    expression.SelectorsOwnedBy owner := by
  induction expression with
  | var query =>
      cases query <;>
        simp_all [Expression.SelectorFree, Expression.SelectorsOwnedBy]
  | const value => trivial
  | add left right ihLeft ihRight =>
      exact ⟨ihLeft hfree.1, ihRight hfree.2⟩
  | mul left right ihLeft ihRight =>
      exact ⟨ihLeft hfree.1, ihRight hfree.2⟩

theorem Expression.selectorsCovered_of_selectorsOwnedBy
    (owner : Selector) (expression : Expression F Query)
    (howned : expression.SelectorsOwnedBy owner) :
    expression.selectorsCovered
      (fun selector => decide (selector = owner.index)) = true := by
  induction expression with
  | var query =>
      cases query <;>
        simp_all [Expression.SelectorsOwnedBy,
          Expression.selectorsCovered]
  | const value =>
      rfl
  | add left right ihLeft ihRight
  | mul left right ihLeft ihRight =>
      simp only [Expression.SelectorsOwnedBy,
        Expression.selectorsCovered, Bool.and_eq_true] at howned ⊢
      exact ⟨ihLeft howned.1, ihRight howned.2⟩

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
      constraint.poly.SelectorsOwnedBy selector
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
  -- TODO HALO2 why is this a list of `Expression F Query` and not just `Query`??
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
      simp only [querySelector, Expression.SelectorsOwnedBy, true_and]
      exact Expression.selectorsOwnedBy_of_selectorFree selector poly
        (hfree (constraintName, poly) hsource)
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
  /-- The complex selector whose activation marks a row as participating in this
  lookup. Auxiliary selectors may choose between input modes, but must be activated
  together with this selector; see `LookupSelectorsLawful`. -/
  masterSelector : ComplexSelector
  inputs : List (Expression F Query)
  tables : List (Expression F Query)
  /-- Halo 2 rejects simple selectors in lookup input expressions. -/
  inputsNoSimpleSelectors : inputs.Forall Expression.NoSimpleSelectors
  /-- Halo 2 constructs the table side solely from lookup-table columns. -/
  tablesFree : ∀ table ∈ tables, table.SelectorFree
  /-- `lookup` receives pairs and unzips them, so both tuple sides have equal arity. -/
  arity : inputs.length = tables.length

/-- Halo 2's lookup-argument degree: `max 4 (2 + input + table)`, where
`input` and `table` are the largest degrees on the respective tuple sides. -/
def LookupArgument.requiredDegree (argument : LookupArgument F) : ℕ :=
  let inputDegree :=
    argument.inputs.foldl (fun current expression =>
      max current expression.degree) 1
  let tableDegree :=
    argument.tables.foldl (fun current expression =>
      max current expression.degree) 1
  max 4 (2 + inputDegree + tableDegree)

private theorem foldl_max_eq_max_foldl_max_zero
    (values : List ℕ) (initial : ℕ) :
    values.foldl max initial = max initial (values.foldl max 0) := by
  induction values generalizing initial with
  | nil => simp
  | cons value rest inductionHypothesis =>
      rw [List.foldl_cons, inductionHypothesis (max initial value),
        List.foldl_cons]
      simp only [Nat.zero_max]
      rw [inductionHypothesis value]
      ac_rfl

private theorem foldl_max_append (left right : List ℕ) :
    (left ++ right).foldl max 0 =
      max (left.foldl max 0) (right.foldl max 0) := by
  rw [List.foldl_append, foldl_max_eq_max_foldl_max_zero]

/-- The degree contributed by configured gate and lookup arguments, including Halo 2's
permutation baseline of three. This small value composes by `max`. -/
def constraintDegree
    (gates : List (Gate F)) (lookups : List (LookupArgument F)) : ℕ :=
  let lookupDegree := (lookups.map LookupArgument.requiredDegree).foldl max 0
  let gateDegree := ((gates.flatMap fun gate =>
    gate.constraints.map (fun constraint => constraint.poly)).map
      Expression.degree).foldl max 0
  max 3 (max lookupDegree gateDegree)

theorem three_le_constraintDegree
    (gates : List (Gate F)) (lookups : List (LookupArgument F)) :
    3 ≤ constraintDegree gates lookups := by
  simp [constraintDegree]

theorem constraintDegree_append
    (leftGates rightGates : List (Gate F))
    (leftLookups rightLookups : List (LookupArgument F)) :
    constraintDegree (leftGates ++ rightGates) (leftLookups ++ rightLookups) =
      max (constraintDegree leftGates leftLookups)
        (constraintDegree rightGates rightLookups) := by
  simp only [constraintDegree, List.map_append, foldl_max_append,
    List.flatMap_append]
  omega

deriving instance DecidableEq for Constraint
deriving instance DecidableEq for Gate
deriving instance DecidableEq for LookupArgument

/-- Selector indices occurring in an expression, with syntax-order multiplicity. -/
@[circuit_norm]
def Expression.selectorIndices : Expression F Query → List ℕ
  | .var (.selector selector) => [selector.index]
  | .var _ => []
  | .const _ => []
  | .add left right =>
      left.selectorIndices ++ right.selectorIndices
  | .mul left right =>
      left.selectorIndices ++ right.selectorIndices

@[circuit_norm, keygen_norm]
theorem Expression.selectorIndices_querySelector (selector : Selector) :
    (querySelector selector : Expression F Query).selectorIndices = [selector.index] := rfl

@[circuit_norm, keygen_norm]
theorem Expression.selectorIndices_queryFixed (column : Column .fixed) :
    (queryFixed column : Expression F Query).selectorIndices = [] := rfl

@[circuit_norm, keygen_norm]
theorem Expression.selectorIndices_queryAdvice
    (column : Column .advice) (rotation : Rotation) :
    (queryAdvice column rotation : Expression F Query).selectorIndices = [] := rfl

@[circuit_norm, keygen_norm]
theorem Expression.selectorIndices_queryInstance
    (column : Column .instance) (rotation : Rotation) :
    (queryInstance column rotation : Expression F Query).selectorIndices = [] := rfl

@[keygen_norm]
theorem Expression.selectorIndices_const (value : F) :
    (Expression.const value : Expression F Query).selectorIndices = [] := rfl

@[keygen_norm]
theorem Expression.selectorIndices_zero [Field F] :
    (0 : Expression F Query).selectorIndices = [] := rfl

@[keygen_norm]
theorem Expression.selectorIndices_one [Field F] :
    (1 : Expression F Query).selectorIndices = [] := rfl

@[keygen_norm]
theorem Expression.selectorIndices_coe [Field F] (value : F) :
    (value : Expression F Query).selectorIndices = [] := rfl

@[keygen_norm]
theorem Expression.selectorIndices_add
    (left right : Expression F Query) :
    (left + right).selectorIndices = left.selectorIndices ++ right.selectorIndices := rfl

@[keygen_norm]
theorem Expression.selectorIndices_mul
    (left right : Expression F Query) :
    (left * right).selectorIndices = left.selectorIndices ++ right.selectorIndices := rfl

@[keygen_norm]
theorem Expression.selectorIndices_neg [Field F]
    (expression : Expression F Query) :
    (-expression).selectorIndices = expression.selectorIndices := by
  simp [Expression.selectorIndices]

@[keygen_norm]
theorem Expression.selectorIndices_sub
    [Field F] (left right : Expression F Query) :
    (left - right).selectorIndices = left.selectorIndices ++ right.selectorIndices := by
  simp [Expression.selectorIndices]

/-- Selector indices used by a lookup input other than its distinguished master
selector. Multiplicity is harmless and keeps this a direct structural projection. -/
@[circuit_norm]
def LookupArgument.auxiliarySelectorIndices
    (argument : LookupArgument F) : List ℕ :=
  (argument.inputs.flatMap Expression.selectorIndices).filter
    (· != argument.masterSelector.index)

/-- Every selector that a lookup activation may enable: its mandatory master followed
by the auxiliary selectors occurring in its input expressions. -/
@[circuit_norm]
def LookupArgument.selectorIndices (argument : LookupArgument F) : List ℕ :=
  argument.masterSelector.index :: argument.auxiliarySelectorIndices

@[keygen_norm]
theorem LookupArgument.masterSelector_mem_selectorIndices
    (argument : LookupArgument F) :
    argument.masterSelector.index ∈ argument.selectorIndices :=
  List.mem_cons_self

/-- The selector-only projection of a lookup argument. This is the complete data
needed to check selector compatibility, without retaining its expressions. -/
structure LookupSelectorUsage where
  master : ComplexSelector
  auxiliary : List ℕ
  selectors : List ℕ
deriving DecidableEq, Repr

def LookupArgument.selectorUsage
    (argument : LookupArgument F) : LookupSelectorUsage where
  master := argument.masterSelector
  auxiliary := argument.auxiliarySelectorIndices
  selectors := argument.selectorIndices

def Selector.LookupSelectorsCompatible
    (gate : Selector) (argument : LookupSelectorUsage) : Prop :=
  (argument.auxiliary.Forall fun selector => selector ≠ gate.index) ∧
    (argument.master.index = gate.index → gate.simple = false)

def LookupSelectorUsage.SelectorsCompatible
    (source target : LookupSelectorUsage) : Prop :=
  source.selectors.Forall fun selector =>
    selector ∈ target.auxiliary → target.master.index = source.master.index

/-- A gate selector cannot double as an auxiliary selector of this lookup. -/
@[circuit_norm]
def Gate.LookupSelectorsCompatible
    (gate : Gate F) (argument : LookupArgument F) : Prop :=
  gate.selector.LookupSelectorsCompatible argument.selectorUsage

/-- Enabling selectors declared by `source` respects `target`'s master-selector rule.
This one-sided formulation permits harmless selector sharing whenever `target`'s
master is enabled as well. -/
@[circuit_norm]
def LookupArgument.SelectorsCompatible
    (source target : LookupArgument F) : Prop :=
  source.selectorUsage.SelectorsCompatible target.selectorUsage

@[circuit_norm]
theorem LookupArgument.selectorsCompatible_self
    (argument : LookupArgument F) : argument.SelectorsCompatible argument := by
  rw [LookupArgument.SelectorsCompatible,
    LookupSelectorUsage.SelectorsCompatible,
    LookupArgument.selectorUsage, List.forall_iff_forall_mem]
  intros
  rfl

/-- Static selector compatibility of explicit gate and lookup lists. -/
@[circuit_norm]
def LookupSelectorsCompatible
    (gates : List (Gate F)) (lookups : List (LookupArgument F)) : Prop :=
  (gates.Forall fun gate =>
      lookups.Forall (gate.LookupSelectorsCompatible ·)) ∧
    lookups.Forall fun source =>
      lookups.Forall source.SelectorsCompatible

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

/-- All fixed columns allocated in a completed constraint system. -/
def ConstraintSystem.fixedColumns
    (constraintSystem : ConstraintSystem F) : List (Column .fixed) :=
  (List.range constraintSystem.numFixedColumns).map Column.mk

theorem ConstraintSystem.mem_fixedColumns_iff
    (constraintSystem : ConstraintSystem F) (column : Column .fixed) :
    column ∈ constraintSystem.fixedColumns ↔
      column.index < constraintSystem.numFixedColumns := by
  rcases column with ⟨index⟩
  simp [ConstraintSystem.fixedColumns]

/-- Flatten a constraint system's gates to its ordered constraint-polynomial list. -/
def flatGates (cs : ConstraintSystem F) : List (Expression F Query) :=
  cs.gates.flatMap fun gate => gate.constraints.map (fun constraint => constraint.poly)

/-- Halo 2's `ConstraintSystem::degree`: the maximum of the permutation argument's
constant degree three, lookup requirements, and gate-polynomial degrees. -/
def csDegree (cs : ConstraintSystem F) : ℕ :=
  constraintDegree cs.gates cs.lookups

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


end Halo2
