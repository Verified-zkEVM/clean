import Clean.Halo2.Configure.Delta

namespace Halo2

variable {F : Type}

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

/-- Fixed columns allocated by this configure program, in allocation order. -/
def fixedColumns (program : Configure F α)
    (counts : ConfigureCounts) : List (Column .fixed) :=
  (List.range' counts.numFixedColumns
    (program.countDelta counts).numFixedColumns).map Column.mk

theorem fixedColumns_nodup (program : Configure F α)
    (counts : ConfigureCounts) :
    (program.fixedColumns counts).Nodup := by
  apply List.Nodup.map
  · intro left right heq
    exact congrArg Column.index heq
  · exact List.nodup_range'

theorem mem_fixedColumns_iff
    (program : Configure F α) (counts : ConfigureCounts)
    (column : Column .fixed) :
    column ∈ program.fixedColumns counts ↔
      counts.numFixedColumns ≤ column.index ∧
        column.index < (program.finalCounts counts).numFixedColumns := by
  rcases column with ⟨index⟩
  simp [fixedColumns, finalCounts, ConfigureCountDelta.apply]

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

-- TODO HALO2 this has the wrong input type: it only depends on counts, the rest of
-- `initial` is thrown away.
def run (program : Configure F α) (initial : ConstraintSystem F) :
    α × ConstraintSystem F :=
  let counts := ConfigureCounts.ofConstraintSystem initial
  let (output, delta, countDelta) := program.plan counts
  (output, delta.apply initial (countDelta.apply counts))

theorem csDegree_run (program : Configure F α)
    (initial : ConstraintSystem F) :
    csDegree (program.run initial).2 =
      max (csDegree initial)
        (program.delta
          (ConfigureCounts.ofConstraintSystem initial)).constraintDegree := by
  exact ConfigureDelta.csDegree_apply _ _ _

/-- Running a configure program returns the same value as its compositional
`output` projection at the initial constraint system's allocation counts. -/
theorem run_fst (program : Configure F α) (initial : ConstraintSystem F) :
    (program.run initial).1 =
      program.output (ConfigureCounts.ofConstraintSystem initial) :=
  rfl

-- TODO HALO2 are we missing a `Configure.constraintSystem` method as the canonical spelling
-- for `(program.run initial).2`? I see a lot of `.2` in this file

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

theorem mem_constants_run_iff
    (program : Configure F α) (initial : ConstraintSystem F)
    (column : Column .fixed) :
    column ∈ (program.run initial).2.constants ↔
      column ∈ initial.constants ∨
        column ∈
          (program.delta
            (ConfigureCounts.ofConstraintSystem initial)).constants := by
  simp only [run, delta, ConfigureDelta.apply, mem_appendFirstEncounters]

/-- Configure interpretation preserves the first-encounter invariant of the
permutation-column list. -/
theorem permutationColumns_run_nodup
    (program : Configure F α) (initial : ConstraintSystem F)
    (hinitial : initial.permutationColumns.Nodup) :
    (program.run initial).2.permutationColumns.Nodup := by
  exact nodup_appendFirstEncounters _ _ hinitial

/-- Configure interpretation retains each constants column only at its first request. -/
theorem constants_run_nodup
    (program : Configure F α) (initial : ConstraintSystem F)
    (hinitial : initial.constants.Nodup) :
    (program.run initial).2.constants.Nodup := by
  exact nodup_appendFirstEncounters _ _ hinitial

/-- Configure interpretation retains each fixed query only at its first request. -/
theorem fixedQueries_run_nodup
    (program : Configure F α) (initial : ConstraintSystem F)
    (hinitial : initial.fixedQueries.Nodup) :
    (program.run initial).2.fixedQueries.Nodup := by
  exact nodup_appendFirstEncounters _ _ hinitial

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

def ConfigureDelta.queriedCell :
    Expression F Query → ConfigureDelta F
  | .var (.advice column rotation) =>
      { adviceQueries := [(column, rotation)] }
  | .var (.fixed column _) =>
      { fixedQueries := [(column, 0)] }
  | .var (.instance column rotation) =>
      { instanceQueries := [(column, rotation)] }
  | _ => {}

def ConfigureDelta.queriedCells
    (cells : List (Expression F Query)) : ConfigureDelta F :=
  cells.foldl
    (fun delta cell => delta.append (.queriedCell cell)) {}

/-- Rotation-zero fixed-query requests emitted by lookup table columns, in program
order. -/
def ConfigureDelta.fixedQueriesOfColumns
    (columns : List TableColumn) : ConfigureDelta F :=
  columns.foldl
    (fun delta column =>
      delta.append { fixedQueries := [(column.inner, 0)] }) {}

theorem ConfigureDelta.queriedCell_registersQuery
    {query : Query}
    (hvalid : (Expression.var query : Expression F Query).QueryAtom) :
    (ConfigureDelta.queriedCell (F := F) (.var query)).RegistersQuery query := by
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
    {cells : List (Expression F Query)} {query : Query}
    (hvalid : cells.Forall Expression.QueryAtom)
    (hquery : (Expression.var query : Expression F Query) ∈ cells) :
    (ConfigureDelta.queriedCells cells).RegistersQuery query := by
  unfold ConfigureDelta.queriedCells
  have aux (remaining : List (Expression F Query))
      (initial : ConfigureDelta F)
      (hremaining : remaining.Forall Expression.QueryAtom)
      (hquery : initial.RegistersQuery query ∨
        (Expression.var query : Expression F Query) ∈ remaining) :
      (remaining.foldl
        (fun delta cell => delta.append (.queriedCell cell))
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
                  hremaining.1).append_right
            · exact Or.inr hquery
  exact aux cells {} hvalid (Or.inr hquery)

/-- Every valid atom in a gate's query declaration is registered by the declaration
writer itself. -/
theorem ConfigureDelta.queriedCells_queriesRegistered
    {cells : List (Expression F Query)}
    (hvalid : cells.Forall Expression.QueryAtom) :
    cells.Forall
      (·.QueriesRegistered (ConfigureDelta.queriedCells cells)) := by
  rw [List.forall_iff_forall_mem]
  intro cell hcell
  have hatom := List.forall_iff_forall_mem.mp hvalid cell hcell
  cases cell with
  | var query =>
      cases query with
      | selector => simp [Expression.QueryAtom] at hatom
      | advice | «instance» =>
          exact ConfigureDelta.queriedCells_registersQuery_of_mem
            hvalid hcell
      | fixed column rotation =>
          simp only [Expression.QueryAtom] at hatom
          subst rotation
          exact ConfigureDelta.queriedCells_registersQuery_of_mem
            hvalid hcell
  | const | add | mul => simp [Expression.QueryAtom] at hatom

/-- Syntactic query declaration entails semantic registration by the corresponding
configure delta. -/
theorem Expression.QueriesDeclared.queriesRegistered_queriedCells
    {cells : List (Expression F Query)}
    {expression : Expression F Query}
    (hvalid : cells.Forall Expression.QueryAtom)
    (hdeclared : expression.QueriesDeclared cells) :
    expression.QueriesRegistered (ConfigureDelta.queriedCells cells) := by
  induction expression with
  | var query =>
      cases query with
      | selector => trivial
      | advice | fixed | «instance» =>
          exact ConfigureDelta.queriedCells_registersQuery_of_mem
            hvalid hdeclared
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
def complexSelector : Configure F ComplexSelector :=
  ⟨fun counts =>
    (⟨counts.numSelectors⟩, {},
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
theorem Configure.countDelta_enableEquality
    (column : AnyColumn) (counts : ConfigureCounts) :
    (enableEquality (F := F) column).countDelta counts = {} :=
  rfl

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

@[simp] theorem Configure.delta_enableEquality_constants
    (column : AnyColumn) (counts : ConfigureCounts) :
    ((enableEquality (F := F) column).delta counts).constants = [] := by
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
      permutationRequests := [col]
    }, {})⟩

@[simp] theorem Configure.delta_enableConstant_constants
    (column : Column .fixed) (counts : ConfigureCounts) :
    ((enableConstant (F := F) column).delta counts).constants = [column] :=
  rfl

/-- Rust: `meta.lookup_table_column()`. -/
def lookupTableColumn : Configure F TableColumn := do
  return { inner := ← fixedColumn }

@[simp] theorem Configure.delta_lookupTableColumn_gates
    (counts : ConfigureCounts) :
    ((lookupTableColumn : Configure F TableColumn).delta counts).gates = [] :=
  rfl

@[simp] theorem Configure.delta_lookupTableColumn_lookups
    (counts : ConfigureCounts) :
    ((lookupTableColumn : Configure F TableColumn).delta counts).lookups = [] :=
  rfl

@[simp] theorem Configure.delta_lookupTableColumn_constants
    (counts : ConfigureCounts) :
    ((lookupTableColumn : Configure F TableColumn).delta counts).constants = [] :=
  rfl

/-- Rust: `meta.create_gate(name, |meta| Constraints::with_selector(guard, [...]))`.
Registers the gate's `queriedCells` in list order (the closure's queries all execute
before the gate is pushed, `circuit.rs:1195-1229`), then appends the gate. -/
def createGate (gate : Gate F) : Configure F Unit :=
  ⟨fun _ =>
    ((), (ConfigureDelta.queriedCells gate.queriedCells).append
      { gates := [gate] }, {})⟩

@[simp]
theorem Configure.countDelta_createGate
    (gate : Gate F) (counts : ConfigureCounts) :
    (createGate gate).countDelta counts = {} :=
  rfl

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
    (masterSelector : ComplexSelector)
    (tableMap : List (Expression F Query × TableColumn))
    (_hqueries : LookupQueriesDeclared queriedCells tableMap := by
      query_correct)
    (_hnoSimpleSelectors :
      (tableMap.map Prod.fst).Forall Expression.NoSimpleSelectors := by
      simp [Expression.NoSimpleSelectors]) : Configure F Unit :=
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
  have inputsNoSimpleSelectors :
      inputs.Forall Expression.NoSimpleSelectors :=
    _hnoSimpleSelectors
  let argument : LookupArgument F :=
    { masterSelector := masterSelector
      inputs := inputs
      tables := tables
      inputsNoSimpleSelectors := inputsNoSimpleSelectors
      tablesFree := tablesFree
      arity := arity }
  ⟨fun _ =>
    let queryDelta := ConfigureDelta.queriedCells queriedCells
    let tableDelta := ConfigureDelta.fixedQueriesOfColumns
      (tableMap.map Prod.snd)
    ((), queryDelta.append tableDelta |>.append
      { lookups := [argument] }, {})⟩

@[simp] theorem ConfigureDelta.gates_append
    (left right : ConfigureDelta F) :
    (left.append right).gates = left.gates ++ right.gates :=
  rfl

@[simp] theorem ConfigureDelta.lookups_append
    (left right : ConfigureDelta F) :
    (left.append right).lookups = left.lookups ++ right.lookups :=
  rfl

end Halo2
