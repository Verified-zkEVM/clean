import Clean.Halo2.Configure

namespace Halo2

variable {F : Type}

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
    (counts : ConfigureCounts)
    {cell : Expression F Query} (hcell : cell.QueryAllocated counts) :
    (ConfigureDelta.queriedCell cell).QueriesLawful counts := by
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
    (counts : ConfigureCounts)
    {cells : List (Expression F Query)}
    (hcells : cells.Forall (·.QueryAllocated counts)) :
    (ConfigureDelta.queriedCells cells).QueriesLawful counts := by
  unfold ConfigureDelta.queriedCells
  have aux (remaining : List (Expression F Query))
      (initial : ConfigureDelta F)
      (hremaining : remaining.Forall (·.QueryAllocated counts))
      (hinitial : initial.QueriesLawful counts) :
      (remaining.foldl
        (fun delta cell => delta.append (.queriedCell cell))
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
              counts hremaining.1)
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

/-- Every occurring selector index lies below the expression's selector bound. -/
theorem Expression.lt_selectorBound_of_mem_selectorIndices
    (expression : Expression F Query) {selector : ℕ}
    (hselector : selector ∈ expression.selectorIndices) :
    selector < expression.selectorBound := by
  induction expression with
  | var query =>
      cases query <;>
        simp_all [Expression.selectorIndices, Expression.selectorBound]
  | const value => simp [Expression.selectorIndices] at hselector
  | add left right ihLeft ihRight =>
      simp only [Expression.selectorIndices, List.mem_append] at hselector
      simp only [Expression.selectorBound]
      exact hselector.elim
        (fun hleft => (ihLeft hleft).trans_le (Nat.le_max_left _ _))
        (fun hright => (ihRight hright).trans_le (Nat.le_max_right _ _))
  | mul left right ihLeft ihRight =>
      simp only [Expression.selectorIndices, List.mem_append] at hselector
      simp only [Expression.selectorBound]
      exact hselector.elim
        (fun hleft => (ihLeft hleft).trans_le (Nat.le_max_left _ _))
        (fun hright => (ihRight hright).trans_le (Nat.le_max_right _ _))

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


end Halo2
