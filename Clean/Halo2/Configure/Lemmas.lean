import Clean.Halo2.Configure.Selectors

namespace Halo2

variable {F : Type}

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
    delta (complexSelector : Configure F ComplexSelector) counts = {} :=
  rfl

@[simp] theorem delta_createGate
    (gate : Gate F) (counts : ConfigureCounts) :
    delta (createGate gate) counts =
      (ConfigureDelta.queriedCells gate.queriedCells).append
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

@[simp] theorem fixedColumns_pure
    (value : α) (counts : ConfigureCounts) :
    fixedColumns (pure value : Configure F α) counts = [] := by
  simp [fixedColumns]

@[simp] theorem fixedColumns_adviceColumn (counts : ConfigureCounts) :
    fixedColumns (adviceColumn : Configure F (Column .advice)) counts = [] := by
  simp [fixedColumns, countDelta, adviceColumn]

@[simp] theorem fixedColumns_instanceColumn (counts : ConfigureCounts) :
    fixedColumns (instanceColumn : Configure F (Column .instance)) counts = [] := by
  simp [fixedColumns, countDelta, instanceColumn]

@[simp] theorem fixedColumns_selector (counts : ConfigureCounts) :
    fixedColumns (selector : Configure F Selector) counts = [] := by
  simp [fixedColumns, countDelta, selector]

@[simp] theorem fixedColumns_complexSelector (counts : ConfigureCounts) :
    fixedColumns (complexSelector : Configure F ComplexSelector) counts = [] := by
  simp [fixedColumns, countDelta, complexSelector]

@[simp] theorem fixedColumns_enableEquality
    (column : AnyColumn) (counts : ConfigureCounts) :
    fixedColumns (enableEquality (F := F) column) counts = [] := by
  simp [fixedColumns, countDelta, enableEquality]

@[simp] theorem fixedColumns_createGate
    (gate : Gate F) (counts : ConfigureCounts) :
    fixedColumns (createGate gate) counts = [] := by
  simp [fixedColumns, countDelta, createGate]

@[simp] theorem fixedColumns_lookup
    (queriedCells : List (Expression F Query))
    (masterSelector : ComplexSelector)
    (tableMap : List (Expression F Query × TableColumn))
    (hqueries : LookupQueriesDeclared queriedCells tableMap)
    (hnoSimpleSelectors :
      (tableMap.map Prod.fst).Forall Expression.NoSimpleSelectors)
    (counts : ConfigureCounts) :
    fixedColumns
      (lookup queriedCells masterSelector tableMap hqueries hnoSimpleSelectors)
      counts = [] := by
  simp [fixedColumns, countDelta, lookup]

@[simp] theorem fixedColumns_bind
    (program : Configure F α) (next : α → Configure F β)
    (counts : ConfigureCounts) :
    fixedColumns (program >>= next) counts =
      program.fixedColumns counts ++
        (next (program.output counts)).fixedColumns
          (program.finalCounts counts) := by
  simp only [fixedColumns, countDelta_bind,
    ConfigureCountDelta.append, finalCounts_numFixedColumns]
  rw [← List.map_append, List.range'_append_1]

/-- Fixed columns allocated by the first half of a configure bind remain allocated by
the composite program. -/
theorem mem_fixedColumns_bind_left
    (program : Configure F α) (next : α → Configure F β)
    (counts : ConfigureCounts) {column : Column .fixed}
    (hcolumn : column ∈ program.fixedColumns counts) :
    column ∈ (program >>= next).fixedColumns counts := by
  rw [fixedColumns_bind]
  exact List.mem_append_left _ hcolumn

/-- Fixed columns allocated by the second half of a configure bind are allocated by
the composite program. -/
theorem mem_fixedColumns_bind_right
    (program : Configure F α) (next : α → Configure F β)
    (counts : ConfigureCounts) {column : Column .fixed}
    (hcolumn : column ∈
      (next (program.output counts)).fixedColumns (program.finalCounts counts)) :
    column ∈ (program >>= next).fixedColumns counts := by
  rw [fixedColumns_bind]
  exact List.mem_append_right _ hcolumn

@[simp] theorem fixedColumns_fixedColumn (counts : ConfigureCounts) :
    fixedColumns (fixedColumn : Configure F (Column .fixed)) counts =
      [⟨counts.numFixedColumns⟩] := by
  simp [fixedColumns, countDelta, fixedColumn]

@[simp] theorem fixedColumns_lookupTableColumn (counts : ConfigureCounts) :
    fixedColumns (lookupTableColumn : Configure F TableColumn) counts =
      [⟨counts.numFixedColumns⟩] := by
  unfold lookupTableColumn
  simp

@[simp] theorem fixedColumns_enableConstant
    (column : Column .fixed) (counts : ConfigureCounts) :
    fixedColumns (enableConstant (F := F) column) counts = [] :=
  rfl

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

@[simp] theorem output_lookupTableColumn (counts : ConfigureCounts) :
    output (lookupTableColumn : Configure F TableColumn) counts =
      { inner := ⟨counts.numFixedColumns⟩ } :=
  rfl

@[simp] theorem finalCounts_lookupTableColumn (counts : ConfigureCounts) :
    finalCounts (lookupTableColumn : Configure F TableColumn) counts =
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
    output (complexSelector : Configure F ComplexSelector) counts =
      ⟨counts.numSelectors⟩ :=
  rfl

@[simp] theorem finalCounts_complexSelector (counts : ConfigureCounts) :
    finalCounts (complexSelector : Configure F ComplexSelector) counts =
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
    (masterSelector : ComplexSelector)
    (tableMap : List (Expression F Query × TableColumn))
    (hqueries : LookupQueriesDeclared queriedCells tableMap)
    (hnoSimpleSelectors :
      (tableMap.map Prod.fst).Forall Expression.NoSimpleSelectors)
    (counts : ConfigureCounts) :
    output (lookup queriedCells masterSelector tableMap hqueries
      hnoSimpleSelectors) counts = () :=
  rfl

@[simp] theorem finalCounts_lookup
    (queriedCells : List (Expression F Query))
    (masterSelector : ComplexSelector)
    (tableMap : List (Expression F Query × TableColumn))
    (hqueries : LookupQueriesDeclared queriedCells tableMap)
    (hnoSimpleSelectors :
      (tableMap.map Prod.fst).Forall Expression.NoSimpleSelectors)
    (counts : ConfigureCounts) :
    finalCounts (lookup queriedCells masterSelector tableMap hqueries
      hnoSimpleSelectors) counts = counts :=
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
    (cell : Expression F Query) :
    (ConfigureDelta.queriedCell cell).instanceQueries =
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
    (cells : List (Expression F Query))
    (initial : ConfigureDelta F) :
    (cells.foldl
      (fun delta cell => delta.append (.queriedCell cell))
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
    (cells : List (Expression F Query)) :
    (ConfigureDelta.queriedCells cells).instanceQueries =
      ConfigureDelta.instanceQueriesOfCells cells := by
  rw [ConfigureDelta.queriedCells]
  simpa [ConfigureDelta.instanceQueriesOfCells] using
    ConfigureDelta.queriedCells_instanceQueries_aux
      (F := F) cells {}

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
    (Configure.delta (complexSelector : Configure F ComplexSelector)
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
    (masterSelector : ComplexSelector)
    (tableMap : List (Expression F Query × TableColumn))
    (hqueries : LookupQueriesDeclared queriedCells tableMap)
    (hnoSimpleSelectors :
      (tableMap.map Prod.fst).Forall Expression.NoSimpleSelectors)
    (counts : ConfigureCounts) :
    (Configure.delta (lookup queriedCells masterSelector tableMap hqueries
      hnoSimpleSelectors) counts).instanceQueries =
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
    (cell : Expression F Query) :
    (ConfigureDelta.queriedCell cell).fixedQueries =
      match cell with
      | .var (.fixed column _) => [(column, 0)]
      | _ => [] := by
  cases cell with
  | var query =>
      cases query <;> rfl
  | const | add | mul => rfl

private theorem ConfigureDelta.queriedCells_fixedQueries_aux
    (cells : List (Expression F Query))
    (initial : ConfigureDelta F) :
    (cells.foldl
      (fun delta cell => delta.append (.queriedCell cell))
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
    (cells : List (Expression F Query)) :
    (ConfigureDelta.queriedCells cells).fixedQueries =
      ConfigureDelta.fixedQueriesOfCells cells := by
  rw [ConfigureDelta.queriedCells]
  simpa using ConfigureDelta.queriedCells_fixedQueries_aux
    (F := F) cells {}

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
    ((complexSelector : Configure F ComplexSelector).delta counts).fixedQueries = [] :=
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
    (masterSelector : ComplexSelector)
    (tableMap : List (Expression F Query × TableColumn))
    (hqueries : LookupQueriesDeclared queriedCells tableMap)
    (hnoSimpleSelectors :
      (tableMap.map Prod.fst).Forall Expression.NoSimpleSelectors)
    (counts : ConfigureCounts) :
    ((lookup queriedCells masterSelector tableMap hqueries
      hnoSimpleSelectors).delta counts).fixedQueries =
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

end Halo2
