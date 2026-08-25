import Clean.Halo2.Configure.Lemmas

namespace Halo2

variable {F : Type}

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
  /-- Exact reduced degree of the gates and lookups emitted by this program. -/
  constraintDegree : ConfigureCounts → ℕ
  constraintDegree_eq : ∀ counts,
    (program.delta counts).constraintDegree = constraintDegree counts
  instanceQueries :
    ConfigureCounts → List (Column .instance × Rotation) := fun _ => []
  instanceQueries_eq : ∀ counts,
    (program.delta counts).instanceQueries =
      instanceQueries counts := by
    configure_norm
  /-- Reduced gate/lookup selector usage. Parent configure programs use this summary
  to check cross-child compatibility without reopening child expressions. -/
  selectorSummary : ConfigureCounts → ConfigureSelectorSummary :=
    fun counts => (program.delta counts).selectorSummary
  selectorSummary_eq : ∀ counts,
    (program.delta counts).selectorSummary = selectorSummary counts := by
    intro counts
    rfl
  /-- Selector usages inherited from the incoming configure state. Closed child
  programs normally reduce this to the empty summary. -/
  externalSelectorSummary : ConfigureCounts → ConfigureSelectorSummary :=
    fun counts => (selectorSummary counts).externalAt counts.numSelectors
  externalSelectorSummary_eq : ∀ counts,
    (selectorSummary counts).externalAt counts.numSelectors =
      externalSelectorSummary counts := by
    intro counts
    rfl
  /--
  Selector allocation required from the incoming configure state. Primitive gate and
  lookup registration expose requirements; monadic bind composes them.
  -/
  selectorRequirements : ConfigureCounts → Prop := fun _ => True
  selectorsAllocated : ∀ counts, selectorRequirements counts →
    (program.delta counts).SelectorsAllocated
      (program.finalCounts counts).numSelectors
  /-- Gate and lookup selector sets emitted by configure are mutually compatible. -/
  lookupSelectorsCompatible : ∀ counts, selectorRequirements counts →
    (program.delta counts).LookupSelectorsCompatible := by
    intro counts _
    simp [ConfigureDelta.LookupSelectorsCompatible,
      Halo2.LookupSelectorsCompatible]
  /-- Query allocation required from the incoming configure state. Gate and lookup
  registration expose the columns they reference; monadic bind composes them. -/
  queryRequirements : ConfigureCounts → Prop := fun counts =>
    (program.delta counts).QueriesLawful (program.finalCounts counts)
  queriesLawful : ∀ counts, queryRequirements counts →
    (program.delta counts).QueriesLawful
      (program.finalCounts counts) := by
    intro _ hqueries
    exact hqueries

namespace ElaboratedConfigure

/-- Replace a discharged selector requirement by its reduced `True` summary. Parent
configure programs can then consume the resulting allocation and compatibility facts
without replaying the child's configure tree. -/
@[reducible] def closeSelectorRequirements
    {program : Configure F α} (self : ElaboratedConfigure program)
    (requirements : ∀ counts, self.selectorRequirements counts) :
    ElaboratedConfigure program :=
  { self with
    selectorRequirements _ := True
    selectorsAllocated counts _ :=
      self.selectorsAllocated counts (requirements counts)
    lookupSelectorsCompatible counts _ :=
      self.lookupSelectorsCompatible counts (requirements counts) }

@[configure_selector_norm, keygen_norm]
theorem closeSelectorRequirements_selectorSummary
    {program : Configure F α} (self : ElaboratedConfigure program)
    (requirements : ∀ counts, self.selectorRequirements counts)
    (counts : ConfigureCounts) :
    (self.closeSelectorRequirements requirements).selectorSummary counts =
      self.selectorSummary counts := rfl

@[configure_selector_norm, keygen_norm]
theorem closeSelectorRequirements_externalSelectorSummary
    {program : Configure F α} (self : ElaboratedConfigure program)
    (requirements : ∀ counts, self.selectorRequirements counts)
    (counts : ConfigureCounts) :
    (self.closeSelectorRequirements requirements).externalSelectorSummary counts =
      self.externalSelectorSummary counts := rfl

/-- Replace computed external-selector provenance by its reduced circuit-local
summary. Parents consume this small interface instead of reopening the configure
program that established it. -/
@[reducible] def withExternalSelectorSummary
    {program : Configure F α} (self : ElaboratedConfigure program)
    (summary : ConfigureCounts → ConfigureSelectorSummary)
    (summary_eq : ∀ counts,
      (self.selectorSummary counts).externalAt counts.numSelectors =
        summary counts) : ElaboratedConfigure program :=
  { self with
    externalSelectorSummary := summary
    externalSelectorSummary_eq := summary_eq }

/-- Close selector provenance when a configure program only uses selectors allocated
at or after its incoming selector count. -/
@[reducible] def withNoExternalSelectors
    {program : Configure F α} (self : ElaboratedConfigure program)
    (fresh : ∀ counts,
      (program.delta counts).SelectorsFreshFrom counts.numSelectors) :
    ElaboratedConfigure program :=
  self.withExternalSelectorSummary (fun _ => {}) (by
    intro counts
    rw [← self.selectorSummary_eq]
    exact ConfigureDelta.selectorSummary_externalAt_eq_empty_of_fresh
      (fresh counts))

@[simp] theorem delta_instanceQueries
    (program : Configure F α) [elaborated : ElaboratedConfigure program]
    (counts : ConfigureCounts) :
    (program.delta counts).instanceQueries =
      elaborated.instanceQueries counts :=
  elaborated.instanceQueries_eq counts

@[simp] theorem delta_constraintDegree
    (program : Configure F α) [elaborated : ElaboratedConfigure program]
    (counts : ConfigureCounts) :
    (program.delta counts).constraintDegree =
      elaborated.constraintDegree counts :=
  elaborated.constraintDegree_eq counts

/-- A closed configure program's reduced degree is exactly the degree of the
constraint system obtained by running it from the empty state. -/
theorem csDegree_run_empty
    (program : Configure F α) [elaborated : ElaboratedConfigure program] :
    csDegree (program.run {}).2 = elaborated.constraintDegree {} := by
  rw [Configure.csDegree_run, ConfigureCounts.ofConstraintSystem_empty]
  have hdegree : csDegree ({} : ConstraintSystem F) ≤
      (program.delta {}).constraintDegree := by
    simp [csDegree, ConfigureDelta.constraintDegree,
      Halo2.constraintDegree]
  rw [Nat.max_eq_right hdegree, elaborated.constraintDegree_eq]

instance pure (value : α) :
    ElaboratedConfigure (pure value : Configure F α) where
  constraintDegree _ := 3
  constraintDegree_eq := by intro counts; rfl
  instanceQueries_eq := by
    intro counts
    rfl
  selectorSummary _ := {}
  selectorRequirements _ := True
  selectorsAllocated := by
    intro counts _
    exact ConfigureDelta.SelectorsAllocated.empty counts.numSelectors
  queryRequirements _ := True
  queriesLawful := by
    intro counts _
    exact ConfigureDelta.QueriesLawful.empty counts

instance bind {β : Type}
    (program : Configure F α) [programElaborated : ElaboratedConfigure program]
    (next : α → Configure F β)
    [nextElaborated : ∀ value, ElaboratedConfigure (next value)] :
    ElaboratedConfigure (program >>= next) where
  constraintDegree counts :=
    max (programElaborated.constraintDegree counts)
      ((nextElaborated (program.output counts)).constraintDegree
        (program.finalCounts counts))
  constraintDegree_eq := by
    intro counts
    rw [Configure.delta_bind, ConfigureDelta.constraintDegree_append,
      programElaborated.constraintDegree_eq,
      (nextElaborated (program.output counts)).constraintDegree_eq]
  instanceQueries counts :=
    programElaborated.instanceQueries counts ++
      (nextElaborated (program.output counts)).instanceQueries
        (program.finalCounts counts)
  instanceQueries_eq := by
    intro counts
    rw [Configure.delta_bind, ConfigureDelta.instanceQueries_append,
      programElaborated.instanceQueries_eq,
      (nextElaborated (program.output counts)).instanceQueries_eq]
  selectorSummary counts :=
    (programElaborated.selectorSummary counts).append
      ((nextElaborated (program.output counts)).selectorSummary
        (program.finalCounts counts))
  selectorSummary_eq := by
    intro counts
    rw [Configure.delta_bind, ConfigureDelta.selectorSummary_append,
      programElaborated.selectorSummary_eq,
      (nextElaborated (program.output counts)).selectorSummary_eq]
  externalSelectorSummary counts :=
    (programElaborated.externalSelectorSummary counts).append
      (((nextElaborated (program.output counts)).externalSelectorSummary
        (program.finalCounts counts)).externalAt counts.numSelectors)
  externalSelectorSummary_eq := by
    intro counts
    rw [ConfigureSelectorSummary.externalAt_append,
      programElaborated.externalSelectorSummary_eq,
      ← (nextElaborated
        (program.output counts)).externalSelectorSummary_eq]
    rw [ConfigureSelectorSummary.externalAt_externalAt _
      (program.numSelectors_le_finalCounts counts)]
  selectorRequirements counts :=
    programElaborated.selectorRequirements counts ∧
      (nextElaborated (program.output counts)).selectorRequirements
        (program.finalCounts counts) ∧
      (programElaborated.selectorSummary counts).CrossCompatible
        ((nextElaborated
          (program.output counts)).externalSelectorSummary
            (program.finalCounts counts))
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
          (program.finalCounts counts) hrequirements.2.1
  lookupSelectorsCompatible := by
    intro counts hrequirements
    rw [Configure.delta_bind]
    exact ConfigureDelta.lookupSelectorsCompatible_append _ _
      (programElaborated.lookupSelectorsCompatible counts hrequirements.1)
      ((nextElaborated (program.output counts)).lookupSelectorsCompatible
        (program.finalCounts counts) hrequirements.2.1)
      (ConfigureDelta.LookupSelectorsCrossCompatible.ofSelectorSummary (by
        apply ConfigureSelectorSummary.CrossCompatible.of_externalAt
          (boundary := (program.finalCounts counts).numSelectors)
        · exact ConfigureDelta.selectorSummary_bounded
            ((programElaborated.selectorsAllocated counts
              hrequirements.1).selectorsBounded)
        · rw [programElaborated.selectorSummary_eq,
            (nextElaborated (program.output counts)).selectorSummary_eq,
            (nextElaborated
              (program.output counts)).externalSelectorSummary_eq]
          exact hrequirements.2.2))
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

instance adviceColumn :
    ElaboratedConfigure (adviceColumn : Configure F (Column .advice)) where
  constraintDegree _ := 3
  constraintDegree_eq := by intro counts; rfl
  instanceQueries_eq := Configure.delta_adviceColumn_instanceQueries
  selectorSummary _ := {}
  selectorRequirements _ := True
  selectorsAllocated := by
    intro counts _
    exact ConfigureDelta.SelectorsAllocated.empty counts.numSelectors
  queryRequirements _ := True
  queriesLawful := by
    intro counts _
    exact ConfigureDelta.QueriesLawful.empty _

instance fixedColumn :
    ElaboratedConfigure (fixedColumn : Configure F (Column .fixed)) where
  constraintDegree _ := 3
  constraintDegree_eq := by intro counts; rfl
  instanceQueries_eq := Configure.delta_fixedColumn_instanceQueries
  selectorSummary _ := {}
  selectorRequirements _ := True
  selectorsAllocated := by
    intro counts _
    exact ConfigureDelta.SelectorsAllocated.empty counts.numSelectors
  queryRequirements _ := True
  queriesLawful := by
    intro counts _
    exact ConfigureDelta.QueriesLawful.empty _

instance instanceColumn :
    ElaboratedConfigure (instanceColumn : Configure F (Column .instance)) where
  constraintDegree _ := 3
  constraintDegree_eq := by intro counts; rfl
  instanceQueries_eq := Configure.delta_instanceColumn_instanceQueries
  selectorSummary _ := {}
  selectorRequirements _ := True
  selectorsAllocated := by
    intro counts _
    exact ConfigureDelta.SelectorsAllocated.empty counts.numSelectors
  queryRequirements _ := True
  queriesLawful := by
    intro counts _
    exact ConfigureDelta.QueriesLawful.empty _

instance selector :
    ElaboratedConfigure (selector : Configure F Selector) where
  constraintDegree _ := 3
  constraintDegree_eq := by intro counts; rfl
  instanceQueries_eq := Configure.delta_selector_instanceQueries
  selectorSummary _ := {}
  selectorRequirements _ := True
  selectorsAllocated := by
    intro counts _
    exact ConfigureDelta.SelectorsAllocated.empty
      (counts.numSelectors + 1)
  queryRequirements _ := True
  queriesLawful := by
    intro counts _
    exact ConfigureDelta.QueriesLawful.empty _

instance complexSelector :
    ElaboratedConfigure (complexSelector : Configure F ComplexSelector) where
  constraintDegree _ := 3
  constraintDegree_eq := by intro counts; rfl
  instanceQueries_eq := Configure.delta_complexSelector_instanceQueries
  selectorSummary _ := {}
  selectorRequirements _ := True
  selectorsAllocated := by
    intro counts _
    exact ConfigureDelta.SelectorsAllocated.empty
      (counts.numSelectors + 1)
  queryRequirements _ := True
  queriesLawful := by
    intro counts _
    exact ConfigureDelta.QueriesLawful.empty _

instance enableEquality (column : AnyColumn) :
    ElaboratedConfigure (enableEquality (F := F) column) where
  constraintDegree _ := 3
  constraintDegree_eq := by
    intro counts
    rcases column with ⟨kind, index⟩
    cases kind <;> rfl
  instanceQueries _ :=
    match column with
    | ⟨.instance, index⟩ => [(⟨index⟩, 0)]
    | _ => []
  instanceQueries_eq :=
    Configure.delta_enableEquality_instanceQueries column
  selectorSummary _ := {}
  selectorSummary_eq := by
    intro counts
    rcases column with ⟨kind, index⟩
    cases kind <;>
      simp [ConfigureDelta.selectorSummary, Configure.delta,
        Halo2.enableEquality, ConfigureDelta.queryAny]
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

instance enableConstant (column : Column .fixed) :
    ElaboratedConfigure (enableConstant (F := F) column) where
  constraintDegree _ := 3
  constraintDegree_eq := by intro counts; rfl
  instanceQueries_eq :=
    Configure.delta_enableConstant_instanceQueries column
  selectorSummary _ := {}
  selectorRequirements _ := True
  selectorsAllocated := by
    intro counts _
    constructor
    · simp [Configure.delta, Configure.finalCounts,
        Configure.countDelta, ConfigureCountDelta.apply,
        Halo2.enableConstant]
    · simp [Configure.delta, Configure.finalCounts,
        Configure.countDelta, ConfigureCountDelta.apply,
        Halo2.enableConstant]
    · simp [Configure.delta, Configure.finalCounts,
        Configure.countDelta, ConfigureCountDelta.apply,
        Halo2.enableConstant, lookupInputSelectorBound]
  lookupSelectorsCompatible := by
    intro counts _
    simp [ConfigureDelta.LookupSelectorsCompatible,
      Halo2.LookupSelectorsCompatible, Configure.delta,
      Halo2.enableConstant]
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

instance createGate (gate : Gate F) :
    ElaboratedConfigure (createGate gate) where
  constraintDegree _ := Halo2.constraintDegree [gate] []
  constraintDegree_eq := by
    intro counts
    simp [ConfigureDelta.constraintDegree, Configure.delta,
      Halo2.createGate]
  instanceQueries := fun _ =>
    ConfigureDelta.instanceQueriesOfCells gate.queriedCells
  instanceQueries_eq :=
    Configure.delta_createGate_instanceQueries gate
  selectorSummary _ := { gates := [gate.selector] }
  selectorSummary_eq := by
    intro counts
    simp [ConfigureDelta.selectorSummary, Configure.delta,
      Halo2.createGate]
  selectorRequirements counts :=
    gate.selector.index < counts.numSelectors
  selectorsAllocated := by
    intro counts hselector
    constructor
    · simpa [Configure.delta_createGate] using hselector
    · simp [Configure.delta_createGate]
    · simp [Configure.delta_createGate, lookupInputSelectorBound]
  queryRequirements counts :=
    gate.queriedCells.Forall (·.QueryAllocated counts)
  queriesLawful := by
    intro counts hqueries
    let queryDelta := ConfigureDelta.queriedCells
      (F := F) gate.queriedCells
    have hqueryDelta : queryDelta.QueriesLawful counts :=
      ConfigureDelta.queriedCells_queriesLawful counts hqueries
    have hgateQueries : gate.QueriesRegistered queryDelta :=
      gate.wellFormed.constraintQueriesDeclared.imp fun _ hconstraint =>
        hconstraint.queriesRegistered_queriedCells
          gate.wellFormed.queriedCellsValid
    have hcombined :
        (queryDelta.append { gates := [gate] }).QueriesLawful counts := by
      constructor
      · simpa [ConfigureDelta.append] using
          hqueryDelta.adviceQueries_fst_lt_numAdviceColumns
      · simpa [ConfigureDelta.append] using
          hqueryDelta.fixedQueries_fst_lt_numFixedColumns
      · simpa [ConfigureDelta.append] using
          hqueryDelta.instanceQueries_fst_lt_numInstanceColumns
      · simpa [queryDelta] using
          (Gate.QueriesRegistered.append_left
            (right := ({ gates := [gate] } : ConfigureDelta F)) hgateQueries)
      · simpa [queryDelta] using
          (Gate.QueriedCellsRegistered.append_left
            (right := ({ gates := [gate] } : ConfigureDelta F))
            (ConfigureDelta.queriedCells_queriesRegistered
              gate.wellFormed.queriedCellsValid))
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

instance lookup
    (queriedCells : List (Expression F Query))
    (masterSelector : ComplexSelector)
    (tableMap : List (Expression F Query × TableColumn))
    (hqueries : LookupQueriesDeclared queriedCells tableMap)
    (hnoSimpleSelectors :
      (tableMap.map Prod.fst).Forall Expression.NoSimpleSelectors) :
    ElaboratedConfigure (lookup queriedCells masterSelector tableMap hqueries
      hnoSimpleSelectors) where
  constraintDegree counts :=
    ((Halo2.lookup queriedCells masterSelector tableMap hqueries
      hnoSimpleSelectors).delta counts).constraintDegree
  constraintDegree_eq := by intro counts; rfl
  instanceQueries := fun _ =>
    ConfigureDelta.instanceQueriesOfCells queriedCells
  instanceQueries_eq :=
    Configure.delta_lookup_instanceQueries queriedCells masterSelector tableMap hqueries
      hnoSimpleSelectors
  selectorSummary _ :=
    let auxiliary :=
      ((tableMap.map Prod.fst).flatMap Expression.selectorIndices).filter
        (· != masterSelector.index)
    { lookups :=
        [{ master := masterSelector
           auxiliary
           selectors := masterSelector.index :: auxiliary }] }
  selectorSummary_eq := by
    intro counts
    simp [ConfigureDelta.selectorSummary, Configure.delta, Halo2.lookup,
      ConfigureDelta.fixedQueriesOfColumns, foldlTableDelta_gates,
      foldlTableDelta_lookups, LookupArgument.selectorUsage,
      LookupArgument.selectorIndices, LookupArgument.auxiliarySelectorIndices]
  selectorRequirements counts :=
    masterSelector.index < counts.numSelectors ∧
      lookupInputSelectorBound
        ((Halo2.lookup queriedCells masterSelector tableMap hqueries
          hnoSimpleSelectors).delta counts).lookups ≤
          counts.numSelectors
  selectorsAllocated := by
    intro counts hselectors
    constructor
    · simp [Configure.delta_lookup_gates]
    · simpa [Configure.delta, Halo2.lookup,
        ConfigureDelta.fixedQueriesOfColumns, foldlTableDelta_lookups] using
        hselectors.1
    · simpa using hselectors.2
  lookupSelectorsCompatible := by
    intro counts _
    unfold ConfigureDelta.LookupSelectorsCompatible
      Halo2.LookupSelectorsCompatible
    rw [Configure.delta_lookup_gates]
    constructor
    · simp
    · unfold Configure.delta Halo2.lookup
      simp [ConfigureDelta.fixedQueriesOfColumns,
        foldlTableDelta_lookups,
        LookupArgument.selectorsCompatible_self]
  queryRequirements counts :=
    queriedCells.Forall (·.QueryAllocated counts) ∧
      (tableMap.map Prod.snd).Forall fun table =>
        table.inner.index < counts.numFixedColumns
  queriesLawful := by
    intro counts hrequirements
    let queryDelta := ConfigureDelta.queriedCells
      (F := F) queriedCells
    let tableDelta := ConfigureDelta.fixedQueriesOfColumns
      (F := F) (tableMap.map Prod.snd)
    have hqueryDelta : queryDelta.QueriesLawful counts :=
      ConfigureDelta.queriedCells_queriesLawful counts hrequirements.1
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
            hqueries.1).append_left.append_left
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

instance lookupTableColumn :
    ElaboratedConfigure (lookupTableColumn : Configure F TableColumn) := by
  unfold Halo2.lookupTableColumn
  infer_instance

end ElaboratedConfigure

attribute [configure_selector_norm] ElaboratedConfigure.pure ElaboratedConfigure.bind
attribute [configure_query_norm] ElaboratedConfigure.pure ElaboratedConfigure.bind
attribute [configure_selector_norm] List.nil_append List.append_nil List.filter_nil

open Lean Meta Simp in
/-- Fold the reduced selector summary stored in an inferred configure elaboration. -/
def foldElaboratedConfigureSelectorSummaryProc : Simproc := fun expression => do
  unless expression.getAppFn.isConstOf ``ElaboratedConfigure.selectorSummary ||
      expression.getAppFn.isConstOf
        ``ElaboratedConfigure.externalSelectorSummary do
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

simproc foldElaboratedConfigureSelectorSummary
    (ElaboratedConfigure.selectorSummary _ _) :=
  foldElaboratedConfigureSelectorSummaryProc
attribute [configure_selector_norm] foldElaboratedConfigureSelectorSummary

simproc foldElaboratedConfigureExternalSelectorSummary
    (ElaboratedConfigure.externalSelectorSummary _ _) :=
  foldElaboratedConfigureSelectorSummaryProc
attribute [configure_selector_norm]
  foldElaboratedConfigureExternalSelectorSummary

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
