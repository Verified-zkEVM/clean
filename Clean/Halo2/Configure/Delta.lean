import Clean.Halo2.ConstraintSystem

namespace Halo2

variable {F : Type}

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

-- TODO HALO2 it's silly to use a separate type from ConfigureCounts here
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

-- TODO HALO2 is there any reason to not have the counts be part of this delta?
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

/-- Exact degree of the gate and lookup arguments emitted by this configure delta. -/
def ConfigureDelta.constraintDegree (delta : ConfigureDelta F) : ℕ :=
  Halo2.constraintDegree delta.gates delta.lookups

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

@[simp] theorem ConfigureDelta.append_constants
    (left right : ConfigureDelta F) :
    (left.append right).constants = left.constants ++ right.constants :=
  rfl

@[simp] theorem ConfigureDelta.empty_append (delta : ConfigureDelta F) :
    ({} : ConfigureDelta F).append delta = delta := by
  cases delta
  rfl

@[simp] theorem ConfigureDelta.append_empty (delta : ConfigureDelta F) :
    delta.append ({} : ConfigureDelta F) = delta := by
  cases delta
  simp [ConfigureDelta.append]

@[simp] theorem ConfigureDelta.constraintDegree_append
    (left right : ConfigureDelta F) :
    (left.append right).constraintDegree =
      max left.constraintDegree right.constraintDegree := by
  change Halo2.constraintDegree (left.gates ++ right.gates)
      (left.lookups ++ right.lookups) =
    max (Halo2.constraintDegree left.gates left.lookups)
      (Halo2.constraintDegree right.gates right.lookups)
  exact Halo2.constraintDegree_append _ _ _ _

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

def appendFirstEncounters {α : Type} [DecidableEq α]
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

theorem nodup_appendFirstEncounters {α : Type} [DecidableEq α]
    (initial requests : List α) (hinitial : initial.Nodup) :
    (appendFirstEncounters initial requests).Nodup := by
  induction requests generalizing initial with
  | nil => simpa [appendFirstEncounters] using hinitial
  | cons request requests inductionHypothesis =>
      rw [appendFirstEncounters, List.foldl_cons]
      apply inductionHypothesis
      by_cases hrequest : request ∈ initial
      · simpa [hrequest] using hinitial
      · simp only [hrequest, if_false]
        exact hinitial.append (by simp : [request].Nodup)
          (by simpa using hrequest)

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
  constants := appendFirstEncounters initial.constants delta.constants
  adviceQueries :=
    appendFirstEncounters initial.adviceQueries delta.adviceQueries
  fixedQueries :=
    appendFirstEncounters initial.fixedQueries delta.fixedQueries
  instanceQueries :=
    appendFirstEncounters initial.instanceQueries delta.instanceQueries

theorem ConfigureDelta.mem_constants_apply
    (delta : ConfigureDelta F) (initial : ConstraintSystem F)
    (counts : ConfigureCounts) (column : Column .fixed) :
    column ∈ (delta.apply initial counts).constants ↔
      column ∈ initial.constants ∨ column ∈ delta.constants := by
  exact mem_appendFirstEncounters column initial.constants delta.constants

theorem ConfigureDelta.constants_nodup_apply
    (delta : ConfigureDelta F) (initial : ConstraintSystem F)
    (counts : ConfigureCounts) (hinitial : initial.constants.Nodup) :
    (delta.apply initial counts).constants.Nodup := by
  exact nodup_appendFirstEncounters initial.constants delta.constants hinitial

theorem ConfigureDelta.csDegree_apply
    (delta : ConfigureDelta F) (initial : ConstraintSystem F)
    (counts : ConfigureCounts) :
    csDegree (delta.apply initial counts) =
      max (csDegree initial) delta.constraintDegree := by
  simpa only [csDegree, ConfigureDelta.apply,
    ConfigureDelta.constraintDegree] using
    Halo2.constraintDegree_append initial.gates delta.gates
      initial.lookups delta.lookups


end Halo2
