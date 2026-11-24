import Clean.Halo2.ElaboratedConfigure
import Clean.Halo2.Expression.Checks

/-!
# midnight-zk configure constructs

Each construct records `ConfigureExtension` entries saying how midnight-zk compiles it, except an
accepted `with_selector` gate, which is a plain `createGate`. Additive gates, owned
`without_selector` gates and selected `batched_lookup`s then emit their shadows, ordinary Clean
gates and lookups, through the existing primitives, so query registration is that of `createGate`
and `lookup`: closure queries in call order, then table columns, as Rust's `VirtualCells` does.
`rows` gates and unstated lookups have no shadow: they register their queries and emit a handle
per selector they read, and `ConfigurationHolds` states them. `setMinimumDegree` and rejected
bodies emit only their entry. The entry list keeps program order across kinds, which the gate and
lookup lists lose. Existing programs call none of these, so their deltas and meaning are
unchanged; `Configure.Unextended` states that.

The `Closure` layer ports midnight-zk's `create_gate` and lookup closures. It runs the body,
picks the construct by evaluation, and records a `rejected` entry for a body it does not
compile: an empty or non-rectangular body, a query that is not a column query or that the
closure did not make, a selector inside a `with_selector` or additive body, a simple selector in
a lookup, an unselected or selector-reading `batched_lookup`, and a `batched_lookup_any` that
`batchedLookup` states per tuple.
-/

namespace Halo2

variable {F : Type}

/-! ## Existing deltas record no entries -/

@[simp] theorem ConfigureDelta.extensions_queriedCell (cell : Expression F Query) :
    (ConfigureDelta.queriedCell cell).extensions = [] := by
  cases cell with
  | var query => cases query <;> rfl
  | const => rfl
  | add => rfl
  | mul => rfl

@[simp] theorem ConfigureDelta.extensions_queriedCells (cells : List (Expression F Query)) :
    (ConfigureDelta.queriedCells cells).extensions = [] := by
  unfold ConfigureDelta.queriedCells
  suffices h : ∀ initial : ConfigureDelta F, initial.extensions = [] →
      (cells.foldl (fun delta cell => delta.append (.queriedCell cell)) initial).extensions =
        [] from
    h {} rfl
  induction cells with
  | nil => exact fun _ h => h
  | cons cell cells ih =>
    intro initial h
    rw [List.foldl_cons]
    apply ih
    simp [h]

@[simp] theorem ConfigureDelta.extensions_fixedQueriesOfColumns (columns : List TableColumn) :
    (ConfigureDelta.fixedQueriesOfColumns (F := F) columns).extensions = [] := by
  unfold ConfigureDelta.fixedQueriesOfColumns
  suffices h : ∀ initial : ConfigureDelta F, initial.extensions = [] →
      (columns.foldl (fun delta column =>
        delta.append { fixedQueries := [(column.inner, 0)] }) initial).extensions = [] from
    h {} rfl
  induction columns with
  | nil => exact fun _ h => h
  | cons column columns ih =>
    intro initial h
    rw [List.foldl_cons]
    apply ih
    simp [h]

/-- The program records no midnight-zk entry, so a zcash key of it is the key of all of it.
Derived like `ElaboratedConfigure`, from instances for the primitives and `bind`. -/
class Configure.Unextended {α : Type} (program : Configure F α) : Prop where
  extensions_eq_nil : ∀ counts, (program.delta counts).extensions = []

namespace Configure.Unextended

variable {α β : Type}

@[simp] theorem delta_extensions (program : Configure F α) [h : Unextended program]
    (counts : ConfigureCounts) : (program.delta counts).extensions = [] :=
  h.extensions_eq_nil counts

instance instPure (value : α) : Unextended (Pure.pure value : Configure F α) :=
  ⟨fun _ => rfl⟩

instance instBind (program : Configure F α) [Unextended program] (next : α → Configure F β)
    [∀ value, Unextended (next value)] : Unextended (program >>= next) :=
  ⟨fun counts => by simp [Configure.delta_bind]⟩

instance instAdviceColumn : Unextended (adviceColumn : Configure F (Column .advice)) :=
  ⟨fun _ => rfl⟩

instance instFixedColumn : Unextended (fixedColumn : Configure F (Column .fixed)) :=
  ⟨fun _ => rfl⟩

instance instInstanceColumn : Unextended (instanceColumn : Configure F (Column .instance)) :=
  ⟨fun _ => rfl⟩

instance instSelector : Unextended (selector : Configure F Selector) := ⟨fun _ => rfl⟩

instance instComplexSelector : Unextended (complexSelector : Configure F ComplexSelector) :=
  ⟨fun _ => rfl⟩

instance instLookupTableColumn : Unextended (lookupTableColumn : Configure F TableColumn) :=
  ⟨fun _ => rfl⟩

instance instEnableEquality (column : AnyColumn) :
    Unextended (enableEquality (F := F) column) :=
  ⟨fun _ => by
    rcases column with ⟨kind, index⟩
    cases kind <;> rfl⟩

instance instEnableConstant (column : Column .fixed) :
    Unextended (enableConstant (F := F) column) :=
  ⟨fun _ => rfl⟩

instance instCreateGate (gate : Gate F) : Unextended (createGate gate) :=
  ⟨fun _ => by simp [Configure.delta_createGate]⟩

instance instLookup (queriedCells : List (Expression F Query)) (masterSelector : ComplexSelector)
    (tableMap : List (Expression F Query × TableColumn))
    (hqueries : LookupQueriesDeclared queriedCells tableMap)
    (hnoSimpleSelectors : (tableMap.map Prod.fst).Forall Expression.NoSimpleSelectors) :
    Unextended (lookup queriedCells masterSelector tableMap hqueries hnoSimpleSelectors) :=
  ⟨fun _ => by simp [Configure.delta, Halo2.lookup]⟩

end Configure.Unextended

/-! ## Typed constructs -/

/-- Record how midnight-zk compiles what follows; position 0 is the next gate or lookup.
Private, so that an entry always describes the shadows its construct emits. -/
private def extend (entry : ConfigureExtension F) : Configure F Unit :=
  ⟨fun _ => ((), { extensions := [entry] }, {})⟩

/-- `extend` emits no gate, lookup, query or allocation: the `pure` metadata. -/
instance instElaboratedConfigureExtend (entry : ConfigureExtension F) :
    ElaboratedConfigure (extend entry) where
  constraintDegree _ := 3
  constraintDegree_eq := by
    intro counts
    rfl
  instanceQueries_eq := by
    intro counts
    rfl
  selectorSummary _ := {}
  selectorRequirements _ := True
  selectorsAllocated := by
    intro counts _
    show ({ extensions := [entry] } : ConfigureDelta F).SelectorsAllocated _
    constructor
    · simp
    · simp
    · simp [lookupInputSelectorBound]
  lookupSelectorsCompatible := by
    intro counts _
    show ({ extensions := [entry] } : ConfigureDelta F).LookupSelectorsCompatible
    simp [ConfigureDelta.LookupSelectorsCompatible, Halo2.LookupSelectorsCompatible]
  queryRequirements _ := True
  queriesLawful := by
    intro counts _
    show ({ extensions := [entry] } : ConfigureDelta F).QueriesLawful _
    constructor <;> simp

/-- Rust `Constraints::with_additive_selector(q, constraints)`, compiled as a trash argument.
The shadow is `Gate.withSelector` over the complex selector, the argument's per-row meaning. -/
def additiveGate [Field F] (name : String) (q : ComplexSelector)
    (queriedCells : List (Expression F Query))
    (constraints : List (String × Expression F Query))
    (hfree : ∀ constraint ∈ constraints, constraint.2.SelectorFree := by selector_free)
    (hqueries :
      queriedCells.Forall Expression.QueryAtom ∧
        constraints.Forall fun constraint =>
          constraint.2.QueriesDeclared queriedCells := by
      query_correct) :
    Configure F Unit := do
  extend (.gate { mode := .additive })
  createGate (Gate.withSelector name q queriedCells constraints hfree hqueries)

/-- A gate whose every polynomial has positive degree in `q` and no other selector, taken
verbatim: Rust's `Constraints::without_selector` over one owning selector. -/
def Gate.ofOwned (name : String) (q : Selector) (queriedCells : List (Expression F Query))
    (constraints : List (String × Expression F Query))
    (howned : constraints.all (·.2.ownedBy q) = true)
    (hqueries :
      queriedCells.Forall Expression.QueryAtom ∧
        constraints.Forall fun constraint =>
          constraint.2.QueriesDeclared queriedCells) :
    Gate F where
  name := name
  selector := q
  queriedCells := queriedCells
  constraints := constraints.map fun (name, p) => { name := name, poly := p }
  wellFormed := by
    have degree : ∀ c ∈ constraints, ∃ d, c.2.selectorDegree q = some (d + 1) :=
      fun c hc => Expression.exists_selectorDegree_of_ownedBy (List.all_eq_true.mp howned c hc)
    refine ⟨hqueries.1, ?_, ?_, ?_⟩
    · rw [List.forall_iff_forall_mem]
      intro c hc
      obtain ⟨c', hc', rfl⟩ := List.mem_map.mp hc
      exact (List.forall_iff_forall_mem.mp hqueries.2) c' hc'
    · rw [List.forall_iff_forall_mem]
      intro c hc
      obtain ⟨c', hc', rfl⟩ := List.mem_map.mp hc
      obtain ⟨d, hd⟩ := degree c' hc'
      exact Expression.selectorDegree_selectorsOwnedBy _ _ hd
    · intro _ c hc base scale hscale hzero
      obtain ⟨c', hc', rfl⟩ := List.mem_map.mp hc
      obtain ⟨d, hd⟩ := degree c' hc'
      rw [Expression.eval_scale _ _ hd] at hzero
      exact (mul_eq_zero.mp hzero).resolve_left (pow_ne_zero _ hscale)

/-- Rust `Constraints::without_selector` owned by `q`. The shadow is the gate itself. -/
def gateWithoutSelector (name : String) (q : Selector)
    (queriedCells : List (Expression F Query))
    (constraints : List (String × Expression F Query))
    (howned : constraints.all (·.2.ownedBy q) = true)
    (hqueries :
      queriedCells.Forall Expression.QueryAtom ∧
        constraints.Forall fun constraint =>
          constraint.2.QueriesDeclared queriedCells)
    (queriedSelectors : List Selector := []) :
    Configure F Unit := do
  extend (.gate { mode := .withoutSelector, queriedSelectors := queriedSelectors })
  createGate (Gate.ofOwned name q queriedCells constraints howned hqueries)

/-- The tuple width of a batch: Rust indexes the first column and asserts that every column
has its length (`logup.rs:296-303`). `none` for an empty batch or empty tuples. -/
def batchWidth {α : Type} : List (List (Expression F Query) × α) → Option ℕ
  | [] => none
  | (inputs, _) :: rest =>
      if inputs.length != 0 && rest.all (·.1.length == inputs.length) then
        some inputs.length
      else none

/-- Inputs Clean states as lookups: selector-free, over the closure's queries. -/
def batchInputsValid {α : Type} (queries : List Query)
    (columns : List (List (Expression F Query) × α)) : Bool :=
  columns.all fun column => column.1.all fun input => input.free && input.declared queries

/-- Tuple `j` of a width-major batch: each column's `j`-th input against its table. -/
def batchTuple (j : ℕ) (columns : List (List (Expression F Query) × TableColumn)) :
    List (Expression F Query × TableColumn) :=
  columns.filterMap fun column => column.1[j]?.map fun input => (input, column.2)

theorem mem_of_mem_batchTuple {j : ℕ}
    {columns : List (List (Expression F Query) × TableColumn)}
    {pair : Expression F Query × TableColumn} (h : pair ∈ batchTuple j columns) :
    ∃ column ∈ columns, pair.1 ∈ column.1 := by
  obtain ⟨column, hcolumn, hpair⟩ := List.mem_filterMap.mp h
  have hpair : column.1[j]?.map (fun input => (input, column.2)) = some pair := hpair
  cases hinput : column.1[j]? with
  | none =>
    rw [hinput] at hpair
    simp at hpair
  | some input =>
    rw [hinput] at hpair
    have hp : (input, column.2) = pair := Option.some.inj hpair
    subst hp
    exact ⟨column, hcolumn, List.mem_of_getElem? hinput⟩

theorem forall_batchTuple {P : Expression F Query → Prop} {j : ℕ}
    {columns : List (List (Expression F Query) × TableColumn)}
    (h : ∀ column ∈ columns, ∀ input ∈ column.1, P input) :
    ((batchTuple j columns).map Prod.fst).Forall P := by
  rw [List.forall_iff_forall_mem]
  intro input hinput
  obtain ⟨pair, hpair, rfl⟩ := List.mem_map.mp hinput
  obtain ⟨column, hcolumn, hmem⟩ := mem_of_mem_batchTuple hpair
  exact h column hcolumn pair.1 hmem

theorem forall_queryAtom_of_all {cells : List (Expression F Query)}
    (h : cells.all Expression.isQueryAtom = true) : cells.Forall Expression.QueryAtom :=
  List.forall_iff_forall_mem.mpr fun cell hcell =>
    Expression.queryAtom_of_isQueryAtom (List.all_eq_true.mp h cell hcell)

theorem batchInputsValid_spec {α : Type} {queries : List Query}
    {columns : List (List (Expression F Query) × α)}
    (h : batchInputsValid queries columns = true) :
    ∀ column ∈ columns, ∀ input ∈ column.1,
      input.free = true ∧ input.QueriesDeclared (queries.map (.var ·)) := by
  intro column hcolumn input hinput
  have hboth := Bool.and_eq_true_iff.mp
    (List.all_eq_true.mp (List.all_eq_true.mp h column hcolumn) input hinput)
  exact ⟨hboth.1, (Expression.declared_iff input queries).mp hboth.2⟩

theorem batchTuple_queriesDeclared {queries : List Query} {j : ℕ}
    {columns : List (List (Expression F Query) × TableColumn)}
    (hatoms : (queries.map (.var ·) : List (Expression F Query)).all Expression.isQueryAtom = true)
    (hinputs : batchInputsValid queries columns = true) :
    LookupQueriesDeclared (queries.map (.var ·)) (batchTuple j columns) :=
  ⟨forall_queryAtom_of_all hatoms,
    forall_batchTuple fun column hcolumn input hinput =>
      (batchInputsValid_spec hinputs column hcolumn input hinput).2⟩

theorem batchTuple_noSimpleSelectors {queries : List Query} {j : ℕ}
    {columns : List (List (Expression F Query) × TableColumn)}
    (hinputs : batchInputsValid queries columns = true) :
    ((batchTuple j columns).map Prod.fst).Forall Expression.NoSimpleSelectors :=
  forall_batchTuple fun column hcolumn input hinput =>
    Expression.free_noSimpleSelectors input
      (batchInputsValid_spec hinputs column hcolumn input hinput).1

/-- Rust `meta.batched_lookup(name, Some(q), |meta| columns)` (`logup.rs:176`): `queries` are the
closure's in call order and `columns` is width-major. The shadows are one Clean `lookup` per
tuple, sharing the closure's queries, so registration is Rust's: the first tuple's requests are
the only first encounters. -/
def batchedLookup (name : String) (q : ComplexSelector) (queries : List Query)
    (columns : List (List (Expression F Query) × TableColumn))
    (_hshape : (batchWidth columns).isSome = true)
    (hatoms : (queries.map (.var ·) : List (Expression F Query)).all Expression.isQueryAtom = true)
    (hinputs : batchInputsValid queries columns = true) : Configure F Unit := do
  let width := (batchWidth columns).getD 0
  let queriedCells : List (Expression F Query) := queries.map (.var ·)
  extend (.lookup
    { name := name
      selector := some q
      queriedCells := queriedCells
      columns := columns.map fun column => (column.1, queryFixed column.2.inner)
      shadows := width })
  for j in List.range width do
    lookup queriedCells q (batchTuple j columns) (batchTuple_queriesDeclared hatoms hinputs)
      (batchTuple_noSimpleSelectors hinputs)

/-- Rust `meta.set_minimum_degree(degree)`. -/
def setMinimumDegree (degree : ℕ) : Configure F Unit :=
  extend (.minimumDegree degree)

/-! ## Rows gates, unstated lookups and handles

These have no shadow that states them. Their entry carries the construct and
`ConfigurationHolds` gives its meaning. Each selector they read gets a *handle*, a
constraint-free gate on it, so that synthesis can enable the selector with `enableGate`. -/

/-- Register a closure's queries in call order, emitting nothing else. Selector queries
register nothing. -/
private def registerQueries (cells : List (Expression F Query)) : Configure F Unit :=
  ⟨fun _ => ((), ConfigureDelta.queriedCells cells, {})⟩

instance instElaboratedConfigureRegisterQueries (cells : List (Expression F Query)) :
    ElaboratedConfigure (registerQueries cells) where
  constraintDegree _ := 3
  constraintDegree_eq := by
    intro counts
    show (ConfigureDelta.queriedCells cells).constraintDegree = 3
    rw [ConfigureDelta.constraintDegree, ConfigureDelta.gates_queriedCells,
      ConfigureDelta.lookups_queriedCells]
    rfl
  instanceQueries _ := ConfigureDelta.instanceQueriesOfCells cells
  instanceQueries_eq := by
    intro counts
    exact ConfigureDelta.queriedCells_instanceQueries cells
  selectorsAllocated := by
    intro counts _
    show (ConfigureDelta.queriedCells cells).SelectorsAllocated _
    constructor
    · simp
    · simp
    · simp [lookupInputSelectorBound]
  lookupSelectorsCompatible := by
    intro counts _
    show (ConfigureDelta.queriedCells cells).LookupSelectorsCompatible
    simp [ConfigureDelta.LookupSelectorsCompatible, Halo2.LookupSelectorsCompatible]
  queryRequirements counts := cells.Forall (·.QueryAllocated counts)
  queriesLawful := by
    intro counts hcells
    exact ConfigureDelta.queriedCells_queriesLawful counts hcells

/-- The selectors `e` reads, in syntax order. -/
def Expression.selectorReads : Expression F Query → List Selector
  | .var (.selector s) => [s]
  | .var _ | .const _ => []
  | .add a b | .mul a b => a.selectorReads ++ b.selectorReads

/-- The selectors the expressions read, each once, in order of first read. -/
def selectorReads (expressions : List (Expression F Query)) : List Selector :=
  (expressions.flatMap Expression.selectorReads).eraseDups

/-- A constraint-free gate on `q`. Enabling it activates `q` and states nothing. -/
def Gate.handle (name : String) (q : Selector) (queriedCells : List (Expression F Query))
    (hcells : queriedCells.Forall Expression.QueryAtom) : Gate F where
  name := name
  selector := q
  queriedCells := queriedCells
  constraints := []
  wellFormed := ⟨hcells, trivial, trivial, by intro _ _ hc; simp at hc⟩

/-- A handle on `q`, which midnight-zk compiles to nothing. -/
def selectorHandle (name : String) (q : Selector) (queriedCells : List (Expression F Query))
    (hcells : queriedCells.Forall Expression.QueryAtom) : Configure F Unit := do
  extend (.gate { mode := .handle })
  createGate (Gate.handle name q queriedCells hcells)

/-- Rust `Constraints::without_selector` for a body no one selector owns: selector-free, or
over several selectors. Its handles carry the closure's queries, as Rust's gate does. -/
def rowsGate (name : String) (queriedCells : List (Expression F Query))
    (constraints : List (String × Expression F Query))
    (hcells : queriedCells.Forall Expression.QueryAtom)
    (queriedSelectors : List Selector := []) : Configure F Unit := do
  extend (.gate
    { mode := .rows
      name := name
      queriedCells := queriedCells
      queriedSelectors := queriedSelectors
      constraints := constraints.map fun (name, p) => { name := name, poly := p } })
  registerQueries queriedCells
  for q in selectorReads (constraints.map (·.2)) do
    selectorHandle name q queriedCells hcells

/-- Rust's lookup `selector`, `Constant(1)` for `None`. -/
def lookupSelectorExpr [Field F] : Option ComplexSelector → Expression F Query
  | some q => .var (.selector q.toSelector)
  | none => .const 1

def LookupExtension.selectorExpr [Field F] (entry : LookupExtension F) : Expression F Query :=
  lookupSelectorExpr entry.selector

/-- Handles on the selectors an unstated lookup reads. -/
def lookupHandles (name : String) : List Selector → Configure F Unit
  | [] => pure ()
  | s :: selectors => do
    selectorHandle name s [] trivial
    lookupHandles name selectors

/-- Rust `batched_lookup_any` with a batch no shadow states: unselected, reading selectors, or
over table expressions. `queries` are the closure's, selectors included, in call order. -/
def unstatedLookup [Field F] (name : String) (q : Option ComplexSelector) (queries : List Query)
    (columns : List (List (Expression F Query) × Expression F Query)) : Configure F Unit := do
  extend (.lookup
    { name := name
      any := true
      selector := q
      queriedCells := queries.map (.var ·)
      columns := columns })
  registerQueries (queries.map (.var ·))
  lookupHandles name
    (selectorReads (lookupSelectorExpr q :: columns.flatMap fun c => c.1 ++ [c.2]))

/-! ## Closures -/

/-- Rust's `VirtualCells`: a closure's queries in call order. -/
abbrev VirtualCells := StateM (Array Query)

namespace VirtualCells

private def query (q : Query) : VirtualCells (Expression F Query) := do
  modify (·.push q)
  return .var q

/-- Rust `meta.query_advice(column, rotation)`. -/
def queryAdvice (column : Column .advice) (rotation : Rotation := 0) :
    VirtualCells (Expression F Query) :=
  query (.advice column rotation)

/-- Rust `meta.query_fixed(column, rotation)`. -/
def queryFixed (column : Column .fixed) (rotation : Rotation := 0) :
    VirtualCells (Expression F Query) :=
  query (.fixed column rotation)

/-- Rust `meta.query_instance(column, rotation)`. -/
def queryInstance (column : Column .instance) (rotation : Rotation := 0) :
    VirtualCells (Expression F Query) :=
  query (.instance column rotation)

/-- Rust `meta.query_selector(q)`. Gates keep it apart from their column queries, as Rust's
`queried_selectors`; lookups record it among their queries. -/
def querySelector (q : Selector) : VirtualCells (Expression F Query) :=
  query (.selector q)

/-- Run a closure: its result and its queries in call order. -/
def record {α : Type} (body : VirtualCells α) : α × List Query :=
  let (result, calls) := Id.run (StateT.run body #[])
  (result, calls.toList)

end VirtualCells

private def reject (message : String) : Configure F Unit :=
  extend (.rejected message)

private theorem all_free {constraints : List (String × Expression F Query)}
    (h : constraints.all (·.2.free) = true) :
    ∀ constraint ∈ constraints, constraint.2.SelectorFree :=
  fun constraint hconstraint =>
    (Expression.free_iff constraint.2).mp (List.all_eq_true.mp h constraint hconstraint)

private theorem all_declared {constraints : List (String × Expression F Query)}
    {calls : List Query} (h : constraints.all (·.2.declared calls) = true) :
    constraints.Forall fun constraint =>
      constraint.2.QueriesDeclared (calls.map (.var ·)) :=
  List.forall_iff_forall_mem.mpr fun constraint hconstraint =>
    (Expression.declared_iff constraint.2 calls).mp (List.all_eq_true.mp h constraint hconstraint)

/-- The first selector atom, in syntax order. -/
private def firstSelector : Expression F Query → Option Selector
  | .var (.selector s) => some s
  | .var _ | .const _ => none
  | .add a b | .mul a b =>
      match firstSelector a with
      | some s => some s
      | none => firstSelector b

namespace Closure

private def emptyBody (name : String) : String :=
  s!"gate {name}: expected a nonempty constraint body"

private def undeclared (name : String) : String :=
  s!"gate {name}: a polynomial uses a query its closure did not make"

/-- `meta.create_gate(name, |meta| Constraints::with_selector(q, body))`. -/
def gate [Field F] (name : String) (q : Selector)
    (body : VirtualCells (List (String × Expression F Query))) : Configure F Unit :=
  let (constraints, calls) := VirtualCells.record body
  let cells : List (Expression F Query) := calls.map (.var ·)
  if constraints.isEmpty then reject (emptyBody name) else
  if hfree : constraints.all (·.2.free) = true then
    if hatoms : cells.all Expression.isQueryAtom = true then
      if hdeclared : constraints.all (·.2.declared calls) = true then
        createGate (Gate.withSelector name q cells constraints (all_free hfree)
          ⟨forall_queryAtom_of_all hatoms, all_declared hdeclared⟩)
      else reject (undeclared name)
    else reject s!"gate {name}: a query that is not a column query"
  else reject s!"gate {name}: a selector inside a with_selector body"

/-- `meta.create_gate(name, |meta| Constraints::with_additive_selector(q, body))`. -/
def additiveGate [Field F] (name : String) (q : ComplexSelector)
    (body : VirtualCells (List (String × Expression F Query))) : Configure F Unit :=
  let (constraints, calls) := VirtualCells.record body
  let cells : List (Expression F Query) := calls.map (.var ·)
  if constraints.isEmpty then reject (emptyBody name) else
  if hfree : constraints.all (·.2.free) = true then
    if hatoms : cells.all Expression.isQueryAtom = true then
      if hdeclared : constraints.all (·.2.declared calls) = true then
        Halo2.additiveGate name q cells constraints (all_free hfree)
          ⟨forall_queryAtom_of_all hatoms, all_declared hdeclared⟩
      else reject (undeclared name)
    else reject s!"gate {name}: a query that is not a column query"
  else reject s!"gate {name}: a selector inside an additive body"

/-- `meta.create_gate(name, |meta| Constraints::without_selector(body))`: owned by its first
selector when every polynomial is, else a `rows` gate. -/
def gateWithoutSelector (name : String)
    (body : VirtualCells (List (String × Expression F Query))) : Configure F Unit :=
  let (constraints, calls) := VirtualCells.record body
  let columns := calls.filter fun | .selector _ => false | _ => true
  let selectors := calls.filterMap fun | .selector s => some s | _ => none
  let cells : List (Expression F Query) := columns.map (.var ·)
  if constraints.isEmpty then reject (emptyBody name) else
  if hatoms : cells.all Expression.isQueryAtom = true then
    if hdeclared : constraints.all (·.2.declared columns) = true then
      match constraints.findSome? (firstSelector ·.2) with
      | none => rowsGate name cells constraints (forall_queryAtom_of_all hatoms) selectors
      | some q =>
        if howned : constraints.all (·.2.ownedBy q) = true then
          Halo2.gateWithoutSelector name q cells constraints howned
            ⟨forall_queryAtom_of_all hatoms, all_declared hdeclared⟩ selectors
        else rowsGate name cells constraints (forall_queryAtom_of_all hatoms) selectors
    else reject (undeclared name)
  else reject s!"gate {name}: a query that is not a column query"

/-- `meta.batched_lookup(name, q, |meta| columns)`, with `columns` width-major. Only selected
batches with selector-free inputs are stated by Clean yet. -/
def batchedLookup (name : String) (q : Option ComplexSelector)
    (body : VirtualCells (List (List (Expression F Query) × TableColumn))) : Configure F Unit :=
  let (columns, calls) := VirtualCells.record body
  match q with
  | none => reject s!"lookup {name}: an unselected batch is not stated by Clean yet"
  | some q =>
    if hshape : (batchWidth columns).isSome = true then
      if hatoms : (calls.map (.var ·) : List (Expression F Query)).all
          Expression.isQueryAtom = true then
        if hinputs : batchInputsValid calls columns = true then
          Halo2.batchedLookup name q calls columns hshape hatoms hinputs
        else reject s!"lookup {name}: inputs must be selector-free over the closure's queries"
      else reject s!"lookup {name}: a query that is not a column query"
    else reject s!"lookup {name}: expected a nonempty rectangular batch"

/-- A batch midnight-zk states per tuple: selected, selector-free, over bare fixed columns. -/
private def anyOwned (q : Option ComplexSelector)
    (columns : List (List (Expression F Query) × Expression F Query)) : Bool :=
  q.isSome && columns.all fun column =>
    column.1.all (·.free) && match column.2 with
      | .var (.fixed _ rotation) => rotation == 0
      | _ => false

/-- `meta.batched_lookup_any(name, q, |meta| columns)`, with `columns` width-major. A batch
midnight-zk states per tuple is refused: write it as `batchedLookup`. So is a simple selector on
either side, as Rust refuses it (circuit.rs:1761). -/
def batchedLookupAny [Field F] (name : String) (q : Option ComplexSelector)
    (body : VirtualCells (List (List (Expression F Query) × Expression F Query))) :
    Configure F Unit :=
  let (columns, calls) := VirtualCells.record body
  if (batchWidth columns).isSome then
    if !columns.all (fun column => column.1.all (·.noSimple) && column.2.noSimple) then
      reject s!"lookup {name}: a simple selector in a lookup expression"
    else if columns.all fun column => column.1.all (·.declared calls) && column.2.declared calls
    then
      if anyOwned q columns then
        reject s!"lookup {name}: a batched_lookup_any over fixed columns; use batchedLookup"
      else unstatedLookup name q calls columns
    else reject s!"lookup {name}: a polynomial uses a query its closure did not make"
  else reject s!"lookup {name}: expected a nonempty rectangular batch"

/-- `meta.lookup_any(name, q, |meta| pairs)`: a batch of one tuple. -/
def lookupAny [Field F] (name : String) (q : Option ComplexSelector)
    (body : VirtualCells (List (Expression F Query × Expression F Query))) : Configure F Unit :=
  batchedLookupAny name q ((·.map fun (x, t) => ([x], t)) <$> body)

end Closure

/-! ## Elaborated metadata

Instances for the constructs, the conditionals their closures decide and `for` over a list, so a
program written with them gets its `ElaboratedConfigure` from `infer_instance`. The conditional
and loop instances are scoped, so existing clients' instance search is unchanged; open
`Halo2.ElaboratedConfigure` to use them. -/

namespace ElaboratedConfigure

variable {α β : Type}

scoped instance instDite (c : Prop) [h : Decidable c] (t : c → Configure F α)
    (e : ¬c → Configure F α)
    [∀ hc, ElaboratedConfigure (t hc)] [∀ hc, ElaboratedConfigure (e hc)] :
    ElaboratedConfigure (dite c t e) :=
  match h with
  | isTrue hc => inferInstanceAs (ElaboratedConfigure (t hc))
  | isFalse hc => inferInstanceAs (ElaboratedConfigure (e hc))

scoped instance instIte (c : Prop) [h : Decidable c] (t e : Configure F α)
    [ElaboratedConfigure t] [ElaboratedConfigure e] : ElaboratedConfigure (ite c t e) :=
  match h with
  | isTrue _ => inferInstanceAs (ElaboratedConfigure t)
  | isFalse _ => inferInstanceAs (ElaboratedConfigure e)

/-- `for i in l do body`, by recursion on `l`. -/
@[reducible] def forInList {ι : Type} (f : ι → β → Configure F (ForInStep β))
    [∀ i b, ElaboratedConfigure (f i b)] :
    (l : List ι) → (init : β) → ElaboratedConfigure (forIn l init f)
  | [], init => by
    rw [List.forIn_nil]
    exact ElaboratedConfigure.pure init
  | i :: l, init => by
    rw [List.forIn_cons]
    refine @ElaboratedConfigure.bind F _ _ (f i init) inferInstance _ ?_
    intro step
    cases step with
    | done b => exact ElaboratedConfigure.pure b
    | yield b => exact forInList f l b

scoped instance instForInList {ι : Type} (l : List ι) (init : β)
    (f : ι → β → Configure F (ForInStep β)) [∀ i b, ElaboratedConfigure (f i b)] :
    ElaboratedConfigure (forIn l init f) :=
  forInList f l init

instance instExtendReject (message : String) : ElaboratedConfigure (reject (F := F) message) :=
  instElaboratedConfigureExtend _

instance instAdditiveGate [Field F] (name : String) (q : ComplexSelector)
    (queriedCells : List (Expression F Query))
    (constraints : List (String × Expression F Query)) (hfree) (hqueries) :
    ElaboratedConfigure (additiveGate name q queriedCells constraints hfree hqueries) := by
  unfold additiveGate
  infer_instance

instance instGateWithoutSelector (name : String) (q : Selector)
    (queriedCells : List (Expression F Query))
    (constraints : List (String × Expression F Query)) (howned) (hqueries)
    (queriedSelectors : List Selector) :
    ElaboratedConfigure
      (gateWithoutSelector name q queriedCells constraints howned hqueries queriedSelectors) := by
  unfold gateWithoutSelector
  infer_instance

instance instBatchedLookup (name : String) (q : ComplexSelector) (queries : List Query)
    (columns : List (List (Expression F Query) × TableColumn)) (hshape) (hatoms) (hinputs) :
    ElaboratedConfigure (batchedLookup name q queries columns hshape hatoms hinputs) := by
  unfold batchedLookup
  dsimp only
  infer_instance

instance instSetMinimumDegree (degree : ℕ) :
    ElaboratedConfigure (setMinimumDegree (F := F) degree) := by
  unfold setMinimumDegree
  infer_instance

instance instClosureGate [Field F] (name : String) (q : Selector)
    (body : VirtualCells (List (String × Expression F Query))) :
    ElaboratedConfigure (Closure.gate name q body) := by
  unfold Closure.gate
  cases VirtualCells.record body
  dsimp only
  infer_instance

instance instClosureAdditiveGate [Field F] (name : String) (q : ComplexSelector)
    (body : VirtualCells (List (String × Expression F Query))) :
    ElaboratedConfigure (Closure.additiveGate name q body) := by
  unfold Closure.additiveGate
  cases VirtualCells.record body
  dsimp only
  infer_instance

instance instSelectorHandle (name : String) (q : Selector)
    (queriedCells : List (Expression F Query)) (hcells) :
    ElaboratedConfigure (selectorHandle name q queriedCells hcells) := by
  unfold selectorHandle
  infer_instance

instance instRowsGate (name : String) (queriedCells : List (Expression F Query))
    (constraints : List (String × Expression F Query)) (hcells)
    (queriedSelectors : List Selector) :
    ElaboratedConfigure (rowsGate name queriedCells constraints hcells queriedSelectors) := by
  unfold rowsGate
  infer_instance

instance instLookupHandles (name : String) :
    (selectors : List Selector) → ElaboratedConfigure (lookupHandles (F := F) name selectors)
  | [] => ElaboratedConfigure.pure ()
  | s :: selectors =>
    @ElaboratedConfigure.bind F _ _ (selectorHandle name s [] trivial)
      (instSelectorHandle name s [] trivial) _
      fun _ => instLookupHandles name selectors

instance instUnstatedLookup [Field F] (name : String) (q : Option ComplexSelector)
    (queries : List Query) (columns : List (List (Expression F Query) × Expression F Query)) :
    ElaboratedConfigure (unstatedLookup name q queries columns) := by
  unfold unstatedLookup
  infer_instance

instance instClosureGateWithoutSelector (name : String)
    (body : VirtualCells (List (String × Expression F Query))) :
    ElaboratedConfigure (Closure.gateWithoutSelector name body) := by
  unfold Closure.gateWithoutSelector
  cases VirtualCells.record body with
  | mk constraints calls =>
    dsimp only
    cases constraints.findSome? (firstSelector ·.2) <;> (try dsimp only) <;> infer_instance

instance instClosureBatchedLookupAny [Field F] (name : String) (q : Option ComplexSelector)
    (body : VirtualCells (List (List (Expression F Query) × Expression F Query))) :
    ElaboratedConfigure (Closure.batchedLookupAny name q body) := by
  unfold Closure.batchedLookupAny
  cases VirtualCells.record body
  dsimp only
  infer_instance

instance instClosureLookupAny [Field F] (name : String) (q : Option ComplexSelector)
    (body : VirtualCells (List (Expression F Query × Expression F Query))) :
    ElaboratedConfigure (Closure.lookupAny name q body) := by
  unfold Closure.lookupAny
  infer_instance

instance instClosureBatchedLookup (name : String) (q : Option ComplexSelector)
    (body : VirtualCells (List (List (Expression F Query) × TableColumn))) :
    ElaboratedConfigure (Closure.batchedLookup name q body) := by
  unfold Closure.batchedLookup
  cases VirtualCells.record body
  cases q <;> (try dsimp only) <;> infer_instance

end ElaboratedConfigure

end Halo2
