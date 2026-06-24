import Clean.Air.Circuit

namespace Air.Flat
variable {F : Type} [Field F]
variable {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]

/--
A flat AIR component: one circuit whose constraints are checked independently on each row.
There are no direct adjacent-row constraints; communication with other rows/components is
expressed by channel interactions.
-/
structure Component (F : Type) [Field F] where
  {Input : TypeMap} {Output : TypeMap}
  [provableInput : ProvableType Input] [provableOutput : ProvableType Output]
  circuit : GeneralFormalCircuit F Input Output

instance (t: Component F) : ProvableType t.Input := t.provableInput
instance (t: Component F) : ProvableType t.Output := t.provableOutput

namespace Component
def operations (component : Component F) : Operations F :=
  component.circuit.instantiate.operations 0

def width (component : Component F) : ℕ := component.circuit.size

@[circuit_norm]
abbrev rowOffset (component : Component F) : ℕ := size component.Input
@[circuit_norm]
abbrev rowInputVar (component : Component F): Var component.Input F :=
  varFromOffset component.Input 0

/-- first `size Input` elements of the environment are the input -/
@[circuit_norm]
def rowInput (component : Component F) (row : Environment F) : component.Input F :=
  valueFromOffset component.Input 0 row

/-- output is whatever the circuit computes on the row input -/
@[circuit_norm]
def rowOutput (component : Component F) (row : Environment F) : component.Output F :=
  let outputVar := (component.circuit component.rowInputVar).output component.rowOffset
  eval row outputVar

@[circuit_norm]
def rowOperations (component : Component F) : Operations F :=
  component.circuit.main (varFromOffset component.Input 0) |>.operations (size component.Input)

def Spec (component : Component F) (row : Environment F) : Prop :=
  component.circuit.Spec (component.rowInput row) (component.rowOutput row) row.data

def Assumptions (component : Component F) (row : Environment F) : Prop :=
  component.circuit.Assumptions (component.rowInput row) row.data

abbrev exposedChannels (component : Component F) : List (ExposedChannel F) :=
  component.circuit.exposedChannels component.rowInputVar component.rowOffset

variable {component : Component F} {env : Environment F}

lemma constraints_eq : component.operations.constraints = component.rowOperations.constraints := by
  simp only [circuit_norm, witnessAny, GeneralFormalCircuit.instantiate, Component.operations,
    GeneralFormalCircuit.toSubcircuit, GeneralFormalCircuit.toWithHint,
    GeneralFormalCircuit.WithHint.toSubcircuit, Operations.toNested_toFlat]

lemma lookups_eq : component.operations.lookups = component.rowOperations.lookups := by
  simp only [circuit_norm, witnessAny, GeneralFormalCircuit.instantiate, Component.operations,
    GeneralFormalCircuit.toSubcircuit, GeneralFormalCircuit.toWithHint,
    GeneralFormalCircuit.WithHint.toSubcircuit, Operations.toNested_toFlat]

lemma interactions_eq : component.operations.interactions = component.rowOperations.interactions := by
  simp only [circuit_norm, witnessAny, GeneralFormalCircuit.instantiate, Component.operations,
    GeneralFormalCircuit.toSubcircuit, GeneralFormalCircuit.toWithHint,
    GeneralFormalCircuit.WithHint.toSubcircuit, Operations.toNested_toFlat]

lemma interactionsWith_eq {channel : RawChannel F} :
    component.operations.interactionsWith channel = component.rowOperations.interactionsWith channel := by
  simp only [Operations.interactionsWith, interactions_eq]

lemma interactionsValues_eq : component.operations.interactionValues env = component.rowOperations.interactionValues env := by
  simp only [Operations.interactionValues, interactions_eq]

lemma interactionsWith_of_exposedChannels {table : Component F} {channel : RawChannel F}
  {interactions : List (AbstractInteraction F)}
  (h_exposed : ⟨ channel, interactions ⟩ ∈ table.exposedChannels) :
    table.operations.interactionsWith channel = interactions := by
  rw [Component.interactionsWith_eq]
  simp only [circuit_norm, Component.exposedChannels] at *
  convert table.circuit.interactionsWith_eq_of_mem_exposedChannels _ _ _ h_exposed

lemma constraintsHold_iff (env : Environment F) :
    component.operations.ConstraintsHold env ↔ component.rowOperations.ConstraintsHold env := by
  simp only [circuit_norm, lookups_eq, constraints_eq]

lemma guarantees_iff (env : Environment F) :
    component.operations.FullGuarantees env ↔ component.rowOperations.FullGuarantees env := by
  simp only [circuit_norm, interactions_eq]

lemma requirements_iff (env : Environment F) :
    component.operations.FullRequirements env ↔ component.rowOperations.FullRequirements env := by
  simp only [circuit_norm, interactions_eq]

lemma channelGuarantees_iff (env : Environment F) (channel : RawChannel F) :
    component.operations.ChannelGuarantees channel env ↔ component.rowOperations.ChannelGuarantees channel env := by
  simp only [circuit_norm, interactions_eq]

lemma channelRequirements_iff (env : Environment F) (channel : RawChannel F) :
    component.operations.ChannelRequirements channel env ↔ component.rowOperations.ChannelRequirements channel env := by
  simp only [circuit_norm, interactions_eq]

lemma inChannelsOrRequirements_of_constraints (env : Environment F) :
    component.operations.ConstraintsHold env →
    component.operations.InChannelsOrRequirementsFull component.circuit.channelsWithRequirements env := by
  rw [constraintsHold_iff]
  intro h_constraints
  simp only [circuit_norm, interactions_eq]
  exact component.circuit.in_channels_or_requirements_full_of_constraints h_constraints

lemma inChannelsOrGuarantees (env : Environment F) :
    component.operations.InChannelsOrGuaranteesFull component.circuit.channelsWithGuarantees env := by
  have h := component.circuit.in_channels_or_guarantees_full
  simp only [circuit_norm, interactions_eq] at *
  convert h _ _ env

-- this is the circuit's soundness theorem, stated in "instantiated" form
theorem weakSoundness {component : Component F} {env : Environment F} :
    component.Assumptions env →
    component.operations.ConstraintsHold env →
    component.operations.FullGuarantees env →
      component.Spec env ∧ component.operations.FullRequirements env := by
  simp only [constraintsHold_iff, guarantees_iff, requirements_iff, rowOperations, Spec]
  intro h_assumptions h_constraints h_guarantees
  set inputVar := varFromOffset component.Input 0
  set ops := (component.circuit.main inputVar).operations (size component.Input)
  have h_assumptions' : component.circuit.Assumptions (eval env inputVar) env.data := by
    simpa only [Assumptions, rowInput, inputVar, eval_varFromOffset_valueFromOffset] using h_assumptions
  convert component.circuit.original_full_soundness _ _ _ h_assumptions' h_constraints h_guarantees
  simp only [rowInput, inputVar, eval_varFromOffset_valueFromOffset]
end Component

/-- Concrete rows and prover data for one flat AIR component. -/
structure Table (F : Type) [Field F] where
  component : Component F
  width : ℕ
  table : List (Array F)
  data : ProverData F
  uniform_width : ∀ row ∈ table, row.size = width

namespace Table
variable {table : Table F} {channel : RawChannel F}

abbrev length (t : Table F) : ℕ := t.table.length

def environment (table : Table F) (row : Array F) :=
  Environment.fromArray row table.data

theorem ext_iff {table1 table2 : Table F} :
    table1 = table2 ↔
    table1.component = table2.component ∧
    table1.width = table2.width ∧
    table1.table = table2.table ∧
    table1.data = table2.data := by
  cases table1
  cases table2
  simp only [mk.injEq]

@[circuit_norm]
def channelsWithGuarantees (table : Table F) : List (RawChannel F) :=
  table.component.circuit.channelsWithGuarantees

@[circuit_norm]
def channelsWithRequirements (table : Table F) : List (RawChannel F) :=
  table.component.circuit.channelsWithRequirements

def Constraints (table : Table F) : Prop :=
  ∀ row ∈ table.table,
    table.component.operations.ConstraintsHold (table.environment row)

def Assumptions (table : Table F) : Prop :=
  ∀ row ∈ table.table,
    table.component.Assumptions (table.environment row)

def Guarantees (table : Table F) : Prop :=
  ∀ row ∈ table.table,
    table.component.operations.FullGuarantees (table.environment row)

def ChannelGuarantees (table : Table F) (channel : RawChannel F) : Prop :=
  ∀ row ∈ table.table,
    table.component.operations.ChannelGuarantees channel (table.environment row)

def InChannelsOrGuarantees (table : Table F) (channels : List (RawChannel F)) : Prop :=
  ∀ row ∈ table.table,
    table.component.operations.InChannelsOrGuaranteesFull channels (table.environment row)

def Requirements (table : Table F) : Prop :=
  ∀ row ∈ table.table,
    table.component.operations.FullRequirements (table.environment row)

def ChannelRequirements (table : Table F) (channel : RawChannel F) : Prop :=
  ∀ row ∈ table.table,
    table.component.operations.ChannelRequirements channel (table.environment row)

def InChannelsOrRequirements (table : Table F) (channels : List (RawChannel F)) : Prop :=
  ∀ row ∈ table.table,
    table.component.operations.InChannelsOrRequirementsFull channels (table.environment row)

def Spec (table : Table F) : Prop :=
  ∀ row ∈ table.table,
    table.component.Spec (table.environment row)

def interactions (table : Table F) : List (Interaction F) :=
  table.table.flatMap fun row =>
    table.component.operations.interactionValues (table.environment row)

noncomputable def interactionsWith (table : Table F) (channel : RawChannel F) : List (Interaction F) :=
  table.table.flatMap fun row =>
    table.component.operations.interactionValuesWith channel (table.environment row)

open Classical in lemma interactionsWith_eq_filter :
    table.interactionsWith channel = table.interactions.filter (·.channel = channel) := by
  simp only [interactionsWith, interactions, List.filter_flatMap]
  congr
  funext row
  rw [Operations.interactionValuesWith_eq_filter]

noncomputable def interactionssWith (table : Table F)
    (channel : RawChannel F) : List (List (Interaction F)) :=
  table.table.map fun row =>
    table.component.operations.interactionValuesWith channel (table.environment row)

lemma channel_eq_of_mem_interactionsWith {i : Interaction F} :
    i ∈ table.interactionsWith channel → i.channel = channel := by
  intro h_mem
  simp only [interactionsWith, List.mem_flatMap] at h_mem
  rcases h_mem with ⟨row, h_row, hi⟩
  simp only [Operations.interactionValuesWith, List.mem_map] at hi
  rcases hi with ⟨i_abs, hi_abs, heq⟩
  rw [←heq]
  apply Operations.channel_eq_of_mem_interactionsWith hi_abs

lemma forall_interactions_iff (table : Table F) (motive : Interaction F → Prop) :
    (∀ i ∈ table.interactions, motive i) ↔
    ∀ row ∈ table.table, ∀ i ∈ table.component.operations.interactions,
      motive (i.eval (table.environment row)) := by
  simp only [interactions, Operations.interactionValues, List.mem_flatMap, List.mem_map,
    forall_exists_index, and_imp]
  constructor
  · intro h row h_row i hi
    set env := table.environment row
    exact h (i.eval env) row h_row i hi rfl
  · intro h i row h_row i' hi' h_eq
    rw [← h_eq]
    exact h row h_row i' hi'

lemma forall_interactionsWith_iff (table : Table F) (channel : RawChannel F)
  (motive : Interaction F → Prop) :
    (∀ i ∈ table.interactionsWith channel, motive i) ↔
    ∀ row ∈ table.table, ∀ i ∈ table.component.operations.interactions,
      (i.channel = channel → motive (i.eval (table.environment row))) := by
  simp only [interactionsWith, List.mem_flatMap, List.mem_map,
    forall_exists_index, and_imp, circuit_norm]
  constructor
  · intro h row h_row i hi h_channel
    set env := table.environment row
    exact h (i.eval env) row h_row i hi h_channel rfl
  · intro h i row h_row i' hi' h_channel h_eq
    rw [← h_eq]
    exact h row h_row i' hi' h_channel

lemma interactionsWith_nil_of_channel_not_mem :
    channel ∉ table.component.circuit.channels → table.interactionsWith channel = [] := by
  contrapose!
  simp only [AbstractInteraction.eval_channel, interactionsWith_eq_filter, ne_eq, List.filter_eq_nil_iff,
    decide_eq_true_eq, forall_interactions_iff, not_forall, not_not, forall_exists_index]
  intro component table_mem i i_mem channel_eq
  symm at channel_eq; subst channel_eq
  simp only [Component.interactions_eq] at i_mem
  have h_subset := table.component.circuit.channels_subset table.component.rowInputVar
    table.component.rowOffset
  apply h_subset
  simp only [Operations.channels, List.mem_map]
  exists i

lemma guarantees_iff_forall (table : Table F) :
    table.Guarantees ↔
    ∀ i ∈ table.interactions, i.Guarantees table.data := by
  simp only [Table.Guarantees, circuit_norm, forall_interactions_iff]
  rfl

lemma channelGuarantees_iff_forall (table : Table F) (channel : RawChannel F) :
    table.ChannelGuarantees channel ↔
    ∀ i ∈ table.interactionsWith channel, i.Guarantees table.data := by
  simp only [Table.ChannelGuarantees, circuit_norm, forall_interactionsWith_iff]
  rfl

lemma guarantees_iff_channelGuarantees (table : Table F) :
    table.Guarantees ↔
    ∀ channel ∈ table.channelsWithGuarantees, table.ChannelGuarantees channel := by
  simp only [Table.Guarantees, Table.ChannelGuarantees, channelsWithGuarantees]
  simp only [Component.guarantees_iff, Component.channelGuarantees_iff, Component.rowOperations]
  simp only [GeneralFormalCircuit.guarantees_iff]
  constructor <;> simp_all

lemma channelGuarantees_of_requirements (table : Table F) {channel : RawChannel F} :
    table.Guarantees → table.ChannelGuarantees channel := by
  simp_all [Table.Guarantees, Table.ChannelGuarantees, circuit_norm]

lemma requirements_iff_forall (table : Table F) :
    table.Requirements ↔
    ∀ i ∈ table.interactions, i.Requirements table.data := by
  simp only [Table.Requirements, circuit_norm, forall_interactions_iff]
  rfl

lemma channelRequirements_iff_forall (table : Table F) (channel : RawChannel F) :
    table.ChannelRequirements channel ↔
    ∀ i ∈ table.interactionsWith channel, i.Requirements table.data := by
  simp only [Table.ChannelRequirements, circuit_norm, forall_interactionsWith_iff]
  rfl

lemma requirements_iff_channelRequirements_of_constraints (table : Table F) :
    table.Constraints →
    (table.Requirements ↔
    ∀ channel ∈ table.channelsWithRequirements, table.ChannelRequirements channel) := by
  intro h_constraints
  simp only [Table.Requirements, Table.ChannelRequirements, channelsWithRequirements]
  simp only [Component.requirements_iff, Component.channelRequirements_iff, Component.rowOperations]
  simp_rw [Table.Constraints, table.component.constraintsHold_iff] at h_constraints
  constructor
  · intro h_reqs channel h_channel row h_row
    specialize h_reqs row h_row
    rw [table.component.circuit.requirements_iff_of_constraints (h_constraints row h_row)] at h_reqs
    exact h_reqs channel h_channel
  · intro h_reqs row h_row
    rw [table.component.circuit.requirements_iff_of_constraints (h_constraints row h_row)]
    intro channel h_channel
    exact h_reqs channel h_channel row h_row

lemma channelRequirements_of_requirements (table : Table F) {channel : RawChannel F} :
    table.Requirements → table.ChannelRequirements channel := by
  simp_all [Table.Requirements, Table.ChannelRequirements, circuit_norm]

lemma inChannelsOrRequirements_of_constraints (table : Table F) :
    table.Constraints →
    table.InChannelsOrRequirements table.channelsWithRequirements := by
  intro h_constraints
  simp only [InChannelsOrRequirements, channelsWithRequirements]
  intro row h_row
  exact table.component.inChannelsOrRequirements_of_constraints
    (table.environment row) (h_constraints row h_row)

lemma requirements_of_not_mem_of_constraints (table : Table F) {channel : RawChannel F} :
    table.Constraints →
    channel ∉ table.channelsWithRequirements → table.ChannelRequirements channel := by
  intro h_constraints h_not_mem
  have h_in_or_req := table.inChannelsOrRequirements_of_constraints h_constraints
  simp only [ChannelRequirements, InChannelsOrRequirements] at *
  intro row h_row
  specialize h_in_or_req row h_row
  apply Operations.requirements_of_not_mem _ table.channelsWithRequirements
  assumption
  assumption

lemma inChannelsOrGuarantees (table : Table F) :
    table.InChannelsOrGuarantees table.channelsWithGuarantees := by
  simp [InChannelsOrGuarantees, channelsWithGuarantees, Component.inChannelsOrGuarantees]

lemma guarantees_of_not_mem (table : Table F) {channel : RawChannel F} :
    channel ∉ table.channelsWithGuarantees → table.ChannelGuarantees channel := by
  intro h_not_mem
  have h_in_or_guar := table.inChannelsOrGuarantees
  simp only [ChannelGuarantees, InChannelsOrGuarantees] at *
  intro row h_row
  specialize h_in_or_guar row h_row
  apply Operations.guarantees_of_not_mem _ table.channelsWithGuarantees
  assumption
  assumption

/-- Circuit soundness, lifted to full table level. -/
theorem weakSoundness {table : Table F} :
    table.Assumptions → table.Constraints → table.Guarantees →
    table.Spec ∧ table.Requirements := by
  simp_all [Table.Constraints, Table.Guarantees, Table.Spec,
    Table.Requirements, Table.Assumptions, Component.weakSoundness]

/--
If we know constraints and _some_ of the guarantees unconditionally, we can remove them from the per-row assumptions.

This lemma is tailored to VM-like channels where there remains a single channel that we need to
prove guarantees for.
-/
lemma requirements_of_partial_guarantees_of_constraints {table : Table F}
  {finished : List (RawChannel F)} {unfinished : RawChannel F} :
  table.Assumptions →
  table.Constraints →
  table.channelsWithGuarantees ⊆ unfinished :: finished →
  (∀ channel ∈ finished, table.ChannelGuarantees channel) →
    ∀ row ∈ table.table,
      table.component.operations.ChannelGuarantees unfinished (table.environment row) →
      table.component.operations.ChannelRequirements unfinished (table.environment row) := by
  intro assumptions constraints subset finished_grts row h_row channel_grts
  replace finished_grts channel hc := finished_grts channel hc row h_row
  set env := table.environment row
  suffices table.component.operations.FullRequirements env by
    simp only [circuit_norm] at this ⊢
    intro i hi _
    exact this i hi
  suffices table.component.operations.FullGuarantees env from
    table.component.weakSoundness (assumptions row h_row) (constraints row h_row) this |>.right
  simp only [Component.guarantees_iff, Component.rowOperations]
  rw [GeneralFormalCircuit.guarantees_iff]
  intro channel channel_mem
  show table.component.rowOperations.ChannelGuarantees channel env
  rw [← Component.channelGuarantees_iff]
  replace channel_mem := subset channel_mem
  simp at channel_mem
  rcases channel_mem with rfl | channel_mem
  · exact channel_grts
  · exact finished_grts _ channel_mem
end Table

/-- Light-weight package of multiple flat AIR tables sharing one prover data object. -/
structure Tables (F : Type) [Field F] where
  tables : List (Table F)
  data : ProverData F
  same_data : ∀ table ∈ tables, table.data = data

namespace Tables
def cons (table : Table F) (tables : Tables F) (same_data : table.data = tables.data) : Tables F where
  tables := table :: tables.tables
  data := tables.data
  same_data := by
    simp [same_data]
    apply tables.same_data

@[circuit_norm] lemma cons_tables {table : Table F} {tables : Tables F} (same_data : table.data = tables.data) :
  (cons table tables same_data).tables = table :: tables.tables := rfl

@[circuit_norm] lemma cons_data {table : Table F} {tables : Tables F} (same_data : table.data = tables.data) :
  (cons table tables same_data).data = tables.data := rfl

def induct {motive : Tables F → Sort*}
  (nil : ∀ data, motive ⟨ [], data, by simp ⟩)
  (cons : ∀ table tables same_data, motive tables → motive (cons table tables same_data))
    (tables : Tables F) : motive tables := by
  rcases tables with ⟨ ts, data, same_data ⟩
  induction ts with
  | nil => exact nil data
  | cons table ts ih =>
    have same_data' : ∀ table ∈ ts, table.data = data := by
      intro table h_table
      apply same_data
      simp [h_table]
    let tables : Tables F := ⟨ ts, data, same_data' ⟩
    have same_data_table : table.data = tables.data := by
      simp [tables, same_data]
    apply cons table tables same_data_table
    exact ih same_data'

def append (tables1 tables2 : Tables F) (same_data : tables1.data = tables2.data) : Tables F where
  tables := tables1.tables ++ tables2.tables
  data := tables1.data
  same_data := by
    simp [or_imp, forall_and]
    constructor
    · apply tables1.same_data
    rw [same_data]
    apply tables2.same_data

@[circuit_norm] lemma append_tables {tables1 tables2 : Tables F} (same_data : tables1.data = tables2.data) :
  (append tables1 tables2 same_data).tables = tables1.tables ++ tables2.tables := rfl

@[circuit_norm] lemma append_data {tables1 tables2 : Tables F} (same_data : tables1.data = tables2.data) :
  (append tables1 tables2 same_data).data = tables1.data := rfl

@[circuit_norm] lemma cons_append {table : Table F} {tables1 tables2 : Tables F}
  (same_data1 : table.data = tables1.data) (same_data2 : tables1.data = tables2.data) :
  (cons table tables1 same_data1).append tables2 same_data2 =
    cons table (append tables1 tables2 same_data2) same_data1 := rfl

@[circuit_norm]
abbrev components (tables : Tables F) : List (Component F) :=
  tables.tables.map (·.component)

instance : Coe (Tables F) (List (Table F)) where
  coe tables := tables.tables

abbrev Constraints (tables : Tables F) : Prop :=
  ∀ table ∈ tables.tables, table.Constraints

abbrev Assumptions (tables : Tables F) : Prop :=
  ∀ table ∈ tables.tables, table.Assumptions

noncomputable abbrev interactionsWith (tables : Tables F) (channel : RawChannel F) : List (Interaction F) :=
  tables.tables.flatMap (·.interactionsWith channel)

@[circuit_norm] lemma interactionsWith_cons {table : Table F} {tables : Tables F}
  (same_data : table.data = tables.data) {channel : RawChannel F} :
  interactionsWith (cons table tables same_data) channel =
    table.interactionsWith channel ++ interactionsWith tables channel := by
  simp [interactionsWith, Table.interactionsWith, circuit_norm]

@[circuit_norm] lemma interactionsWith_append {tables1 tables2 : Tables F}
  (same_data : tables1.data = tables2.data) {channel : RawChannel F} :
  interactionsWith (append tables1 tables2 same_data) channel =
    interactionsWith tables1 channel ++ interactionsWith tables2 channel := by
  simp [interactionsWith, Table.interactionsWith, circuit_norm]
end Tables

end Air.Flat
