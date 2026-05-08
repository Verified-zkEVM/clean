import Clean.Air.Circuit

variable {F : Type} [Field F]
variable {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]

structure AbstractTable (F : Type) [Field F] where
  {Input : TypeMap} {Output : TypeMap}
  [provableInput : ProvableType Input] [provableOutput : ProvableType Output]
  circuit : GeneralFormalCircuit F Input Output

instance (t: AbstractTable F) : ProvableType t.Input := t.provableInput
instance (t: AbstractTable F) : ProvableType t.Output := t.provableOutput

namespace AbstractTable
def operations (table : AbstractTable F) : Operations F :=
  table.circuit.instantiate.operations 0

def width (table : AbstractTable F) : ℕ := table.circuit.size

@[circuit_norm]
abbrev rowOffset (table : AbstractTable F) : ℕ := size table.Input
@[circuit_norm]
abbrev rowInputVar (table : AbstractTable F): Var table.Input F :=
  varFromOffset table.Input 0

/-- first `size Input` elements of the environment are the input -/
@[circuit_norm]
def rowInput (table : AbstractTable F) (row : Environment F) : table.Input F :=
  valueFromOffset table.Input 0 row

/-- output is whatever the circuit computes on the row input -/
@[circuit_norm]
def rowOutput (table : AbstractTable F) (row : Environment F) : table.Output F :=
  let outputVar := (table.circuit table.rowInputVar).output table.rowOffset
  eval row outputVar

@[circuit_norm]
def rowOperations (table : AbstractTable F) : Operations F :=
  table.circuit.main (varFromOffset table.Input 0) |>.operations (size table.Input)

def Spec (table : AbstractTable F) (row : Environment F) : Prop :=
  table.circuit.Spec (table.rowInput row) (table.rowOutput row) row.data

def Assumptions (table : AbstractTable F) (row : Environment F) : Prop :=
  table.circuit.Assumptions (table.rowInput row) row.data

abbrev exposedChannels (table : AbstractTable F) : List (ExposedChannel F) :=
  table.circuit.exposedChannels table.rowInputVar table.rowOffset

variable {table : AbstractTable F} {env : Environment F}

lemma constraints_eq : table.operations.constraints = table.rowOperations.constraints := by
  simp only [circuit_norm, witnessAny, GeneralFormalCircuit.instantiate, AbstractTable.operations,
    GeneralFormalCircuit.toSubcircuit, GeneralFormalCircuit.toWithHint,
    GeneralFormalCircuit.WithHint.toSubcircuit, Operations.toNested_toFlat]

lemma lookups_eq : table.operations.lookups = table.rowOperations.lookups := by
  simp only [circuit_norm, witnessAny, GeneralFormalCircuit.instantiate, AbstractTable.operations,
    GeneralFormalCircuit.toSubcircuit, GeneralFormalCircuit.toWithHint,
    GeneralFormalCircuit.WithHint.toSubcircuit, Operations.toNested_toFlat]

lemma interactions_eq : table.operations.interactions = table.rowOperations.interactions := by
  simp only [circuit_norm, witnessAny, GeneralFormalCircuit.instantiate, AbstractTable.operations,
    GeneralFormalCircuit.toSubcircuit, GeneralFormalCircuit.toWithHint,
    GeneralFormalCircuit.WithHint.toSubcircuit, Operations.toNested_toFlat]

lemma interactionsWith_eq {channel : RawChannel F} :
    table.operations.interactionsWith channel = table.rowOperations.interactionsWith channel := by
  simp only [Operations.interactionsWith, interactions_eq]

lemma interactionsValues_eq : table.operations.interactionValues env = table.rowOperations.interactionValues env := by
  simp only [Operations.interactionValues, interactions_eq]

lemma constraintsHold_iff (env : Environment F) :
    table.operations.ConstraintsHold env ↔ table.rowOperations.ConstraintsHold env := by
  simp only [circuit_norm, lookups_eq, constraints_eq]

lemma guarantees_iff (env : Environment F) :
    table.operations.FullGuarantees env ↔ table.rowOperations.FullGuarantees env := by
  simp only [circuit_norm, interactions_eq]

lemma requirements_iff (env : Environment F) :
    table.operations.FullRequirements env ↔ table.rowOperations.FullRequirements env := by
  simp only [circuit_norm, interactions_eq]

lemma channelGuarantees_iff (env : Environment F) (channel : RawChannel F) :
    table.operations.ChannelGuarantees channel env ↔ table.rowOperations.ChannelGuarantees channel env := by
  simp only [circuit_norm, interactions_eq]

lemma channelRequirements_iff (env : Environment F) (channel : RawChannel F) :
    table.operations.ChannelRequirements channel env ↔ table.rowOperations.ChannelRequirements channel env := by
  simp only [circuit_norm, interactions_eq]

lemma inChannelsOrRequirements (env : Environment F) :
    table.operations.InChannelsOrRequirementsFull table.circuit.channelsWithRequirements env := by
  have h := table.circuit.in_channels_or_requirements_full
  simp only [circuit_norm, interactions_eq] at *
  convert h _ _ env

lemma inChannelsOrGuarantees (env : Environment F) :
    table.operations.InChannelsOrGuaranteesFull table.circuit.channelsWithGuarantees env := by
  have h := table.circuit.in_channels_or_guarantees_full
  simp only [circuit_norm, interactions_eq] at *
  convert h _ _ env

-- this is the circuit's soundness theorem, stated in "instantiated" form
theorem weakSoundness {table : AbstractTable F} {env : Environment F} :
    table.Assumptions env →
    table.operations.ConstraintsHold env →
    table.operations.FullGuarantees env →
      table.Spec env ∧ table.operations.FullRequirements env := by
  simp only [constraintsHold_iff, guarantees_iff, requirements_iff, rowOperations, Spec]
  intro h_assumptions h_constraints h_guarantees
  set inputVar := varFromOffset table.Input 0
  set ops := (table.circuit.main inputVar).operations (size table.Input)
  have h_assumptions' : table.circuit.Assumptions (eval env inputVar) env.data := by
    simpa only [Assumptions, rowInput, inputVar, eval_varFromOffset_valueFromOffset] using h_assumptions
  convert table.circuit.original_full_soundness _ _ _ h_assumptions' h_constraints h_guarantees
  simp only [rowInput, inputVar, eval_varFromOffset_valueFromOffset]
end AbstractTable

structure TableWitness (F : Type) [Field F] where
  abstract : AbstractTable F
  width : ℕ
  table : List (Array F)
  data : ProverData F
  uniform_width : ∀ row ∈ table, row.size = width

namespace TableWitness
variable {witness :TableWitness F} {channel : RawChannel F}

abbrev length (t : TableWitness F) : ℕ := t.table.length

def environment (witness : TableWitness F) (row : Array F) :=
  Environment.fromArray row witness.data

theorem ext_iff {witness1 witness2 : TableWitness F} :
    witness1 = witness2 ↔
    witness1.abstract = witness2.abstract ∧
    witness1.width = witness2.width ∧
    witness1.table = witness2.table ∧
    witness1.data = witness2.data := by
  cases witness1
  cases witness2
  simp only [mk.injEq]

@[circuit_norm]
def channelsWithGuarantees (witness : TableWitness F) : List (RawChannel F) :=
  witness.abstract.circuit.channelsWithGuarantees

@[circuit_norm]
def channelsWithRequirements (witness : TableWitness F) : List (RawChannel F) :=
  witness.abstract.circuit.channelsWithRequirements

def Constraints (witness : TableWitness F) : Prop :=
  ∀ row ∈ witness.table,
    witness.abstract.operations.ConstraintsHold (witness.environment row)

def Assumptions (witness : TableWitness F) : Prop :=
  ∀ row ∈ witness.table,
    witness.abstract.Assumptions (witness.environment row)

def Guarantees (witness : TableWitness F) : Prop :=
  ∀ row ∈ witness.table,
    witness.abstract.operations.FullGuarantees (witness.environment row)

def ChannelGuarantees (witness : TableWitness F) (channel : RawChannel F) : Prop :=
  ∀ row ∈ witness.table,
    witness.abstract.operations.ChannelGuarantees channel (witness.environment row)

def InChannelsOrGuarantees (witness : TableWitness F) (channels : List (RawChannel F)) : Prop :=
  ∀ row ∈ witness.table,
    witness.abstract.operations.InChannelsOrGuaranteesFull channels (witness.environment row)

def Requirements (witness : TableWitness F) : Prop :=
  ∀ row ∈ witness.table,
    witness.abstract.operations.FullRequirements (witness.environment row)

def ChannelRequirements (witness : TableWitness F) (channel : RawChannel F) : Prop :=
  ∀ row ∈ witness.table,
    witness.abstract.operations.ChannelRequirements channel (witness.environment row)

def InChannelsOrRequirements (witness : TableWitness F) (channels : List (RawChannel F)) : Prop :=
  ∀ row ∈ witness.table,
    witness.abstract.operations.InChannelsOrRequirementsFull channels (witness.environment row)

def Spec (witness : TableWitness F) : Prop :=
  ∀ row ∈ witness.table,
    witness.abstract.Spec (witness.environment row)

def interactions (witness : TableWitness F) : List (Interaction F) :=
  witness.table.flatMap fun row =>
    witness.abstract.operations.interactionValues (witness.environment row)

noncomputable def interactionsWith (witness : TableWitness F) (channel : RawChannel F) : List (Interaction F) :=
  witness.table.flatMap fun row =>
    witness.abstract.operations.interactionValuesWith channel (witness.environment row)

open Classical in
lemma interactionsWith_eq_filter :
    witness.interactionsWith channel = witness.interactions.filter (·.channel = channel) := by
  simp only [interactionsWith, interactions, List.filter_flatMap]
  congr
  funext row
  rw [Operations.interactionValuesWith_eq_filter]

lemma channel_eq_of_mem_interactionsWith {i : Interaction F} :
    i ∈ witness.interactionsWith channel → i.channel = channel := by
  intro h_mem
  simp only [interactionsWith, List.mem_flatMap] at h_mem
  rcases h_mem with ⟨row, h_row, hi⟩
  simp only [Operations.interactionValuesWith, List.mem_map] at hi
  rcases hi with ⟨i_abs, hi_abs, heq⟩
  rw [←heq]
  apply Operations.channel_eq_of_mem_interactionsWith hi_abs

lemma forall_interactions_iff (witness : TableWitness F) (motive : Interaction F → Prop) :
    (∀ i ∈ witness.interactions, motive i) ↔
    ∀ row ∈ witness.table, ∀ i ∈ witness.abstract.operations.interactions,
      motive (i.eval (witness.environment row)) := by
  simp only [interactions, Operations.interactionValues, List.mem_flatMap, List.mem_map,
    forall_exists_index, and_imp]
  constructor
  · intro h row h_row i hi
    set env := witness.environment row
    exact h (i.eval env) row h_row i hi rfl
  · intro h i row h_row i' hi' h_eq
    rw [← h_eq]
    exact h row h_row i' hi'

lemma forall_interactionsWith_iff (witness : TableWitness F) (channel : RawChannel F)
  (motive : Interaction F → Prop) :
    (∀ i ∈ witness.interactionsWith channel, motive i) ↔
    ∀ row ∈ witness.table, ∀ i ∈ witness.abstract.operations.interactions,
      (i.channel = channel → motive (i.eval (witness.environment row))) := by
  simp only [interactionsWith, List.mem_flatMap, List.mem_map,
    forall_exists_index, and_imp, circuit_norm]
  constructor
  · intro h row h_row i hi h_channel
    set env := witness.environment row
    exact h (i.eval env) row h_row i hi h_channel rfl
  · intro h i row h_row i' hi' h_channel h_eq
    rw [← h_eq]
    exact h row h_row i' hi' h_channel

lemma interactionsWith_nil_of_channel_not_mem :
    channel ∉ witness.abstract.circuit.channels → witness.interactionsWith channel = [] := by
  contrapose!
  simp only [AbstractInteraction.eval_channel, interactionsWith_eq_filter, ne_eq, List.filter_eq_nil_iff,
    decide_eq_true_eq, forall_interactions_iff, not_forall, not_not, forall_exists_index]
  intro table table_mem i i_mem channel_eq
  symm at channel_eq; subst channel_eq
  simp only [AbstractTable.interactions_eq] at i_mem
  apply witness.abstract.circuit.channels_subset
  simp only [Operations.channels, List.mem_map]
  exists i

lemma guarantees_iff_forall (witness : TableWitness F) :
    witness.Guarantees ↔
    ∀ i ∈ witness.interactions, i.Guarantees witness.data := by
  simp only [TableWitness.Guarantees, circuit_norm, forall_interactions_iff]
  rfl

lemma channelGuarantees_iff_forall (witness : TableWitness F) (channel : RawChannel F) :
    witness.ChannelGuarantees channel ↔
    ∀ i ∈ witness.interactionsWith channel, i.Guarantees witness.data := by
  simp only [TableWitness.ChannelGuarantees, circuit_norm, forall_interactionsWith_iff]
  rfl

lemma guarantees_iff_channelGuarantees (witness : TableWitness F) :
    witness.Guarantees ↔
    ∀ channel ∈ witness.channelsWithGuarantees, witness.ChannelGuarantees channel := by
  simp only [TableWitness.Guarantees, TableWitness.ChannelGuarantees, channelsWithGuarantees]
  simp only [AbstractTable.guarantees_iff, AbstractTable.channelGuarantees_iff, AbstractTable.rowOperations]
  simp only [GeneralFormalCircuit.guarantees_iff']
  constructor <;> simp_all

lemma channelGuarantees_of_requirements (witness : TableWitness F) {channel : RawChannel F} :
    witness.Guarantees → witness.ChannelGuarantees channel := by
  simp_all [TableWitness.Guarantees, TableWitness.ChannelGuarantees, circuit_norm]

lemma requirements_iff_forall (witness : TableWitness F) :
    witness.Requirements ↔
    ∀ i ∈ witness.interactions, i.Requirements witness.data := by
  simp only [TableWitness.Requirements, circuit_norm, forall_interactions_iff]
  rfl

lemma channelRequirements_iff_forall (witness : TableWitness F) (channel : RawChannel F) :
    witness.ChannelRequirements channel ↔
    ∀ i ∈ witness.interactionsWith channel, i.Requirements witness.data := by
  simp only [TableWitness.ChannelRequirements, circuit_norm, forall_interactionsWith_iff]
  rfl

lemma requirements_iff_channelRequirements (witness : TableWitness F) :
    witness.Requirements ↔
    ∀ channel ∈ witness.channelsWithRequirements, witness.ChannelRequirements channel := by
  simp only [TableWitness.Requirements, TableWitness.ChannelRequirements, channelsWithRequirements]
  simp only [AbstractTable.requirements_iff, AbstractTable.channelRequirements_iff, AbstractTable.rowOperations]
  simp only [GeneralFormalCircuit.requirements_iff']
  constructor <;> simp_all

lemma channelRequirements_of_requirements (witness : TableWitness F) {channel : RawChannel F} :
    witness.Requirements → witness.ChannelRequirements channel := by
  simp_all [TableWitness.Requirements, TableWitness.ChannelRequirements, circuit_norm]

lemma inChannelsOrRequirements (witness : TableWitness F) :
    witness.InChannelsOrRequirements witness.channelsWithRequirements := by
  simp [InChannelsOrRequirements, channelsWithRequirements, AbstractTable.inChannelsOrRequirements]

lemma requirements_of_not_mem (witness : TableWitness F) {channel : RawChannel F} :
    channel ∉ witness.channelsWithRequirements → witness.ChannelRequirements channel := by
  intro h_not_mem
  have h_in_or_req := witness.inChannelsOrRequirements
  simp only [ChannelRequirements, InChannelsOrRequirements] at *
  intro row h_row
  specialize h_in_or_req row h_row
  apply Operations.requirements_of_not_mem _ witness.channelsWithRequirements
  assumption
  assumption

lemma inChannelsOrGuarantees (witness : TableWitness F) :
    witness.InChannelsOrGuarantees witness.channelsWithGuarantees := by
  simp [InChannelsOrGuarantees, channelsWithGuarantees, AbstractTable.inChannelsOrGuarantees]

lemma guarantees_of_not_mem (witness : TableWitness F) {channel : RawChannel F} :
    channel ∉ witness.channelsWithGuarantees → witness.ChannelGuarantees channel := by
  intro h_not_mem
  have h_in_or_guar := witness.inChannelsOrGuarantees
  simp only [ChannelGuarantees, InChannelsOrGuarantees] at *
  intro row h_row
  specialize h_in_or_guar row h_row
  apply Operations.guarantees_of_not_mem _ witness.channelsWithGuarantees
  assumption
  assumption

/-- Circuit soundness, lifted to full table level --/
theorem weakSoundness {witness : TableWitness F} :
    witness.Assumptions → witness.Constraints → witness.Guarantees →
    witness.Spec ∧ witness.Requirements := by
  simp_all [TableWitness.Constraints, TableWitness.Guarantees, TableWitness.Spec,
    TableWitness.Requirements, TableWitness.Assumptions, AbstractTable.weakSoundness]

/--
If we know constraints and _some_ of the guarantees unconditionally, we can remove them from the per-row assumptions.

This lemma is tailored to VM-like channels where there remains a single channel that we need to
prove guarantees for.
-/
lemma requirements_of_partial_guarantees_of_constraints {witness : TableWitness F}
  {finished : List (RawChannel F)} {unfinished : RawChannel F} :
  witness.Assumptions →
  witness.Constraints →
  witness.channelsWithGuarantees ⊆ unfinished :: finished →
  (∀ channel ∈ finished, witness.ChannelGuarantees channel) →
    ∀ row ∈ witness.table,
      witness.abstract.operations.ChannelGuarantees unfinished (witness.environment row) →
      witness.abstract.operations.ChannelRequirements unfinished (witness.environment row) := by
  intro assumptions constraints subset finished_grts row h_row channel_grts
  replace finished_grts channel hc := finished_grts channel hc row h_row
  set env := witness.environment row
  suffices witness.abstract.operations.FullRequirements env by
    simp only [circuit_norm] at this ⊢
    intro i hi _
    exact this i hi
  suffices witness.abstract.operations.FullGuarantees env from
    witness.abstract.weakSoundness (assumptions row h_row) (constraints row h_row) this |>.right
  simp only [AbstractTable.guarantees_iff, AbstractTable.rowOperations]
  rw [GeneralFormalCircuit.guarantees_iff']
  intro channel channel_mem
  show witness.abstract.rowOperations.ChannelGuarantees channel env
  rw [← AbstractTable.channelGuarantees_iff]
  replace channel_mem := subset channel_mem
  simp at channel_mem
  rcases channel_mem with rfl | channel_mem
  · exact channel_grts
  · exact finished_grts _ channel_mem
end TableWitness

/-- Light-weight package of multiple table witnesses -/
structure TablesWitness (F : Type) [Field F] where
  tables : List (TableWitness F)
  data : ProverData F
  same_data : ∀ table ∈ tables, table.data = data

namespace TablesWitness
def cons (table : TableWitness F) (witness : TablesWitness F) (same_data : table.data = witness.data) : TablesWitness F where
  tables := table :: witness.tables
  data := witness.data
  same_data := by
    simp [same_data]
    apply witness.same_data

@[circuit_norm] lemma cons_tables {table : TableWitness F} {witness : TablesWitness F} (same_data : table.data = witness.data) :
  (cons table witness same_data).tables = table :: witness.tables := rfl

@[circuit_norm] lemma cons_data {table : TableWitness F} {witness : TablesWitness F} (same_data : table.data = witness.data) :
  (cons table witness same_data).data = witness.data := rfl

def induct {motive : TablesWitness F → Sort*}
  (nil : ∀ data, motive ⟨ [], data, by simp ⟩)
  (cons : ∀ table witness same_data, motive witness → motive (cons table witness same_data))
    (table : TablesWitness F) : motive table := by
  rcases table with ⟨ tables, data, same_data ⟩
  induction tables with
  | nil => exact nil data
  | cons table tables ih =>
    have same_data' : ∀ table ∈ tables, table.data = data := by
      intro table h_table
      apply same_data
      simp [h_table]
    let witness : TablesWitness F := ⟨ tables, data, same_data' ⟩
    have same_data_table : table.data = witness.data := by
      simp [witness, same_data]
    apply cons table witness same_data_table
    exact ih same_data'

def append (witness1 witness2 : TablesWitness F) (same_data : witness1.data = witness2.data) : TablesWitness F where
  tables := witness1.tables ++ witness2.tables
  data := witness1.data
  same_data := by
    simp [or_imp, forall_and]
    constructor
    · apply witness1.same_data
    rw [same_data]
    apply witness2.same_data

@[circuit_norm] lemma append_tables {witness1 witness2 : TablesWitness F} (same_data : witness1.data = witness2.data) :
  (append witness1 witness2 same_data).tables = witness1.tables ++ witness2.tables := rfl

@[circuit_norm] lemma append_data {witness1 witness2 : TablesWitness F} (same_data : witness1.data = witness2.data) :
  (append witness1 witness2 same_data).data = witness1.data := rfl

@[circuit_norm] lemma cons_append {table : TableWitness F} {witness1 witness2 : TablesWitness F}
  (same_data1 : table.data = witness1.data) (same_data2 : witness1.data = witness2.data) :
  (cons table witness1 same_data1).append witness2 same_data2 =
    cons table (append witness1 witness2 same_data2) same_data1 := rfl

@[circuit_norm]
abbrev abstracts (witness : TablesWitness F) : List (AbstractTable F) :=
  witness.tables.map (·.abstract)

instance : Coe (TablesWitness F) (List (TableWitness F)) where
  coe witness := witness.tables

abbrev Constraints (witness : TablesWitness F) : Prop :=
  ∀ table ∈ witness.tables, table.Constraints

abbrev Assumptions (witness : TablesWitness F) : Prop :=
  ∀ table ∈ witness.tables, table.Assumptions

noncomputable abbrev interactionsWith (witness : TablesWitness F) (channel : RawChannel F) : List (Interaction F) :=
  witness.tables.flatMap (·.interactionsWith channel)

@[circuit_norm] lemma interactionsWith_cons {table : TableWitness F} {witness : TablesWitness F}
  (same_data : table.data = witness.data) {channel : RawChannel F} :
  interactionsWith (cons table witness same_data) channel =
    table.interactionsWith channel ++ interactionsWith witness channel := by
  simp [interactionsWith, TableWitness.interactionsWith, circuit_norm]

@[circuit_norm] lemma interactionsWith_append {witness1 witness2 : TablesWitness F}
  (same_data : witness1.data = witness2.data) {channel : RawChannel F} :
  interactionsWith (append witness1 witness2 same_data) channel =
    interactionsWith witness1 channel ++ interactionsWith witness2 channel := by
  simp [interactionsWith, TableWitness.interactionsWith, circuit_norm]
end TablesWitness
