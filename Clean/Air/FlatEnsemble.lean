/-
This file defines flat AIR ensembles and what soundness and completeness mean for them.
-/
module

public import Clean.Air.FlatComponent
public import Clean.Air.Balance
public import Clean.Air.Verifier

@[expose] public section

namespace Air.Flat
universe u
variable {F : Type} [FiniteField F]
variable {PublicIO : TypeMap} [ProvableType PublicIO]

/-- Channels on which a participant of an ensemble, a component or the verifier, adds guarantees and
requirements. -/
class ChannelInterface (α : Type u) (F : outParam Type) where
  channelsWithGuarantees : α → List (RawChannel F)
  channelsWithRequirements : α → List (RawChannel F)

instance : ChannelInterface (Component F) F where
  channelsWithGuarantees component := component.circuit.channelsWithGuarantees
  channelsWithRequirements component := component.circuit.channelsWithRequirements

instance : ChannelInterface (Verifier.Program F PublicIO) F where
  channelsWithGuarantees verifier := verifier.channelsWithGuarantees
  channelsWithRequirements verifier := verifier.channelsWithRequirements

namespace ChannelInterface
@[circuit_norm] lemma channelsWithGuarantees_component (component : Component F) :
    channelsWithGuarantees component = component.circuit.channelsWithGuarantees := rfl
@[circuit_norm] lemma channelsWithRequirements_component (component : Component F) :
    channelsWithRequirements component = component.circuit.channelsWithRequirements := rfl
@[circuit_norm] lemma channelsWithGuarantees_verifier (verifier : Verifier.Program F PublicIO) :
    channelsWithGuarantees verifier = verifier.channelsWithGuarantees := rfl
@[circuit_norm] lemma channelsWithRequirements_verifier (verifier : Verifier.Program F PublicIO) :
    channelsWithRequirements verifier = verifier.channelsWithRequirements := rfl
end ChannelInterface

/-- A named hint table viewing the flattened private input: `rows` rows of `width` elements,
starting at element `offset`. Elements beyond the input read as zero. -/
structure HintTable where
  key : String
  width : ℕ
  offset : ℕ
  rows : ℕ
deriving Repr, DecidableEq

/-- The hint tables `tables` take from the flattened private input `elements`. Like derived prover
data, rows are cut off or zero-padded at the requested width. -/
def HintTable.hint (tables : List HintTable) (elements : Array F) : ProverHint F := fun key width =>
  match tables.find? (·.key == key) with
  | none => #[]
  | some table => Array.ofFn fun (row : Fin table.rows) => rowPrefix width <|
      elements.extract (table.offset + row.val * table.width)
        (table.offset + (row.val + 1) * table.width)

/-- An ensemble of AIR components: everything a prover and a verifier implementation need. -/
structure Ensemble (F : Type) [FiniteField F] (PublicIO : TypeMap) [ProvableType PublicIO] where
  /-- Components have unique names. Their order is the order of the traces. -/
  tables : List (Component F)
  unique_names : (tables.map (·.circuit.name)).Nodup
  channels : List (RawChannel F)
  verifier : Verifier.Program F PublicIO := .empty F PublicIO
  /-- The prover's private input to witness generation. -/
  ProverInput : TypeMap := unit
  [provableProverInput : ProvableType ProverInput]
  /-- The hint tables that witness programs read, as views of the flattened private input. -/
  hintTables : List HintTable := []

instance (ens : Ensemble F PublicIO) : ProvableType ens.ProverInput := ens.provableProverInput

/-- The hint tables encoding a private input. -/
def Ensemble.hint (ens : Ensemble F PublicIO) (proverInput : ens.ProverInput F) : ProverHint F :=
  HintTable.hint ens.hintTables (toElements proverInput).toArray

/-- The public input and the component traces of an ensemble proof. -/
structure EnsembleWitness (ens : Ensemble F PublicIO) where
  tables : List (Table F)
  publicInput : PublicIO F
  same_length : ens.tables.length = tables.length
  same_circuits : ∀ i (hi : i < ens.tables.length),
    ens.tables[i] = tables[i].component
  same_data : ∀ table ∈ tables, table.data = deriveProverData tables (toElements publicInput).toArray

/-- The prover data of a witness: the input rows of its tables, and its public input. -/
def EnsembleWitness.data {ens : Ensemble F PublicIO} (witness : EnsembleWitness ens) :
    ProverData F :=
  deriveProverData witness.tables (toElements witness.publicInput).toArray

/-- The prover data of a witness holds its public input. -/
@[circuit_norm]
lemma EnsembleWitness.data_getPublicInput {ens : Ensemble F PublicIO} (witness : EnsembleWitness ens) :
    witness.data.getPublicInput PublicIO = witness.publicInput :=
  ProvableType.eval_fromInput_varFromOffset_zero witness.publicInput _

@[circuit_norm]
lemma List.flatMap_subset_iff {α β : Type*} {f : α → List β} {l₁ : List α} {l₂ : List β} :
    l₁.flatMap f ⊆ l₂ ↔ ∀ a ∈ l₁, f a ⊆ l₂ := by
  grind

namespace Ensemble
variable {ens : Ensemble F PublicIO}

def empty (F : Type) [FiniteField F] (PublicIO : TypeMap) [ProvableType PublicIO] :
  Ensemble F PublicIO where
    tables := []
    unique_names := by simp
    channels := []

@[circuit_norm] lemma empty_tables :
  (empty F PublicIO).tables = [] := rfl
@[circuit_norm] lemma empty_channels :
  (empty F PublicIO).channels = [] := rfl
@[circuit_norm] lemma empty_verifier :
  (empty F PublicIO).verifier = Verifier.Program.empty F PublicIO := rfl
@[circuit_norm]
abbrev verifierOperations (ens : Ensemble F PublicIO) : Operations F :=
  ens.verifier.circuitOperations

def VerifierGuarantees (ens : Ensemble F PublicIO) (data : ProverData F) : Prop :=
  ens.verifierOperations.FullGuarantees data.publicEnvironment

@[circuit_norm]
def VerifierSpec (ens : Ensemble F PublicIO) (publicInput : PublicIO F) (data : ProverData F) :
    Prop :=
  ens.verifier.Spec publicInput data

lemma verifierSpec_of_verifierGuarantees (ens : Ensemble F PublicIO) (data : ProverData F) :
    ens.VerifierGuarantees data → ens.VerifierSpec (data.getPublicInput PublicIO) data :=
  ens.verifier.soundness data

def VerifierChannelGuarantees (ens : Ensemble F PublicIO) (data : ProverData F)
    (channel : RawChannel F) : Prop :=
  ens.verifierOperations.ChannelGuarantees channel data.publicEnvironment

def VerifierChannelRequirements (ens : Ensemble F PublicIO) (data : ProverData F)
    (channel : RawChannel F) : Prop :=
  ens.verifierOperations.ChannelRequirements channel data.publicEnvironment

lemma verifierChannelRequirements_of_not_mem (ens : Ensemble F PublicIO) (data : ProverData F)
    {channel : RawChannel F} :
    channel ∉ ens.verifier.channelsWithRequirements →
      ens.VerifierChannelRequirements data channel :=
  Operations.requirements_of_not_mem ens.verifierOperations
    ens.verifier.channelsWithRequirements data.publicEnvironment
    (ens.verifier.operations.circuitOperations_inChannelsOrRequirementsFull _) channel

lemma verifierChannelGuarantees_of_not_mem (ens : Ensemble F PublicIO) (data : ProverData F)
    {channel : RawChannel F} :
    channel ∉ ens.verifier.channelsWithGuarantees → ens.VerifierChannelGuarantees data channel :=
  Operations.guarantees_of_not_mem ens.verifierOperations
    ens.verifier.channelsWithGuarantees data.publicEnvironment
    (ens.verifier.operations.circuitOperations_inChannelsOrGuaranteesFull _) channel

lemma verifierGuarantees_iff (ens : Ensemble F PublicIO) (data : ProverData F) :
    ens.VerifierGuarantees data ↔
      ∀ channel ∈ ens.verifier.channelsWithGuarantees, ens.VerifierChannelGuarantees data channel :=
  Operations.guarantees_iff ens.verifierOperations ens.verifier.channelsWithGuarantees _
    (ens.verifier.operations.circuitOperations_inChannelsOrGuaranteesFull _)

def channelsWithGuarantees (ens : Ensemble F PublicIO) : List (RawChannel F) :=
  ens.verifier.channelsWithGuarantees ++
    ens.tables.flatMap (·.circuit.channelsWithGuarantees)

def channelsWithRequirements (ens : Ensemble F PublicIO) : List (RawChannel F) :=
  ens.verifier.channelsWithRequirements ++
    ens.tables.flatMap (·.circuit.channelsWithRequirements)

lemma channelsWithGuarantees_eq_verifier_append (ens : Ensemble F PublicIO) :
  ens.channelsWithGuarantees = ens.verifier.channelsWithGuarantees ++ ens.tables.flatMap (·.circuit.channelsWithGuarantees) := by
  rfl

lemma channelsWithRequirements_eq_verifier_append (ens : Ensemble F PublicIO) :
  ens.channelsWithRequirements = ens.verifier.channelsWithRequirements ++ ens.tables.flatMap (·.circuit.channelsWithRequirements) := by
  rfl

@[circuit_norm]
lemma channelsWithGuarantees_subset_iff {ens : Ensemble F PublicIO} {finished : List (RawChannel F)} :
  ens.channelsWithGuarantees ⊆ finished ↔
    ens.verifier.channelsWithGuarantees ⊆ finished ∧
      ∀ component ∈ ens.tables, component.circuit.channelsWithGuarantees ⊆ finished := by
  simp [circuit_norm, channelsWithGuarantees]
end Ensemble

namespace EnsembleWitness
variable {ens : Ensemble F PublicIO}

@[circuit_norm]
lemma tables_map_component (witness : EnsembleWitness ens) :
    witness.tables.map (·.component) = ens.tables := by
  apply List.ext_getElem
  · simp [witness.same_length]
  intro i hi hi'
  simp [witness.same_circuits i hi']

lemma tableNames_nodup (witness : EnsembleWitness ens) :
    (witness.tables.map (fun table => table.component.circuit.name)).Nodup := by
  rw [show witness.tables.map (fun table => table.component.circuit.name) =
    ens.tables.map (·.circuit.name) by
      calc
        _ = (witness.tables.map (·.component)).map (·.circuit.name) := by simp
        _ = ens.tables.map (·.circuit.name) :=
          congrArg (List.map (·.circuit.name)) witness.tables_map_component]
  exact ens.unique_names

lemma dataConsistency_of_mem (witness : EnsembleWitness ens) :
    ∀ table ∈ witness.tables, table.DataConsistency := by
  intro table htable
  rw [Table.DataConsistency, witness.same_data table htable]
  exact deriveTables_eq_of_mem witness.tables witness.tableNames_nodup htable _

def toTables (witness : EnsembleWitness ens) : Tables F where
  tables := witness.tables
  data := witness.data
  same_data := witness.same_data

@[circuit_norm] lemma toTables_tables (witness : EnsembleWitness ens) :
  witness.toTables.tables = witness.tables := rfl
@[circuit_norm] lemma toTables_data (witness : EnsembleWitness ens) :
  witness.toTables.data = witness.data := rfl

@[circuit_norm]
lemma component_mem_tables_of_mem {witness : EnsembleWitness ens} {table : Table F} :
    table ∈ witness.tables → table.component ∈ ens.tables := by
  rw [← witness.tables_map_component]
  grind

/-- A component with fixed columns has exactly one row of prover data per fixed row. -/
lemma getRows_size_of_fixedColumns (witness : EnsembleWitness ens) {component : Component F}
    (hcomponent : component ∈ ens.tables) {fixed : FixedColumns F}
    (hfixed : component.fixedColumns = some fixed) :
    (witness.data.getRows component.circuit.name component.Input).size = fixed.height.toNat := by
  rw [← witness.tables_map_component, List.mem_map] at hcomponent
  obtain ⟨table, htable, rfl⟩ := hcomponent
  have hmatch := table.fixed_rows_match
  simp only [Component.FixedRowsMatch, hfixed] at hmatch
  rw [ProverData.getRows, EnsembleWitness.data, ← witness.same_data table htable,
    witness.dataConsistency_of_mem table htable]
  simpa [Table.proverRows] using congrArg List.length hmatch

@[circuit_norm]
def Constraints {ens : Ensemble F PublicIO} (witness : EnsembleWitness ens) : Prop :=
  ∀ table ∈ witness.tables, table.Constraints

@[circuit_norm]
def Assumptions {ens : Ensemble F PublicIO} (witness : EnsembleWitness ens) : Prop :=
  ∀ table ∈ witness.tables, table.Assumptions

@[circuit_norm]
def Spec {ens : Ensemble F PublicIO} (witness : EnsembleWitness ens) : Prop :=
  ens.VerifierSpec witness.publicInput witness.data ∧
    ∀ table ∈ witness.tables, table.Spec

def interactions {ens : Ensemble F PublicIO} (witness : EnsembleWitness ens) : List (Interaction F) :=
  ens.verifierOperations.interactionValues witness.data.publicEnvironment ++
    witness.tables.flatMap (fun table => table.interactions)

noncomputable def verifierInteractionsWith {ens : Ensemble F PublicIO}
    (witness : EnsembleWitness ens) (channel : RawChannel F) : List (Interaction F) :=
  ens.verifierOperations.interactionValuesWith channel
    witness.data.publicEnvironment

noncomputable def interactionsWith {ens : Ensemble F PublicIO} (witness : EnsembleWitness ens)
    (channel : RawChannel F) : List (Interaction F) :=
  witness.verifierInteractionsWith channel ++ witness.toTables.interactionsWith channel

lemma mem_interactionsWith {witness : EnsembleWitness ens}
  {channel : RawChannel F} {i : Interaction F} :
    i ∈ witness.interactionsWith channel ↔
    i ∈ witness.verifierInteractionsWith channel ∨
      ∃ table ∈ witness.tables, i ∈ table.interactionsWith channel := by
  simp only [interactionsWith, Tables.interactionsWith, toTables,
    List.mem_append, List.mem_flatMap]

lemma channel_eq_of_mem_interactionsWith {witness : EnsembleWitness ens}
  {channel : RawChannel F} {i : Interaction F} :
    i ∈ witness.interactionsWith channel → i.channel = channel := by
  rw [mem_interactionsWith]
  rintro (h_verifier | ⟨table, _, h_table⟩)
  · simp only [verifierInteractionsWith, Operations.interactionValuesWith_eq_map,
      List.mem_map] at h_verifier
    obtain ⟨interaction, h_interaction, rfl⟩ := h_verifier
    exact Operations.channel_eq_of_mem_interactionsWith h_interaction
  · exact table.channel_eq_of_mem_interactionsWith h_table

lemma verifierChannelRequirements_iff_forall {witness : EnsembleWitness ens}
    {channel : RawChannel F} :
    ens.VerifierChannelRequirements witness.data channel ↔
      ∀ i ∈ witness.verifierInteractionsWith channel, i.Requirements witness.data := by
  simp only [Ensemble.VerifierChannelRequirements, Operations.ChannelRequirements,
    Operations.forall_interactionsWith_iff, verifierInteractionsWith,
    Operations.interactionValuesWith_eq_map, List.forall_mem_map]
  rfl

lemma verifierChannelGuarantees_iff_forall {witness : EnsembleWitness ens}
    {channel : RawChannel F} :
    ens.VerifierChannelGuarantees witness.data channel ↔
      ∀ i ∈ witness.verifierInteractionsWith channel, i.Guarantees witness.data := by
  simp only [Ensemble.VerifierChannelGuarantees, Operations.ChannelGuarantees,
    Operations.forall_interactionsWith_iff, verifierInteractionsWith,
    Operations.interactionValuesWith_eq_map, List.forall_mem_map]
  rfl

lemma interactionsWith_of_verifier_empty {ens : Ensemble F PublicIO} {witness : EnsembleWitness ens} {channel : RawChannel F}
  (h_verifier_empty : ens.verifier = .empty F PublicIO) :
    witness.interactionsWith channel =
      witness.tables.flatMap (·.interactionsWith channel) := by
  simp [interactionsWith, verifierInteractionsWith, Tables.interactionsWith,
    circuit_norm, h_verifier_empty, Verifier.Program.empty]

/-- The ensemble interactions with a particular channel are balanced. -/
@[circuit_norm]
abbrev BalancedChannel {ens : Ensemble F PublicIO} (witness : EnsembleWitness ens)
    (channel : RawChannel F) : Prop :=
  BalancedInteractions (witness.interactionsWith channel)

/-- All ensemble interactions with all ensemble channels are balanced. -/
@[circuit_norm]
def BalancedChannels {ens : Ensemble F PublicIO} (witness : EnsembleWitness ens) : Prop :=
  ∀ channel ∈ ens.channels, BalancedChannel witness channel

/-- The number of rows of each table, in the order of the ensemble's components. -/
def heights {ens : Ensemble F PublicIO} (witness : EnsembleWitness ens) : List ℕ :=
  witness.tables.map (·.table.length)
end EnsembleWitness

/- ## Soundness, Completeness and related definitions -/

namespace Ensemble

/--
The raw "statement" that a proof about an ensemble makes. Could also be called "relation". Like the
public input, the table heights are part of a proof.

TODO: we currently assume a proof system that already provides us with the fact that the
total interaction length doesn't overflow (as part of `BalancedChannels`). Instead, that bound
should follow from the table heights.
-/
def Statement (ens : Ensemble F PublicIO) (publicInput : PublicIO F) (heights : List ℕ) : Prop :=
  ∃ witness : EnsembleWitness ens,
    witness.publicInput = publicInput ∧ witness.heights = heights ∧
    witness.Constraints ∧ witness.BalancedChannels

/-- Soundness: assumptions on the public input and the table heights, plus the raw statement,
imply the spec. -/
def Soundness (ens : Ensemble F PublicIO) (Assumptions : PublicIO F → List ℕ → Prop)
    (Spec : PublicIO F → Prop) : Prop :=
  ∀ publicInput heights, Assumptions publicInput heights →
    ens.Statement publicInput heights → Spec publicInput

/-- Completeness: the spec implies the raw statement, for some table heights satisfying the
assumptions. -/
def Completeness (ens : Ensemble F PublicIO) (Assumptions : PublicIO F → List ℕ → Prop)
    (Spec : PublicIO F → Prop) : Prop :=
  ∀ publicInput, Spec publicInput →
    ∃ heights, Assumptions publicInput heights ∧ ens.Statement publicInput heights
end Ensemble

/-- An ensemble with its specification and soundness proof. -/
structure FormalEnsemble (F : Type) [FiniteField F]
    (PublicIO : TypeMap) [ProvableType PublicIO] where
  ensemble : Ensemble F PublicIO
  /-- Assumptions on the public input and the table heights. -/
  Assumptions : PublicIO F → List ℕ → Prop := fun _ _ => True
  Spec : PublicIO F → Prop
  soundness : ensemble.Soundness Assumptions Spec
  /-- What the public and private inputs must satisfy for witness generation to succeed. -/
  ProverAssumptions : PublicIO F → ensemble.ProverInput F → Prop := fun _ _ => True

namespace Ensemble

/--
"Table soundness" means that we can prove the spec for each table,
assuming constraints and channel balance.
This is just Soundness, except for per-table soundness implying global soundness.
-/
@[circuit_norm]
def TableSoundness (ens : Ensemble F PublicIO) : Prop :=
  ∀ (witness : EnsembleWitness ens),
    witness.Assumptions →
    witness.Constraints →
    witness.BalancedChannels →
    witness.Spec

/-- The verifier spec and table specs imply the ensemble's public specification. -/
def SpecConsistency (ens : Ensemble F PublicIO) (Spec : PublicIO F → Prop) : Prop :=
  ∀ (witness : EnsembleWitness ens),
    -- TODO maybe we could add balanced channels + channel reqs / grts here as well, to enable you to prove
    -- something at the global level from the max interaction length, like we do below for fibonacci
    -- where we prove the counter does not overflow.
    witness.Spec →
    Spec witness.publicInput

/-- Ensemble-level assumptions imply every component's residual assumptions, for all inputs and
prover data. -/
@[circuit_norm]
def AssumptionsConsistency (ens : Ensemble F PublicIO)
    (Assumptions : PublicIO F → List ℕ → Prop) : Prop :=
  ∀ publicInput heights, Assumptions publicInput heights →
    ∀ component ∈ ens.tables, ∀ input data, component.Assumptions input data

lemma assumptions_of_assumptionsConsistency {ens : Ensemble F PublicIO}
    {Assumptions : PublicIO F → List ℕ → Prop}
    (consistency : ens.AssumptionsConsistency Assumptions) (witness : EnsembleWitness ens)
    (assumptions : Assumptions witness.publicInput witness.heights) : witness.Assumptions := by
  intro table htable row _
  exact consistency _ _ assumptions _ (EnsembleWitness.component_mem_tables_of_mem htable) _ _

theorem soundness_of_tableSoundness_and_specConsistency (ens : Ensemble F PublicIO)
  (Assumptions : PublicIO F → List ℕ → Prop) (Spec : PublicIO F → Prop) :
  ens.TableSoundness →
  ens.AssumptionsConsistency Assumptions →
  ens.SpecConsistency Spec →
    ens.Soundness Assumptions Spec := by
  simp only [Soundness, TableSoundness, AssumptionsConsistency, SpecConsistency, Statement,
    forall_exists_index, and_imp]
  intro table_soundness assumptions_consistency spec_consistency
    publicInput heights assumptions witness publicInput_eq heights_eq constraints balance
  simp only [← publicInput_eq, ← heights_eq] at *
  apply spec_consistency witness
  apply table_soundness witness ?assumptions constraints balance
  exact assumptions_of_assumptionsConsistency assumptions_consistency witness assumptions
end Ensemble

/- ## Constructing ensembles -/

namespace Ensemble
/-- Takes the verifier and the prover input from the second ensemble. -/
def merge (ens1 ens2 : Ensemble F PublicIO)
    (unique_names : ((ens2.tables ++ ens1.tables).map (·.circuit.name)).Nodup) :
    Ensemble F PublicIO :=
  { ens2 with
    tables := ens2.tables ++ ens1.tables,
    unique_names
    channels := ens2.channels ++ ens1.channels }

@[circuit_norm] lemma merge_tables (ens1 ens2 : Ensemble F PublicIO) (unique_names) :
  (ens1.merge ens2 unique_names).tables = ens2.tables ++ ens1.tables := rfl
@[circuit_norm] lemma merge_verifier (ens1 ens2 : Ensemble F PublicIO) (unique_names) :
  (ens1.merge ens2 unique_names).verifier = ens2.verifier := rfl

def addTable (ens : Ensemble F PublicIO) (table : Component F)
    (fresh : table.circuit.name ∉ ens.tables.map (·.circuit.name)) : Ensemble F PublicIO :=
  { ens with
    tables := table :: ens.tables
    unique_names := by simpa using List.nodup_cons.mpr ⟨fresh, ens.unique_names⟩ }

@[circuit_norm] lemma addTable_tables (ens : Ensemble F PublicIO) (table : Component F) (fresh) :
  (ens.addTable table fresh).tables = table :: ens.tables := rfl
@[circuit_norm] lemma addTable_verifier (ens : Ensemble F PublicIO) (table : Component F) (fresh) :
  (ens.addTable table fresh).verifier = ens.verifier := rfl

/-- Declare the prover's private input: its type, and the hint tables viewing it. -/
def withProverInput (ens : Ensemble F PublicIO) (ProverInput : TypeMap)
    [ProvableType ProverInput] (hintTables : List HintTable) : Ensemble F PublicIO :=
  { ens with ProverInput, provableProverInput := inferInstance, hintTables }

section
variable {ens : Ensemble F PublicIO} {ProverInput : TypeMap} [ProvableType ProverInput]
  {hintTables : List HintTable}

@[circuit_norm] lemma withProverInput_tables :
  (ens.withProverInput ProverInput hintTables).tables = ens.tables := rfl
@[circuit_norm] lemma withProverInput_channels :
  (ens.withProverInput ProverInput hintTables).channels = ens.channels := rfl
@[circuit_norm] lemma withProverInput_verifier :
  (ens.withProverInput ProverInput hintTables).verifier = ens.verifier := rfl
end

end Ensemble
end Air.Flat
