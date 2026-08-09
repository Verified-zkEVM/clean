/-
This file defines flat AIR ensembles and what soundness and completeness mean for them.
-/
import Clean.Air.FlatComponent
import Clean.Air.Balance

namespace Air.Flat
variable {F : Type} [FiniteField F]
variable {PublicIO : TypeMap} [ProvableType PublicIO]

structure Ensemble (F : Type) [FiniteField F] (PublicIO : TypeMap) [ProvableType PublicIO] where
  /-- Components form an ordered map: names are keys, while list order fixes the trace order
  consumed by witness generation and backend extraction. -/
  tables : List (Component F)
  unique_names : (tables.map (·.name)).Nodup
  channels : List (RawChannel F)
  -- TODO: the verifier shouldn't be treated as a "circuit", and possibly shouldn't even be on here
  verifier : GeneralFormalCircuit F PublicIO unit := .empty F PublicIO
  verifier_length_zero : ∀ pi, verifier.localLength pi = 0 := by
    simp only [GeneralFormalCircuit.empty, circuit_norm]

/-- Semantic tables in their shared prover-data environment. This is the witness used by
the soundness and composition APIs; it may represent a shaped subset of a larger commitment. -/
structure EnsembleWitness (ens : Ensemble F PublicIO) where
  tables : List (Table F)
  publicInput : PublicIO F
  data : ProverData F
  same_length : ens.tables.length = tables.length
  same_circuits : ∀ i (hi : i < ens.tables.length),
    ens.tables[i] = tables[i].component
  same_data : ∀ table ∈ tables, table.data = data

/-- The externally committed tables. Their semantic `ProverData` is derived, not supplied. -/
structure CommittedEnsembleWitness (ens : Ensemble F PublicIO) where
  tableWitnesses : List (BareTable F)
  publicInput : PublicIO F
  same_length : ens.tables.length = tableWitnesses.length
  same_circuits : ∀ i (hi : i < ens.tables.length),
    ens.tables[i] = tableWitnesses[i].component

namespace CommittedEnsembleWitness

def data {ens : Ensemble F PublicIO} (witness : CommittedEnsembleWitness ens) : ProverData F :=
  deriveProverData witness.tableWitnesses

private lemma components_eq {ens : Ensemble F PublicIO}
    (committed : CommittedEnsembleWitness ens) :
    committed.tableWitnesses.map (·.component) = ens.tables := by
  apply List.ext_getElem
  · simp [committed.same_length]
  · intro i hi hi'
    simpa using (committed.same_circuits i hi').symm

private lemma tableNamesNodup {ens : Ensemble F PublicIO}
    (committed : CommittedEnsembleWitness ens) :
    (committed.tableWitnesses.map (fun table => table.component.name)).Nodup := by
  rw [show committed.tableWitnesses.map (fun table => table.component.name) =
    ens.tables.map (·.name) by rw [← committed.components_eq]; simp]
  exact ens.unique_names

private def tableOfMem {ens : Ensemble F PublicIO}
    (committed : CommittedEnsembleWitness ens)
    (bare : { table // table ∈ committed.tableWitnesses }) : Table F :=
  bare.val.toTable committed.data <| by
    intro hcolumns
    change committed.data bare.val.component.name bare.val.component.dataColumns.length =
      bare.val.proverRows bare.val.component.dataColumns.length
    exact deriveProverData_eq_of_mem committed.tableWitnesses committed.tableNamesNodup
      bare.property hcolumns _

def tables {ens : Ensemble F PublicIO} (committed : CommittedEnsembleWitness ens) :
    List (Table F) :=
  committed.tableWitnesses.attach.map committed.tableOfMem

@[circuit_norm] lemma tables_length {ens : Ensemble F PublicIO} (witness : CommittedEnsembleWitness ens) :
    witness.tables.length = witness.tableWitnesses.length := by simp [tables]

def toWitness {ens : Ensemble F PublicIO}
    (committed : CommittedEnsembleWitness ens) : EnsembleWitness ens where
  tables := committed.tables
  publicInput := committed.publicInput
  data := committed.data
  same_length := committed.same_length.trans committed.tables_length.symm
  same_circuits := by
    intro i hi
    simpa [tables, tableOfMem, BareTable.toTable] using committed.same_circuits i hi
  same_data := by
    intro table htable
    simp only [tables, List.mem_map] at htable
    obtain ⟨bare, _, rfl⟩ := htable
    rfl

end CommittedEnsembleWitness

/-- it's convenient to define a `Table` for the verifier, to treat them in a unified way -/
def Ensemble.verifierTable (ens : Ensemble F PublicIO) : Component F :=
  { name := "__verifier", circuit := ens.verifier }

/-- it's convenient to define a `Table` for the verifier, to treat them in a unified way -/
def EnsembleWitness.verifierTable {ens : Ensemble F PublicIO} (witness : EnsembleWitness ens) : Table F where
  component := { name := "__verifier", circuit := ens.verifier }
  -- it's important that this has one row, which contains the input,
  -- since we want to "run" the verifier once to produce interactions,
  -- and so that constraints etc are actually enforced
  table := [witness.publicInput |> toElements |>.toArray]
  data := witness.data
  uniform_width := by simp [Component.width, GeneralFormalCircuit.size_eq,
    ens.verifier_length_zero]
  fixed_rows_match := by simp [Component.fixedRowsMatch]

@[circuit_norm]
lemma List.flatMap_subset_iff {α β : Type*} {f : α → List β} {l₁ : List α} {l₂ : List β} :
    l₁.flatMap f ⊆ l₂ ↔ ∀ a ∈ l₁, f a ⊆ l₂ := by
  grind

namespace Ensemble
variable {ens : Ensemble F PublicIO}

def allTables (ens : Ensemble F PublicIO) : List (Component F) :=
  ens.verifierTable :: ens.tables

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
  (empty F PublicIO).verifier = .empty F PublicIO := rfl
@[circuit_norm] lemma empty_allTables :
  (empty F PublicIO).allTables = [{ name := "__verifier", circuit := .empty F PublicIO }] := rfl

lemma size_verifier {ens : Ensemble F PublicIO} :
    ens.verifier.size = size PublicIO := by
  simp [GeneralFormalCircuit.size_eq, ens.verifier_length_zero]

@[circuit_norm] lemma verifierTable_circuit : ens.verifierTable.circuit = ens.verifier := rfl
@[circuit_norm] lemma verifierTable_input : ens.verifierTable.Input = PublicIO := rfl
@[circuit_norm] lemma verifierTable_output : ens.verifierTable.Output = unit := rfl

@[circuit_norm] lemma mem_allTables_verifierTable:
  ens.verifierTable ∈ ens.allTables := by simp [allTables]
lemma mem_allTables_of_mem_tables {table : Component F} :
    table ∈ ens.tables → table ∈ ens.allTables := by simp_all [allTables]

lemma verifierTable_ext {ens1 ens2 : Ensemble F PublicIO} {witness1 : EnsembleWitness ens1} {witness2 : EnsembleWitness ens2} :
    ens1.verifier = ens2.verifier →
    witness1.publicInput = witness2.publicInput →
    witness1.data = witness2.data →
      witness1.verifierTable = witness2.verifierTable := by
  rintro h_circuit h_input h_data
  simp [EnsembleWitness.verifierTable, h_circuit, h_input, h_data]

@[circuit_norm]
abbrev verifierOperations (ens : Ensemble F PublicIO) : Operations F :=
  (ens.verifier.main (varFromOffset PublicIO 0)).operations (size PublicIO)

def VerifierConstraints (ens : Ensemble F PublicIO) (publicInput : PublicIO F) (data : ProverData F) : Prop :=
  ens.verifierOperations.ConstraintsHold (.fromInput publicInput data)

def VerifierGuarantees (ens : Ensemble F PublicIO) (publicInput : PublicIO F) (data : ProverData F) : Prop :=
  ens.verifierOperations.FullGuarantees (.fromInput publicInput data)

@[circuit_norm]
def VerifierSpec (ens : Ensemble F PublicIO) (publicInput : PublicIO F) (data : ProverData F) : Prop :=
  ens.verifier.Spec publicInput () data

lemma verifierTable_constraints :
  ens.verifierTable.operations.constraints = ens.verifierOperations.constraints := by
  rw [Component.constraints_eq]
  simp only [circuit_norm, Component.rowOperations]
  rfl

lemma verifierTable_lookups :
  ens.verifierTable.operations.lookups = ens.verifierOperations.lookups := by
  rw [Component.lookups_eq]
  simp only [circuit_norm, Component.rowOperations]
  rfl

lemma verifierTable_interactions :
  ens.verifierTable.operations.interactions = ens.verifierOperations.interactions := by
  rw [Component.interactions_eq]
  simp only [circuit_norm, Component.rowOperations]
  rfl

lemma verifierTable_interactionsWith {channel : RawChannel F} :
  ens.verifierTable.operations.interactionsWith channel =
    ens.verifierOperations.interactionsWith channel := by
  rw [Component.interactionsWith_eq]
  simp only [circuit_norm, Component.rowOperations]
  rfl

def channelsWithGuarantees (ens : Ensemble F PublicIO) : List (RawChannel F) :=
  ens.allTables.flatMap (·.circuit.channelsWithGuarantees)

def channelsWithRequirements (ens : Ensemble F PublicIO) : List (RawChannel F) :=
  ens.allTables.flatMap (·.circuit.channelsWithRequirements)

lemma channelsWithGuarantees_eq_verifier_append (ens : Ensemble F PublicIO) :
  ens.channelsWithGuarantees = ens.verifier.channelsWithGuarantees ++ ens.tables.flatMap (·.circuit.channelsWithGuarantees) := by
  simp [channelsWithGuarantees, allTables, verifierTable]

lemma channelsWithRequirements_eq_verifier_append (ens : Ensemble F PublicIO) :
  ens.channelsWithRequirements = ens.verifier.channelsWithRequirements ++ ens.tables.flatMap (·.circuit.channelsWithRequirements) := by
  simp [channelsWithRequirements, allTables, verifierTable]

@[circuit_norm]
lemma channelsWithGuarantees_subset_iff {ens : Ensemble F PublicIO} {finished : List (RawChannel F)} :
  ens.channelsWithGuarantees ⊆ finished ↔
    ∀ tables ∈ ens.allTables, tables.circuit.channelsWithGuarantees ⊆ finished := by
  simp [circuit_norm, channelsWithGuarantees]
end Ensemble

namespace EnsembleWitness
variable {ens : Ensemble F PublicIO}

def allTables (witness : EnsembleWitness ens) : List (Table F) :=
  witness.verifierTable :: witness.tables

@[circuit_norm] lemma data_eq_of_mem_allTables (witness : EnsembleWitness ens) :
  ∀ table ∈ witness.allTables, table.data = witness.data := by
  simp [allTables, verifierTable]
  exact witness.same_data

abbrev allTablesWitness (witness : EnsembleWitness ens) : Tables F where
  tables := witness.allTables
  data := witness.data
  same_data := by
    simp [allTables, verifierTable]
    apply witness.same_data

@[circuit_norm] lemma allTablesWitness_tables (witness : EnsembleWitness ens) :
  witness.allTablesWitness.tables = witness.allTables := rfl
@[circuit_norm] lemma allTablesWitness_data (witness : EnsembleWitness ens) :
  witness.allTablesWitness.data = witness.data := rfl

instance : CoeOut (EnsembleWitness ens) (Tables F) where
  coe witness := witness.allTablesWitness

lemma mem_allTables_of_mem_tables (witness : EnsembleWitness ens) {table : Table F} :
    table ∈ witness.tables → table ∈ witness.allTables := by
  simp_all [allTables]

lemma mem_allTables_verifierTable (witness : EnsembleWitness ens) :
    witness.verifierTable ∈ witness.allTables := by
  simp [allTables]

lemma forall_mem_allTables_iff (witness : EnsembleWitness ens)
  (motive : Table F → Prop) :
    (∀ table ∈ witness.allTables, motive table) ↔
    motive witness.verifierTable ∧ (∀ table ∈ witness.tables, motive table) := by
  simp [allTables]

@[circuit_norm] lemma verifierTable_component (witness : EnsembleWitness ens) :
  witness.verifierTable.component = ens.verifierTable := rfl
@[circuit_norm] lemma verifierTable_table (witness : EnsembleWitness ens) :
  witness.verifierTable.table = [witness.publicInput |> toElements |>.toArray] := rfl

@[circuit_norm]
lemma tables_map_component (witness : EnsembleWitness ens) :
    witness.tables.map (·.component) = ens.tables := by
  apply List.ext_getElem
  · simp [witness.same_length]
  intro i hi hi'
  simp [witness.same_circuits i hi']

@[circuit_norm]
lemma allTables_map_component (witness : EnsembleWitness ens) :
    witness.allTables.map (·.component) = ens.allTables := by
  simp only [circuit_norm, allTables, Ensemble.allTables]

lemma mem_tables_component_of_mem_tables {witness : EnsembleWitness ens} {table : Table F} :
    table ∈ witness.tables → table.component ∈ ens.tables := by
  rw [← witness.tables_map_component]
  grind

lemma mem_allTables_component_of_mem_allTables {witness : EnsembleWitness ens} {table : Table F} :
    table ∈ witness.allTables → table.component ∈ ens.allTables := by
  rw [← witness.allTables_map_component]
  grind

def Constraints {ens : Ensemble F PublicIO} (witness : EnsembleWitness ens) : Prop :=
  ∀ table ∈ witness.allTables, table.Constraints

def Assumptions {ens : Ensemble F PublicIO} (witness : EnsembleWitness ens) : Prop :=
  ∀ table ∈ witness.allTables, table.Assumptions

def Spec {ens : Ensemble F PublicIO} (witness : EnsembleWitness ens) : Prop :=
  ∀ table ∈ witness.allTables, table.Spec

def interactions {ens : Ensemble F PublicIO} (witness : EnsembleWitness ens) : List (Interaction F) :=
  (witness.allTables).flatMap (fun table => table.interactions)

noncomputable def interactionsWith {ens : Ensemble F PublicIO} (witness : EnsembleWitness ens)
    (channel : RawChannel F) : List (Interaction F) :=
  witness.allTables.flatMap (·.interactionsWith channel)

@[circuit_norm] lemma allTablesWitness_constraints {ens : Ensemble F PublicIO} (witness : EnsembleWitness ens) :
    witness.allTablesWitness.Constraints ↔ ∀ table ∈ witness.allTables, table.Constraints := by
  simp only [Tables.Constraints]

@[circuit_norm] lemma allTablesWitness_assumptions {ens : Ensemble F PublicIO} (witness : EnsembleWitness ens) :
    witness.allTablesWitness.Assumptions ↔ ∀ table ∈ witness.allTables, table.Assumptions := by
  simp only [Tables.Assumptions]

@[circuit_norm] lemma interactionsWith_allTablesWitness {ens : Ensemble F PublicIO}
  (witness : EnsembleWitness ens) (channel : RawChannel F) :
    witness.allTablesWitness.interactionsWith channel = witness.interactionsWith channel := rfl

lemma mem_interactionsWith {witness : EnsembleWitness ens}
  {channel : RawChannel F} {i : Interaction F} :
    i ∈ witness.interactionsWith channel ↔
    ∃ table ∈ witness.allTables, i ∈ table.interactionsWith channel := by
  simp only [interactionsWith, List.mem_flatMap]

lemma channel_eq_of_mem_interactionsWith {witness : EnsembleWitness ens}
  {channel : RawChannel F} {i : Interaction F} :
    i ∈ witness.interactionsWith channel → i.channel = channel := by
  rw [mem_interactionsWith]
  intro h_mem
  rcases h_mem with ⟨ table, h_table, h_mem_table ⟩
  apply table.channel_eq_of_mem_interactionsWith h_mem_table

@[circuit_norm]
lemma verifierTable_forall {witness : EnsembleWitness ens}
      {motive : Array F → Prop} :
    (∀ row ∈ witness.verifierTable.table, motive row) ↔ motive (toElements witness.publicInput).toArray := by
  simp [verifierTable]

@[circuit_norm]
lemma verifierTable_flatMap {witness : EnsembleWitness ens}
      {α : Type*} {f : Array F → List α} :
    witness.verifierTable.table.flatMap f = f (toElements witness.publicInput).toArray := by
  simp [verifierTable]

@[circuit_norm]
lemma verifierTable_environment {witness : EnsembleWitness ens} {publicInput : PublicIO F} :
    witness.verifierTable.environment (toElements publicInput).toArray =
      Environment.fromInput publicInput witness.data := rfl

lemma verifierConstraints_iff_verifierTable_constraints {witness : EnsembleWitness ens} :
  ens.VerifierConstraints witness.publicInput witness.data ↔
    witness.verifierTable.Constraints := by
  simp only [Ensemble.VerifierConstraints, Table.Constraints]
  simp only [circuit_norm, Ensemble.verifierTable_constraints, Ensemble.verifierTable_lookups]

lemma verifierAssumptions_iff_verifierTable_assumptions {witness : EnsembleWitness ens} :
  ens.verifier.Assumptions witness.publicInput witness.data ↔
    witness.verifierTable.Assumptions := by
  simp +instances only [circuit_norm, Table.Assumptions,
    Ensemble.verifierTable, Component.RowAssumptions]

lemma verifierSpec_iff_verifierTable_spec {witness : EnsembleWitness ens} :
  ens.VerifierSpec witness.publicInput witness.data ↔
    witness.verifierTable.Spec := by
  simp only [Ensemble.VerifierSpec, Table.Spec]
  simp +instances only [circuit_norm, Ensemble.verifierTable, Component.Spec]

lemma verifierGuarantees_iff_verifierTable_guarantees {witness : EnsembleWitness ens} :
  ens.VerifierGuarantees witness.publicInput witness.data ↔
    witness.verifierTable.Guarantees := by
  simp only [Ensemble.VerifierGuarantees, Table.Guarantees]
  simp only [circuit_norm, Ensemble.verifierTable_interactions]

lemma verifierChannelRequirements_iff {witness : EnsembleWitness ens} {channel : RawChannel F} :
  ens.verifierOperations.ChannelRequirements channel (.fromInput witness.publicInput witness.data) ↔
    witness.verifierTable.ChannelRequirements channel := by
  simp only [Table.ChannelRequirements, circuit_norm, Ensemble.verifierTable_interactions]

lemma verifierConstraints_of_constraints {ens : Ensemble F PublicIO} {witness : EnsembleWitness ens} :
  witness.Constraints →
    ens.VerifierConstraints witness.publicInput witness.data := by
  rw [verifierConstraints_iff_verifierTable_constraints, Constraints, EnsembleWitness.forall_mem_allTables_iff]
  simp_all

lemma verifierAssumptions_of_assumptions {ens : Ensemble F PublicIO} {witness : EnsembleWitness ens} :
  witness.Assumptions →
    ens.verifier.Assumptions witness.publicInput witness.data := by
  rw [verifierAssumptions_iff_verifierTable_assumptions, Assumptions, forall_mem_allTables_iff]
  simp_all

lemma interactionsWith_of_verifier_empty {ens : Ensemble F PublicIO} {witness : EnsembleWitness ens} {channel : RawChannel F}
  (h_verifier_empty : ens.verifier = .empty F PublicIO) :
    witness.interactionsWith channel = witness.tables.flatMap (·.interactionsWith channel) := by
  simp [interactionsWith, allTables, Table.interactionsWith,
    Ensemble.verifierTable_interactionsWith, circuit_norm, h_verifier_empty]

lemma verifierTable_constraints_of_verifier_empty {ens : Ensemble F PublicIO} {witness : EnsembleWitness ens}
  (h_verifier_empty : ens.verifier = .empty F PublicIO) :
    witness.verifierTable.Constraints := by
  rw [← verifierConstraints_iff_verifierTable_constraints]
  simp only [Ensemble.VerifierConstraints, circuit_norm, h_verifier_empty]

lemma verifierTable_assumptions_of_verifier_empty {ens : Ensemble F PublicIO} {witness : EnsembleWitness ens}
  (h_verifier_empty : ens.verifier = .empty F PublicIO) :
    witness.verifierTable.Assumptions := by
  rw [← verifierAssumptions_iff_verifierTable_assumptions]
  simp only [circuit_norm, h_verifier_empty]

/-- The ensemble interactions with a particular channel are balanced. -/
@[circuit_norm]
abbrev BalancedChannel [DecidableEq F] {ens : Ensemble F PublicIO} (witness : EnsembleWitness ens)
    (channel : RawChannel F) : Prop :=
  BalancedInteractions (witness.allTablesWitness.interactionsWith channel)

/-- All ensemble interactions with all ensemble channels are balanced. -/
@[circuit_norm]
def BalancedChannels [DecidableEq F] {ens : Ensemble F PublicIO} (witness : EnsembleWitness ens) : Prop :=
  ∀ channel ∈ ens.channels, BalancedChannel witness channel
end EnsembleWitness

/- ## Soundness, Completeness and related definitions -/

namespace Ensemble
variable [DecidableEq F]

/--
The raw "statement" that a proof about an ensemble makes. Could also be called "relation".

TODO: we currently assume a proof system that already provides us with the fact that the
total interaction length doesn't overflow (as part of `BalancedChannels`).

In practice, however, it's not the total interaction length that is part of a proof,
but rather the length of each individual table. It should be our verifier's job to
verify a bound on the interaction length from the given table lengths.
-/
def Statement (ens : Ensemble F PublicIO) (publicInput : PublicIO F) : Prop :=
  ∃ committed : CommittedEnsembleWitness ens,
    committed.publicInput = publicInput ∧
    let witness := committed.toWitness
    witness.Constraints ∧ witness.BalancedChannels

/-- Soundness: assumptions plus the raw statement imply the spec. -/
def Soundness (ens : Ensemble F PublicIO) (Assumptions Spec : PublicIO F → Prop) : Prop :=
  ∀ publicInput, Assumptions publicInput → ens.Statement publicInput → Spec publicInput

/--
Completeness: assumptions plus the spec implies the raw statement.
-/
def Completeness (ens : Ensemble F PublicIO) (Assumptions Spec : PublicIO F → Prop) : Prop :=
  ∀ publicInput, Assumptions publicInput → Spec publicInput → ens.Statement publicInput
end Ensemble

structure FormalEnsemble (F : Type) [FiniteField F] [DecidableEq F]
    (PublicIO : TypeMap) [ProvableType PublicIO] where
  ensemble : Ensemble F PublicIO
  Assumptions : PublicIO F → Prop := fun _ => True
  Spec : PublicIO F → Prop
  soundness : ensemble.Soundness Assumptions Spec
  -- completeness : ensemble.Completeness Assumptions Spec

namespace Ensemble
variable [DecidableEq F]

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

/-- specs on all tables + verifier spec imply ensemble spec -/
def SpecConsistency (ens : Ensemble F PublicIO) (Spec : PublicIO F → Prop) : Prop :=
  ∀ (witness : EnsembleWitness ens),
    -- TODO maybe we could add balanced channels + channel reqs / grts here as well, to enable you to prove
    -- something at the global level from the max interaction length, like we do below for fibonacci
    -- where we prove the counter does not overflow.
    -- but it's awkward that the public input is not clearly related to the channel, only via the verifier circuit.
    -- which shows that "circuit" probably isn't the best way to model the verifier.
    (∀ table ∈ witness.allTables, table.Spec) →
    Spec witness.publicInput

/-- Ensemble-level assumptions imply the per-table assumptions and verifier assumptions -/
def AssumptionsConsistency (ens : Ensemble F PublicIO) (Assumptions : PublicIO F → Prop) : Prop :=
  ∀ (witness : EnsembleWitness ens),
    Assumptions witness.publicInput →
    witness.Assumptions

theorem soundness_of_tableSoundness_and_specConsistency (ens : Ensemble F PublicIO)
  (Assumptions Spec : PublicIO F → Prop) :
  ens.TableSoundness →
  ens.AssumptionsConsistency Assumptions →
  ens.SpecConsistency Spec →
    ens.Soundness Assumptions Spec := by
  simp only [Soundness, TableSoundness, AssumptionsConsistency, SpecConsistency, Statement,
    forall_exists_index, and_imp]
  intro table_soundness assumptions_consistency spec_consistency
    publicInput assumptions committed publicInput_eq constraints balance
  let witness := committed.toWitness
  simp only [← publicInput_eq] at *
  apply spec_consistency witness
  apply table_soundness witness ?assumptions constraints balance
  exact assumptions_consistency witness assumptions
end Ensemble

/- ## Constructing ensembles -/

namespace Ensemble
/-- Takes verifier and spec from the second ensemble -/
def merge (ens1 ens2 : Ensemble F PublicIO)
    (unique_names : ((ens2.tables ++ ens1.tables).map (·.name)).Nodup) :
    Ensemble F PublicIO :=
  { ens2 with
    tables := ens2.tables ++ ens1.tables,
    unique_names
    channels := ens2.channels ++ ens1.channels }

@[circuit_norm] lemma merge_tables (ens1 ens2 : Ensemble F PublicIO) (unique_names) :
  (ens1.merge ens2 unique_names).tables = ens2.tables ++ ens1.tables := rfl
@[circuit_norm] lemma merge_verifierTable (ens1 ens2 : Ensemble F PublicIO) (unique_names) :
  (ens1.merge ens2 unique_names).verifierTable = ens2.verifierTable := rfl

def addTable (ens : Ensemble F PublicIO) (table : Component F)
    (fresh : table.name ∉ ens.tables.map (·.name)) : Ensemble F PublicIO :=
  { ens with
    tables := table :: ens.tables
    unique_names := by simpa using List.nodup_cons.mpr ⟨fresh, ens.unique_names⟩ }

@[circuit_norm] lemma addTable_tables (ens : Ensemble F PublicIO) (table : Component F) (fresh) :
  (ens.addTable table fresh).tables = table :: ens.tables := rfl
@[circuit_norm] lemma addTable_verifierTable (ens : Ensemble F PublicIO) (table : Component F) (fresh) :
  (ens.addTable table fresh).verifierTable = ens.verifierTable := rfl
@[circuit_norm] lemma addTable_verifier (ens : Ensemble F PublicIO) (table : Component F) (fresh) :
  (ens.addTable table fresh).verifier = ens.verifier := rfl

end Ensemble
end Air.Flat
