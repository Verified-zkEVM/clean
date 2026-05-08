/-
This file defines flat AIR ensembles and what soundness and completeness mean for them.
-/
import Clean.Air.FlatComponent
import Clean.Air.Balance

namespace Air.Flat
variable {F : Type} [Field F]
variable {PublicIO : TypeMap} [ProvableType PublicIO]

structure Ensemble (F : Type) [Field F] (PublicIO : TypeMap) [ProvableType PublicIO] where
  tables : List (Component F)
  channels : List (RawChannel F)
  -- TODO: the verifier shouldn't be treated as a "circuit", and possibly shouldn't even be on here
  verifier : GeneralFormalCircuit F PublicIO unit := .empty F PublicIO
  verifier_length_zero : ∀ pi, verifier.localLength pi = 0 := by
    simp only [GeneralFormalCircuit.empty, circuit_norm]

lemma Ensemble.size_verifier {ens : Ensemble F PublicIO} :
    ens.verifier.size = size PublicIO := by
  simp [GeneralFormalCircuit.size_eq, ens.verifier_length_zero]

structure EnsembleWitness (ens : Ensemble F PublicIO) where
  tables : List (Table F)
  data : ProverData F
  publicInput : PublicIO F
  same_length : ens.tables.length = tables.length
  same_circuits : ∀ i (hi : i < ens.tables.length), ens.tables[i] = tables[i].component
  same_data : ∀ table ∈ tables, table.data = data

/-- it's convenient to define a `Table` for the verifier, to treat them in a unified way -/
def EnsembleWitness.verifierTable {ens : Ensemble F PublicIO} (witness : EnsembleWitness ens) : Table F where
  component := ⟨ ens.verifier ⟩
  width := size PublicIO
  -- it's important that this has one row, which contains the input,
  -- since we want to "run" the verifier once to produce interactions,
  -- and so that constraints etc are actually enforced
  table := [witness.publicInput |> toElements |>.toArray]
  data := witness.data
  uniform_width := by simp

namespace Ensemble
def verifierTable (ens : Ensemble F PublicIO) : Component F :=
  ⟨ ens.verifier ⟩

def allTables (ens : Ensemble F PublicIO) : List (Component F) :=
  ens.verifierTable :: ens.tables

def empty (F : Type) [Field F] (PublicIO : TypeMap) [ProvableType PublicIO] :
  Ensemble F PublicIO where
    tables := []
    channels := []

@[circuit_norm] lemma empty_tables :
  (empty F PublicIO).tables = [] := rfl
@[circuit_norm] lemma empty_channels :
  (empty F PublicIO).channels = [] := rfl
@[circuit_norm] lemma empty_verifier :
  (empty F PublicIO).verifier = .empty F PublicIO := rfl
@[circuit_norm] lemma empty_allTables :
  (empty F PublicIO).allTables = [⟨ .empty F PublicIO ⟩] := rfl
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
end EnsembleWitness

namespace Ensemble
variable {ens : Ensemble F PublicIO}

@[circuit_norm] lemma verifierTable_circuit : ens.verifierTable.circuit = ens.verifier := rfl
@[circuit_norm] lemma verifierTable_input : ens.verifierTable.Input = PublicIO := rfl
@[circuit_norm] lemma verifierTable_output : ens.verifierTable.Output = unit := rfl

@[circuit_norm] lemma mem_allTables_verifierTable:
  ens.verifierTable ∈ ens.allTables := by simp [allTables]

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
  simp only [circuit_norm]

lemma verifierTable_lookups :
  ens.verifierTable.operations.lookups = ens.verifierOperations.lookups := by
  rw [Component.lookups_eq]
  simp only [circuit_norm]

lemma verifierTable_interactions :
  ens.verifierTable.operations.interactions = ens.verifierOperations.interactions := by
  rw [Component.interactions_eq]
  simp only [circuit_norm]

lemma verifierTable_interactionsWith {channel : RawChannel F} :
  ens.verifierTable.operations.interactionsWith channel =
    ens.verifierOperations.interactionsWith channel := by
  rw [Component.interactionsWith_eq]
  simp only [circuit_norm]
end Ensemble

namespace EnsembleWitness
variable {ens : Ensemble F PublicIO}

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
  simp only [circuit_norm, Table.Assumptions,
    Ensemble.verifierTable, Component.Assumptions]

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
  ∃ witness : EnsembleWitness ens,
    witness.publicInput = publicInput ∧
    witness.Constraints ∧
    witness.BalancedChannels

/-- Soundness: assumptions plus the raw statement imply the spec. -/
def Soundness (ens : Ensemble F PublicIO) (Assumptions Spec : PublicIO F → Prop) : Prop :=
  ∀ publicInput, Assumptions publicInput → ens.Statement publicInput → Spec publicInput

/--
Completeness: assumptions plus the spec implies the raw statement.
-/
def Completeness (ens : Ensemble F PublicIO) (Assumptions Spec : PublicIO F → Prop) : Prop :=
  ∀ publicInput, Assumptions publicInput → Spec publicInput → ens.Statement publicInput
end Ensemble

structure FormalEnsemble (F : Type) [Field F] [DecidableEq F]
    (PublicIO : TypeMap) [ProvableType PublicIO] where
  ensemble : Ensemble F PublicIO
  Assumptions : PublicIO F → Prop := fun _ => True
  Spec : PublicIO F → Prop
  soundness : ensemble.Soundness Assumptions Spec
  -- completeness : ensemble.Completeness Assumptions Spec

end Air.Flat
