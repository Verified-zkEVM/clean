module

public import Clean.Air.FlatEnsemble

/-! # Exact physical ensemble accounting

Literal ledger lengths are determined by physical table heights and static circuit
interaction widths. Zero multiplicities, duplicate keys, padding, and the singleton
verifier all contribute to these counts and hence to the characteristic bound.
-/

@[expose] public section

namespace Air.Flat
open Circuit

variable {F : Type} [FiniteField F] {PublicIO : TypeMap} [ProvableType PublicIO]

/-- Number of syntactic interactions with this channel in each physical row. -/
noncomputable def Component.channelWidth (component : Component F) (channel : RawChannel F) : ℕ :=
  (component.operations.interactionsWith channel).length

/-- Every physical row contributes its full circuit width, even if all multiplicities are zero. -/
theorem Table.interactionsWith_length (table : Table F) (channel : RawChannel F) :
    (table.interactionsWith channel).length = table.length * table.component.channelWidth channel := by
  simp only [Table.interactionsWith, List.length_flatMap, Operations.interactionValuesWith, List.length_map]
  simp [Component.channelWidth, Table.length, List.sum_replicate]

namespace EnsembleWitness
variable {ens : Ensemble F PublicIO}

/-- Exact heights of every physical table, with the singleton verifier first. -/
def tableHeights (witness : EnsembleWitness ens) : List ℕ := witness.allTables.map Table.length

/-- Exact per-channel cost, summed over the literal physical inventory. -/
noncomputable def channelOccurrences (witness : EnsembleWitness ens) (channel : RawChannel F) : ℕ :=
  (witness.allTables.map fun table => table.length * table.component.channelWidth channel).sum

/-- The static height-times-width computation is exactly the evaluated ledger's occurrence count. -/
theorem channelOccurrences_eq_length (witness : EnsembleWitness ens) (channel : RawChannel F) :
    witness.channelOccurrences channel = (witness.interactionsWith channel).length := by
  simp only [channelOccurrences, EnsembleWitness.interactionsWith, List.length_flatMap,
    Table.interactionsWith_length]

/-- The verifier contributes exactly one physical row independently of the supplied table list. -/
theorem tableHeights_eq (witness : EnsembleWitness ens) :
    witness.tableHeights = 1 :: witness.tables.map Table.length := rfl

/-- Separate the verifier's exact cost from every provider, instruction and administrative table. -/
theorem channelOccurrences_eq (witness : EnsembleWitness ens) (channel : RawChannel F) :
    witness.channelOccurrences channel = ens.verifierTable.channelWidth channel +
      (witness.tables.map fun table => table.length * table.component.channelWidth channel).sum := by
  simp only [channelOccurrences, EnsembleWitness.allTables, List.map_cons, List.sum_cons,
    EnsembleWitness.verifierTable, Table.length, List.length_singleton, Nat.one_mul]
  rfl

/-- Each table's full contribution is bounded by the total; duplicate tables remain repeated terms. -/
theorem table_cost_le (witness : EnsembleWitness ens) {table : Table F}
    (member : table ∈ witness.allTables) (channel : RawChannel F) :
    table.length * table.component.channelWidth channel ≤ witness.channelOccurrences channel := by
  apply List.single_le_sum (fun _ _ => Nat.zero_le _)
  exact List.mem_map.mpr ⟨table, member, rfl⟩

/-- A table with a real syntactic channel interaction spends at least one occurrence per row.
Multiplicity zero does not make a row free. -/
theorem table_length_le_occurrences (witness : EnsembleWitness ens) {table : Table F}
    (member : table ∈ witness.allTables) (channel : RawChannel F)
    (positive : 0 < table.component.channelWidth channel) :
    table.length ≤ witness.channelOccurrences channel :=
  (Nat.le_mul_of_pos_right _ positive).trans (witness.table_cost_le member channel)

/-- Inclusive physical budgets, measured from actual rows and every registered channel. -/
def PhysicalFits (witness : EnsembleWitness ens) (rows occurrences : ℕ) : Prop :=
  (∀ height ∈ witness.tableHeights, height ≤ rows) ∧
    ∀ channel ∈ ens.channels, witness.channelOccurrences channel ≤ occurrences

/-- Clean's finite-characteristic capacity condition, over the complete registered-channel list. -/
def ChannelCapacity (witness : EnsembleWitness ens) (characteristic : ℕ) : Prop :=
  ∀ channel ∈ ens.channels, witness.channelOccurrences channel < characteristic

/-- The shared capacity interface is precisely the existing raw ledger bound. -/
theorem channelCapacity_iff (witness : EnsembleWitness ens) (characteristic : ℕ) :
    witness.ChannelCapacity characteristic ↔
      ∀ channel ∈ ens.channels, (witness.interactionsWith channel).length < characteristic := by
  simp only [ChannelCapacity, channelOccurrences_eq_length]

/-- Inclusive resource ceilings below the characteristic suffice for Clean's occurrence bound. -/
theorem PhysicalFits.capacity {witness : EnsembleWitness ens} {rows occurrences characteristic : ℕ}
    (fits : witness.PhysicalFits rows occurrences) (small : occurrences < characteristic) :
    witness.ChannelCapacity characteristic :=
  fun channel member => Nat.lt_of_le_of_lt (fits.2 channel member) small

/-- Accepted witnesses already satisfy the exact all-channel finite-field capacity condition. -/
theorem channelCapacity_of_balanced [DecidableEq F] (witness : EnsembleWitness ens)
    (balanced : witness.BalancedChannels) (positive : 0 < ringChar F) :
    witness.ChannelCapacity (ringChar F) := by
  intro channel member
  rw [channelOccurrences_eq_length]
  exact (balanced channel member).1.resolve_right (Nat.ne_of_gt positive)

/-- Adding raw rows has additive cost; field cancellation cannot recover spent occurrence capacity. -/
theorem table_cost_append (component : Component F) (channel : RawChannel F) (left right : ℕ) :
    (left + right) * component.channelWidth channel =
      left * component.channelWidth channel + right * component.channelWidth channel := Nat.add_mul ..

/-- An exact per-table expansion and its verifier cost suffice for physical construction bounds.
This is an arithmetic construction lemma, not an added semantic-domain premise. -/
theorem physicalFits_iff (witness : EnsembleWitness ens) (rows occurrences : ℕ) :
    witness.PhysicalFits rows occurrences ↔
      1 ≤ rows ∧ (∀ table ∈ witness.tables, table.length ≤ rows) ∧
        ∀ channel ∈ ens.channels, ens.verifierTable.channelWidth channel +
          (witness.tables.map fun table => table.length * table.component.channelWidth channel).sum ≤ occurrences := by
  simp only [PhysicalFits, tableHeights_eq, List.mem_cons, List.mem_map,
    forall_eq_or_imp, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
    channelOccurrences_eq, and_assoc]

end EnsembleWitness

end Air.Flat
