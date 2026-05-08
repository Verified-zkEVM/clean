/-
Playground for channels using Fibonacci8 as an example

Goal - use three channels:
- a "bytes" channel that enables range checks using lookups into a table containing 0,...,255
- an "add8" channel that implements 8-bit addition as a standalone "chip" / table
- a "fibonacci" channel that that maintains state of the fibonacci table

Prove e2e soundness and completeness of the table ensemble.
-/
import Clean.Circuit
import Clean.Circuit.Extensions
import Clean.Gadgets.Addition8.Theorems
import Clean.Air.FlatEnsemble
open ByteUtils (mod256 floorDiv256)
open Gadgets.Addition8 (Theorems.soundness Theorems.completeness_bool Theorems.completeness_add)
open Air.Flat

section
variable {F : Type} [Field F]
variable {Input Output Message : TypeMap} [ProvableType Input] [ProvableType Output] [ProvableType Message]
variable {PublicIO : TypeMap} [ProvableType PublicIO]

-- define what global soundness means for an ensemble of circuits/tables and channels

-- table contains the concrete values on which we expect constraints to hold
-- which also defines what concrete interactions are contained in each channel

-- tables need to be instantiated with a concrete circuit, not a family of circuits
-- this is achieved for any FormalCircuit* by witnessing the inputs and plugging them in

-- infrastructure for iteratively adding tables to an ensemble such that we can always fill in
-- the next table's guarantees

/--
Relaxed version of BalancedChannel that works with ensembles that aren't fully specified yet,
where we assume our interactions are a subset of some larger list which is balanced.

designed to be used for proving soundness by adding one table after another.
-/
def PartialBalancedChannel [DecidableEq F] (tables : Tables F) (channel : RawChannel F) : Prop :=
  -- `extraInteractions` represents the unknown interactions from tables added later
  ∃ extraInteractions : List (Interaction F),
    -- the total of known + unknown interactions is balanced for each "finished" channel
    BalancedInteractions (tables.interactionsWith channel ++ extraInteractions) ∧
    -- the extra interactions are with the same channel.
    (∀ i ∈ extraInteractions, i.channel = channel) ∧
    -- additionally, we _assume_ that either the requirements on future interactions hold unconditionally,
    -- or that known interactions do not assume guarantees on the same channel.
    -- this restricts the order in which tables can be added. essentially, it requires that the `extraTables`
    -- that create the `extraInteractions` satisfy `OrderedChannelLt channel tables extraTables` (see below);
    -- and it's the missing piece when reasoning about requirements and guarantees on the full list of balanced interactions.
    (channel ∉ tables.tables.flatMap (·.channelsWithGuarantees) ∨ ∀ i ∈ extraInteractions, i.Requirements tables.data)

/-- Partial balance is trivially weaker than balance -/
lemma partialBalancedChannel_of_balancedInteractions [DecidableEq F] {tables : Tables F} {channel : RawChannel F} :
    BalancedInteractions (tables.interactionsWith channel) → PartialBalancedChannel tables channel := by
  intro balanced
  use []
  simp [balanced]

-- TODO deduplicate and add to Basic
attribute [circuit_norm] forall_eq_or_imp List.mem_flatMap List.mem_map exists_exists_and_eq_and
  not_exists not_and List.Subset.refl List.subset_append_of_subset_left List.subset_append_of_subset_right
  List.flatMap_append List.mem_append not_or not_exists not_and not_false_eq_true
  List.flatMap_cons List.append_subset

/--
A channel is "ordered" in a list of tables if all the tables that add requirements
come before all the tables that add guarantees for the channel.

Note that the order is reversed compared to the intended hierarchy, this is just because it's the
more natural direction for doing List.cons induction, so we think of a cons'd element as coming
after the rest of the list.
-/
def OrderedChannel (channel : RawChannel F) (tables : List (Component F)) : Prop :=
  ∀ i (hi : i < tables.length) j (hj : j < tables.length),
    channel ∈ tables[i].circuit.channelsWithGuarantees →
    channel ∈ tables[j].circuit.channelsWithRequirements →
      i < j

@[circuit_norm]
lemma orderedChannel_nil (channel : RawChannel F) : OrderedChannel channel [] := by
  simp [OrderedChannel]

@[circuit_norm]
abbrev OrderedChannelRefl (channel : RawChannel F) (table : Component F) : Prop :=
  channel ∉ table.circuit.channelsWithGuarantees ∨ channel ∉ table.circuit.channelsWithRequirements

abbrev OrderedChannelLt (channel : RawChannel F) (tables₁ tables₂ : List (Component F)) : Prop :=
  channel ∉ tables₁.flatMap (·.circuit.channelsWithGuarantees) ∨ channel ∉ tables₂.flatMap (·.circuit.channelsWithRequirements)

@[circuit_norm]
lemma orderedChannelLt_nil_right (channel : RawChannel F) (tables : List (Component F)) :
    OrderedChannelLt channel tables [] := by simp [OrderedChannelLt]

@[circuit_norm]
lemma orderedChannelLt_nil_left (channel : RawChannel F) (tables : List (Component F)) :
    OrderedChannelLt channel [] tables := by simp [OrderedChannelLt]

@[circuit_norm]
lemma orderedChannelLt_cons_right (channel : RawChannel F) {table : Component F} {ts ss : List (Component F)} :
  OrderedChannelLt channel ss (table :: ts) ↔
    (channel ∉ ss.flatMap (·.circuit.channelsWithGuarantees) ∨ channel ∉ table.circuit.channelsWithRequirements) ∧
    OrderedChannelLt channel ss ts := by
  simp [OrderedChannelLt, circuit_norm]
  tauto

@[circuit_norm]
lemma orderedChannelLt_append_left {channel : RawChannel F} {ts₁ ts₂ ss : List (Component F)} :
  OrderedChannelLt channel (ts₁ ++ ts₂) ss ↔
    OrderedChannelLt channel ts₁ ss ∧ OrderedChannelLt channel ts₂ ss := by
  simp only [OrderedChannelLt, circuit_norm]
  tauto

@[circuit_norm]
lemma orderedChannelLt_append_right {channel : RawChannel F} {ts ss₁ ss₂ : List (Component F)} :
  OrderedChannelLt channel ts (ss₁ ++ ss₂) ↔
    OrderedChannelLt channel ts ss₁ ∧ OrderedChannelLt channel ts ss₂ := by
  simp only [OrderedChannelLt, circuit_norm]
  tauto

@[circuit_norm]
lemma orderedChannel_cons (table : Component F) (tables : List (Component F)) (channel : RawChannel F) :
  OrderedChannel channel (table :: tables) ↔
  OrderedChannelRefl channel table ∧ OrderedChannel channel tables ∧ OrderedChannelLt channel tables [table] := by
  simp only [circuit_norm, OrderedChannel, OrderedChannelRefl, List.length_cons]
  -- Intuition: The `i < j` conclusion of `OrderedChannel` falsifies the hypotheses if `j = 0`,
  -- so apart from the "induction hypothesis" where `i, j > 0`, we get two distinct statements by specializing to `i = 0` and `i > 0` respectively
  simp only [Nat.forall_lt_succ_left', List.getElem_cons_zero, List.getElem_cons_succ]
  simp only [lt_self_iff_false, imp_false, lt_add_iff_pos_left, Order.lt_add_one_iff, zero_le,
    implies_true, and_true, not_lt_zero, Order.add_one_le_iff]
  rw [forall₂_and, List.forall_mem_iff_getElem, or_iff_not_imp_left, or_iff_not_imp_left]
  push_neg
  simp only [exists_imp]
  tauto

lemma orderedChannel_singleton_iff (table : Component F) (channel : RawChannel F) :
    OrderedChannel channel [table] ↔ OrderedChannelRefl channel table := by
  simp [circuit_norm]

/-- Alternative, and sometimes more convenient, formulation of `OrderedChannel` -/
lemma orderedChannel_iff (tables : List (Component F)) (channel : RawChannel F) :
  OrderedChannel channel tables ↔
    (∀ t ∈ tables, OrderedChannelRefl channel t) ∧
    ∀ ts ss, tables = ts ++ ss → OrderedChannelLt channel ss ts := by
  simp [OrderedChannel, OrderedChannelLt, OrderedChannelRefl]
  constructor
  · intro ordered_channel
    constructor
    · simp only [List.forall_mem_iff_getElem]
      intro i hi
      specialize ordered_channel i hi i hi
      simp at ordered_channel
      tauto
    intro ts ss h_append
    subst h_append
    simp only [List.length_append] at ordered_channel
    simp only [List.forall_mem_iff_getElem, or_iff_not_imp_left]
    push_neg
    rintro ⟨ i, hi, grts ⟩ j hj reqs
    specialize ordered_channel (ts.length + i) (by linarith) j (by linarith)
    rw [List.getElem_append_right (by omega), List.getElem_append_left (by omega)] at ordered_channel
    have : ¬(ts.length + i < j) := by omega
    apply this
    apply ordered_channel ?_ reqs
    have : ts.length + i - ts.length = i := by simp
    convert grts
  intro ordered_channel' i hi j hj
  simp only [List.forall_mem_iff_getElem] at ordered_channel'
  suffices j = i ∨ j < i →
    channel ∉ tables[i].circuit.channelsWithGuarantees ∨
    channel ∉ tables[j].circuit.channelsWithRequirements by grind
  rintro h
  rcases h with rfl | j_lt_i
  · exact ordered_channel'.left j hi
  have j_succ_lt : j + 1 < tables.length := by linarith
  replace ordered_channel' := ordered_channel'.right (tables.take (j + 1)) (tables.drop (j + 1)) (by simp)
  simp at ordered_channel'
  rcases ordered_channel' with no_grts | no_reqs
  · left
    specialize no_grts (i - (j + 1)) (by omega)
    rw [List.getElem_drop] at no_grts
    have : i = j + 1 + (i - (j + 1)) := by omega
    convert no_grts
  · right
    specialize no_reqs j (by omega) hj
    rw [List.getElem_take] at no_reqs
    exact no_reqs

/-- "Merge sort" for ordered channels -/
@[circuit_norm]
lemma orderedChannel_append (ts ss : List (Component F)) (channel : RawChannel F) :
  OrderedChannel channel (ts ++ ss) ↔
    OrderedChannel channel ts ∧ OrderedChannel channel ss ∧ OrderedChannelLt channel ss ts := by
  simp only [orderedChannel_iff]
  constructor
  · rintro ⟨ordered_refl, ordered_split⟩
    simp_all
    constructor
    · intro ts' ss' h_append
      have hlt := ordered_split ts' (ss' ++ ss) (by simp [h_append])
      rw [orderedChannelLt_append_left] at hlt
      tauto
    · intro ts' ss' h_append
      have hlt := ordered_split (ts ++ ts') ss' (by simp [h_append])
      rw [orderedChannelLt_append_right] at hlt
      tauto
  · simp only [List.append_eq_append_iff, ←exists_or]
    grind

/-- A sufficient condition for ordered channel is that there are no requirements added -/
lemma orderedChannel_of_no_requirements {channel : RawChannel F} {tables : List (Component F)} :
  (∀ table ∈ tables, channel ∉ table.circuit.channelsWithRequirements) →
    OrderedChannel channel tables := by
  intro reqs
  rw [orderedChannel_iff]
  simp_all [OrderedChannelRefl, OrderedChannelLt]

/-- A sufficient condition for ordered channel is that there are no guarantees added -/
lemma orderedChannel_of_no_guarantees {channel : RawChannel F} {tables : List (Component F)} :
  (∀ table ∈ tables, channel ∉ table.circuit.channelsWithGuarantees) →
    OrderedChannel channel tables := by
  intro grts
  rw [orderedChannel_iff]
  simp_all [OrderedChannelRefl, OrderedChannelLt]

/-- A sufficient condition for ordered channel lt is that there are no requirements added in the second list -/
lemma orderedChannelLt_of_no_requirements {channel : RawChannel F} {ts ss : List (Component F)} :
  (∀ table ∈ ts, channel ∉ table.circuit.channelsWithRequirements) →
    OrderedChannelLt channel ss ts := by
  intro no_reqs
  simp_all [OrderedChannelLt]

/-- A sufficient condition for ordered channel lt is that there are no guarantees added in the first list -/
lemma orderedChannelLt_of_no_guarantees {channel : RawChannel F} {ts ss : List (Component F)} :
  (∀ table ∈ ss, channel ∉ table.circuit.channelsWithGuarantees) →
    OrderedChannelLt channel ss ts := by
  intro no_grts
  simp_all [OrderedChannelLt]

/--
For ordered channels, we can always instantiate partial balance at an initial sublist.
-/
theorem partialBalancedChannel_of_cons_of_orderedChannelLt [DecidableEq F]
  {table : Table F} {tables : Tables F} (same_data : table.data = tables.data)
  {channel : RawChannel F} :
  PartialBalancedChannel (.cons table tables same_data) channel →
  OrderedChannelLt channel tables.components [table.component] →
    PartialBalancedChannel tables channel := by
  rintro ⟨ extraInteractions, balanced, same_channel, extra_reqs_or_no_grts ⟩ not_in_reqs_or
  use table.interactionsWith channel ++ extraInteractions
  simp only [circuit_norm] at *
  simp [or_imp] at ⊢ not_in_reqs_or extra_reqs_or_no_grts
  constructor
  · apply balancedInteractions_of_perm balanced
    grw [List.perm_append_comm_assoc]
  constructor
  · intro a
    use Table.channel_eq_of_mem_interactionsWith
    exact same_channel a
  rw [forall_and]
  rcases not_in_reqs_or with channel_not_in_grts | channel_not_in_reqs
  · simp_all
  rcases extra_reqs_or_no_grts with no_grts | extra_reqs
  · simp_all
  · right
    have channel_reqs := table.requirements_of_not_mem channel_not_in_reqs
    rw [Table.channelRequirements_iff_forall, same_data] at channel_reqs
    exact ⟨ channel_reqs, extra_reqs ⟩

/--
For ordered channels, we can always instantiate partial balance at an initial sublist.
-/
lemma partialBalancedChannel_of_cons_of_orderedChannel [DecidableEq F]
  {table : Table F} {tables : Tables F} (same_data : table.data = tables.data)
  {channel : RawChannel F} :
  PartialBalancedChannel (tables.cons table same_data) channel →
  OrderedChannel channel (table.component :: tables.components) →
    PartialBalancedChannel tables channel := by
  intro partial_balance ordered_channel
  apply partialBalancedChannel_of_cons_of_orderedChannelLt same_data partial_balance
  simp_all [circuit_norm]

/--
The significance of `OrderedChannel` is that it lets us prove soundness
on a list of tables by induction. This lemma captures the main step.
-/
lemma guarantees_of_requirements_cons [DecidableEq F]
  -- given a list of tables, and one additional table
  {table : Table F} {tables : Tables F} (same_data : table.data = tables.data)
  -- and a channel that is consistent, ordered on the new table, and partially balanced on the combined tables
  {channel : RawChannel F} [channel.Consistent] :
  OrderedChannelRefl channel table.component →
  PartialBalancedChannel (tables.cons table same_data) channel →
  -- the channel requirements on the old tables imply guarantees on the new table
  (∀ table ∈ tables.tables, table.ChannelRequirements channel) →
    table.ChannelGuarantees channel := by
  rintro ordered_channel partial_balance ih
  /-
  thanks to ordered channel, we know that channel cannot add _both_ grts and reqs for the new table.
  1) if the channel does not add grts, we're done as the grts are trivially satisifed.
  2) if the channel does not add reqs, we can prove that _all_ reqs of that channel are satisfied.
      using consistent channels, we conclude the channel's guarantees.
  -/
  simp only [circuit_norm] at ordered_channel
  rcases ordered_channel with grts | reqs
  · exact table.guarantees_of_not_mem grts
  replace reqs := table.requirements_of_not_mem reqs
  -- there's a special case to discard where the guarantees are trivially satisfied
  rcases partial_balance with ⟨ extraInteractions, balanced, same_channel, grts | extra_reqs ⟩
  · simp only [circuit_norm] at grts
    exact table.guarantees_of_not_mem grts.left
  -- now, to prove this table's channel guarantees, we show guarantees on _all_ channel interactions (that we know are balanced)
  set channelInteractions := (tables.cons table same_data).interactionsWith channel ++ extraInteractions
  have subset_channelInteractions : table.interactionsWith channel ⊆ channelInteractions := by
    simp only [channelInteractions, circuit_norm]
  suffices all_grts : ∀ i ∈ channelInteractions, i.Guarantees tables.data by
    rw [Table.channelGuarantees_iff_forall, same_data]
    intro i hi
    exact all_grts i (subset_channelInteractions hi)
  -- this works since we can prove all channel _requirements_
  -- relies on `ordered_channels` and `partial_balance` (the extra interactions assumption)
  have all_reqs : ∀ i ∈ channelInteractions, i.channel = channel ∧ i.Requirements tables.data := by
    simp only [channelInteractions, circuit_norm]
    intro i h_mem
    rcases h_mem with h_mem_table | h_mem_old | h_mem_extra
    -- for the new table, we can just use the requirements assumption
    · rw [Table.channelRequirements_iff_forall, same_data] at reqs
      use table.channel_eq_of_mem_interactionsWith h_mem_table
      exact reqs _ h_mem_table
    · obtain ⟨ table', h_table', i_mem_table ⟩ := h_mem_old
      simp only [Table.channelRequirements_iff_forall] at ih
      specialize ih table' h_table'
      simp only [tables.same_data _ h_table'] at ih
      use table'.channel_eq_of_mem_interactionsWith i_mem_table
      exact ih i i_mem_table
    · exact ⟨ same_channel i h_mem_extra, extra_reqs i h_mem_extra ⟩
  -- consistent channels goes from requirements to guarantees
  -- uses `consistent_channels` and `partial_balance`
  apply ‹channel.Consistent›.consistent channelInteractions tables.data balanced all_reqs

/--
Partial balance can be specialized to a sublist (= part of a permutation),
as long as none of the extra tables add requirements.
-/
lemma partialBalancedChannel_of_sublist [DecidableEq F] {subtables tables : Tables F} {channel : RawChannel F} :
  PartialBalancedChannel tables channel →
  (∃ otherTables, tables.tables.Perm (subtables.tables ++ otherTables) ∧
    ∀ table ∈ otherTables, channel ∉ table.channelsWithRequirements) →
    PartialBalancedChannel subtables channel := by
  rintro ⟨ extraInteractions, balanced, same_channel, no_grts_or_extra_reqs ⟩ subset_tables
  obtain ⟨ otherTables, perm, otherReqs ⟩ := subset_tables
  by_cases subtables_empty : subtables.tables = []
  · simp [subtables_empty, circuit_norm, PartialBalancedChannel, Tables.interactionsWith]
    use []
    simp [BalancedInteractions, balanceOf]
    omega
  have subtables_subset : subtables.tables ⊆ tables.tables := by
    have p := perm.symm.subset
    simp_all
  have subtables_data : subtables.data = tables.data := by
    have ⟨ one_subtable, h_one_subtable ⟩ : ∃ table, table ∈ subtables.tables := by
      apply List.exists_mem_of_ne_nil
      simp [subtables_empty]
    rw [← subtables.same_data _ h_one_subtable,
      tables.same_data _ (subtables_subset h_one_subtable)]
  use otherTables.flatMap (·.interactionsWith channel) ++ extraInteractions
  simp_all only
  constructor; swap
  -- TODO this half is surprisingly long/annoying, maybe missing helper lemmas
  · simp [circuit_norm, or_imp]
    constructor
    · intro i
      use fun _ _ => Table.channel_eq_of_mem_interactionsWith
      exact same_channel i
    rcases no_grts_or_extra_reqs with no_grts | extra_reqs
    · simp only [List.mem_flatMap, not_exists, not_and] at no_grts
      left
      intro t ht
      exact no_grts _ (subtables_subset ht)
    right
    intro i
    constructor; swap
    · exact extra_reqs i
    intro t ht
    revert i
    have ht' : t ∈ tables.tables := by
      apply perm.symm.subset
      simp [ht]
    rw [← tables.same_data _ ht', ← Table.channelRequirements_iff_forall]
    apply Table.requirements_of_not_mem
    exact otherReqs _ ht
  -- balance
  apply balancedInteractions_of_perm balanced
  simp only [Tables.interactionsWith]
  grw [← List.append_assoc, List.perm_append_right_iff, ← List.flatMap_append, perm.flatMap]
  exact fun _ _ => List.Perm.refl _

/--
The argument of `guarantees_of_requirements_cons`
also works for adding multiple new tables, if we make the assumption a bit stronger:
We can no longer continue to introduce guarantees for the channel.

This is relevant later when we add VM channels on top of an already finished, sound ensemble.
-/
lemma guarantees_of_requirements_append [DecidableEq F]
  -- given two lists of tables
  {ts ss : Tables F} (same_data : ts.data = ss.data)
  -- and a channel that is consistent, _doesn't add requirements_ on the new tables,
  -- and is partially balanced on the combined tables
  {channel : RawChannel F} [channel.Consistent] :
  (∀ table ∈ ts.tables, channel ∉ table.component.circuit.channelsWithRequirements) →
  PartialBalancedChannel (ts.append ss same_data) channel →
  -- the channel requirements on the old tables imply guarantees on the new tables
  (∀ table ∈ ss.tables, table.ChannelRequirements channel) →
    ∀ table ∈ ts.tables, table.ChannelGuarantees channel := by
  -- we show that for each (t, ss) pair, the assumptions of `*_cons` hold
  rintro reqs partial_balance ih table h_table
  have same_data' : table.data = ss.data := by
    rw [ts.same_data _ h_table, same_data]
  apply guarantees_of_requirements_cons (tables := ss) same_data' ?_ ?_ ih
  · right; exact reqs _ h_table
  -- get partial balance by sublist/permutation argument
  apply partialBalancedChannel_of_sublist partial_balance
  obtain ⟨ i, hi, h' ⟩ := List.getElem_of_mem h_table
  symm at h'; subst h'
  use ts.tables.eraseIdx i
  constructor; swap
  · intro t' ht'
    apply reqs _ (List.mem_of_mem_eraseIdx ht')
  simp [circuit_norm]
  grw [List.perm_append_comm, List.perm_cons_append_cons _ List.perm_rfl,
    List.perm_append_left_iff, List.perm_comm]
  apply List.getElem_cons_eraseIdx_perm

/-- Helper lemma that uses circuit soundness, to strengthen guarantees to include requirements -/
lemma iff_guarantees_of_constraints {table : Table F} {finished : List (RawChannel F)} :
  table.Assumptions →
  table.Constraints →
  table.component.circuit.channelsWithGuarantees ⊆ finished →
  ((table.Spec ∧ ∀ channel ∈ finished, table.ChannelGuarantees channel ∧ table.ChannelRequirements channel) ↔
    ∀ channel ∈ finished, table.ChannelGuarantees channel) := by
  intro assumptions constraints subset_finished
  constructor; simp_all
  intro grts
  have all_grts : table.Guarantees := by
    rw [Table.guarantees_iff_channelGuarantees]
    intro channel h_channel
    exact grts _ (subset_finished h_channel)
  -- constraints ∧ guarantees → requirements → channelRequirements
  have ⟨ spec, all_reqs ⟩ := table.weakSoundness assumptions constraints all_grts
  use spec
  intro channel h_channel
  exact ⟨ grts _ h_channel, table.channelRequirements_of_requirements all_reqs ⟩

/--
`SoundChannels` combines three assumptions on the channels used by a list of tables,
that together are

- sufficient for proving soundness of just these tables
- help with proving soundness of additional tables, by handling the guarantees of finished channels.

Notably, `SoundChannels` can be stated and proved entirely (and easily) from the knowledge of each table's
`channelsWithGuarantees` and `channelsWithRequirements`.

In practice, this property holds on ensembles that only use channels in lookup fashion.

Note: In the presence of "VM-like" channels, where a circuit both pushes and pulls to the same channel,
`SoundChannels` does not hold for _any_ list of channels:
- VM channels don't satisfy `OrderedChannel`, so they disqualify for the `finished` list.
- Consequently, the first property `channelsWithGuarantees ⊆ finished` is violated for VM tables, since
  VM channels do belong to the `channelsWithGuarantees`.
However, in that scenario, it is still useful to establish `SoundChannels` on the subset of non-VM tables.
-/
@[circuit_norm]
def SoundChannels [DecidableEq F] (tables : List (Component F)) (finished : List (RawChannel F)) : Prop :=
  (∀ table ∈ tables, table.circuit.channelsWithGuarantees ⊆ finished) ∧
  (∀ channel ∈ finished, OrderedChannel channel tables) ∧
  ∀ channel ∈ finished, channel.Consistent

/-- `SoundChannels` lets us prove a soundness theorem. -/
theorem spec_and_guarantees_of_soundChannels [DecidableEq F] {witness : Tables F} {finished : List (RawChannel F)} :
  SoundChannels (witness.tables.map (·.component)) finished →
  -- constraints + partial balance
  witness.Assumptions →
  witness.Constraints →
  (∀ channel ∈ finished, PartialBalancedChannel witness channel) →
    -- implies the spec, and the guarantees and requirements on all finished channels
    ∀ table ∈ witness.tables, table.Spec ∧ ∀ channel ∈ finished,
    table.ChannelGuarantees channel ∧ table.ChannelRequirements channel := by
  -- by induction on the tables
  rintro ⟨ subset_finished, ordered_channels, consistent_channels ⟩ assumptions constraints partial_balance
  induction witness using Tables.induct
  · intro _ h_table; nomatch h_table
  -- induction step
  rename_i table tables same_data ih
  -- first, we use the IH
  have partial_balance' c hc := partialBalancedChannel_of_cons_of_orderedChannel
    same_data (partial_balance c hc) (ordered_channels c hc)
  simp only [Tables.Assumptions, Tables.Constraints, circuit_norm] at *
  simp only [forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] at *
  specialize ih subset_finished.right (fun c hc => (ordered_channels c hc).right.left)
    assumptions.right constraints.right partial_balance'
  constructor; swap
  · exact ih
  -- it's enough to prove guarantees of all channels, since they + constraints imply requirements
  rw [iff_guarantees_of_constraints assumptions.left constraints.left subset_finished.left]
  -- the rest is just applying `guarantees_of_requirements_cons`
  intro channel h_channel
  have : channel.Consistent := consistent_channels _ h_channel
  have orderedChannelRefl : OrderedChannelRefl channel table.component := by
    simp only [circuit_norm, ordered_channels channel h_channel]
  apply guarantees_of_requirements_cons same_data
    orderedChannelRefl (partial_balance channel h_channel)
  intro t ht
  exact (ih t ht).right _ h_channel |>.right

/-- `SoundChannels` is strictly increasing: you can make the finished list bigger by any consistent channels -/
lemma soundChannels_of_soundChannels_subset [DecidableEq F] {tables : List (Component F)} {finished finished' : List (RawChannel F)} :
  SoundChannels tables finished →
  finished ⊆ finished' →
  (∀ channel ∈ finished', channel.Consistent) →
    SoundChannels tables finished' := by
  rintro ⟨ subset_finished, ordered_channels, consistent_channels ⟩ finished'_subset finished'_consistent
  constructor
  · intro table h_table
    specialize subset_finished table h_table
    trans finished <;> assumption
  constructor; swap
  · assumption
  intro channel h_channel
  by_cases h_channel_finished : channel ∈ finished
  · apply ordered_channels channel h_channel_finished
  apply orderedChannel_of_no_guarantees
  intro table h_table mem_grts
  apply h_channel_finished
  exact subset_finished table h_table mem_grts

/-- You can add one channel to the finished list and preserve `SoundChannels` -/
lemma soundChannels_cons_of_soundChannels [DecidableEq F] {tables : List (Component F)}
  {finished : List (RawChannel F)} {channel : RawChannel F} [channel.Consistent] :
  SoundChannels tables finished →
    SoundChannels tables (channel :: finished) := by
  intro sound_channels
  apply soundChannels_of_soundChannels_subset sound_channels
  · simp
  simp_all [SoundChannels]

namespace Air.Flat
namespace EnsembleWitness
@[circuit_norm]
abbrev PartialBalancedChannels [DecidableEq F] {ens : Ensemble F PublicIO} (finished : List (RawChannel F))
    (witness : EnsembleWitness ens) : Prop :=
  ∀ channel ∈ finished, PartialBalancedChannel witness channel
end EnsembleWitness

namespace Ensemble
/-- Partial balanced channel is trivially weaker than balanced channel -/
lemma partialBalancedChannel_of_balancedChannel [DecidableEq F] {ens : Ensemble F PublicIO}
    {witness : EnsembleWitness ens} (channel : RawChannel F) :
  witness.BalancedChannel channel →
    PartialBalancedChannel witness channel := by
  intro balanced
  use []
  simp_all [EnsembleWitness.BalancedChannel]

@[circuit_norm]
abbrev SoundChannels [DecidableEq F] (ens : Ensemble F PublicIO) (finished : List (RawChannel F)) : Prop :=
  _root_.SoundChannels ens.allTables finished

@[circuit_norm]
abbrev OrderedChannels (ens : Ensemble F PublicIO) (finished : List (RawChannel F)) : Prop :=
  ∀ channel ∈ finished, OrderedChannel channel ens.allTables

/--
Main result of this section:
`SoundChannels` (an easily checkable property) implies
`TableSoundness`, a complex ensemble-level soundness statement.
-/
theorem tableSoundness_of_soundChannels [DecidableEq F] {ens : Ensemble F PublicIO} :
  (∃ finished : List (RawChannel F), finished ⊆ ens.channels ∧ ens.SoundChannels finished) →
    ens.TableSoundness := by
  intro ⟨ finished, finished_subset, soundChannels ⟩ witness assumptions constraints balance table h_table
  have partial_balance : ∀ channel ∈ finished, PartialBalancedChannel witness channel := by
    intro channel h_channel
    apply partialBalancedChannel_of_balancedChannel
    exact balance _ <| finished_subset h_channel
  apply spec_and_guarantees_of_soundChannels ?soundChannels ?assumptions ?constraints
    partial_balance table h_table |>.left
  <;> (simp only [circuit_norm]; assumption)

/-- Empty ensemble satisfies SoundChannels -/
theorem empty_soundChannels [DecidableEq F] : (empty F PublicIO).SoundChannels [] := by
  simp only [circuit_norm]

/-- Empty ensemble satisfies TableSoundness -/
theorem empty_tableSoundness [DecidableEq F] : (empty F PublicIO).TableSoundness :=
  tableSoundness_of_soundChannels ⟨ [], List.Subset.refl [], empty_soundChannels ⟩

-- adding one table to a SoundChannels ensemble preserves SoundChannels under some
-- easy-to-prove assumptions on what channels the new table uses
theorem orderedChannels_of_soundChannels_addTable [DecidableEq F] (ens : Ensemble F PublicIO)
  (table : Component F) {finished : List (RawChannel F)} :
    -- given a sound channels ensemble with empty verifier,
    ens.SoundChannels finished →
    ens.verifier = .empty F PublicIO →
    -- assuming that the new table's channelsWithGuarantees are all finished
    table.circuit.channelsWithGuarantees ⊆ finished →
    -- and that the table's channelsWithRequirements contain none of the finished ones
    -- (so that we don't get new requirements to prove)
    (∀ channel ∈ finished, channel ∉ table.circuit.channelsWithRequirements) →
    -- the ensemble with the new table also satisfies SoundChannels!
    (ens.addTable table).OrderedChannels finished := by
  intro h_sound verifier_empty grts_subset_finished reqs_disjoint_finished channel h_channel
  -- we need to make use of soundness of the original ensemble; that'll give us most of what we need
  simp only [circuit_norm, allTables, verifier_empty] at h_sound ⊢
  -- proof is a trivial combination of the hypotheses
  simp_all

theorem orderedChannels_of_soundChannels_merge [DecidableEq F] (ens1 ens2 : Ensemble F PublicIO)
  {finished : List (RawChannel F)} :
    -- given a sound channels ensemble with empty verifier,
    ens1.SoundChannels finished →
    ens1.verifier = .empty F PublicIO →
    -- assuming that the new tables' channelsWithRequirements contain none of the finished channels
    (∀ channel ∈ finished, channel ∉ ens2.channelsWithRequirements) →
    -- the merged ensemble with the new table satisfies OrderedChannels!
    (ens1.merge ens2).OrderedChannels finished := by
  intro h_sound verifier_empty reqs_disjoint_finished channel h_channel
  simp only [circuit_norm, allTables, verifier_empty] at h_sound ⊢
  simp only [channelsWithRequirements_eq_verifier_append, circuit_norm] at reqs_disjoint_finished
  simp_all only [not_false_eq_true, or_true, true_and, and_true]
  constructor
  · apply orderedChannel_of_no_requirements
    simp_all
  · apply orderedChannelLt_of_no_requirements
    simp_all

theorem soundChannels_markFinished [DecidableEq F] (ens : Ensemble F PublicIO)
    -- given a sound channels ensemble with a list of finished channels
    {finished : List (RawChannel F)} (h_sound : ens.SoundChannels finished)
    -- and given a new consistent channel to mark as finished
    (channel : RawChannel F) [channel.Consistent] :
    -- the ensemble also satisfies SoundChannels including the new channel in the finished list
    ens.SoundChannels (channel :: finished) := by
  exact soundChannels_cons_of_soundChannels h_sound
end Ensemble

structure SoundEnsemble (F : Type) [Field F] [DecidableEq F] (PublicIO : TypeMap) [ProvableType PublicIO]
    extends ensemble : Ensemble F PublicIO where
  finished : List (RawChannel F)
  finished_consistent : ∀ channel ∈ finished, channel.Consistent
  finished_subset : finished ⊆ channels
  subset_finished : ensemble.channelsWithGuarantees ⊆ finished
  ordered_channels : ensemble.OrderedChannels finished
  -- TODO get rid of this assumption, by being more flexible about table order
  -- => use "∃ permutation, s.t. ordered" instead of "ordered" in Ensemble.OrderedChannels
  verifier_empty : ensemble.verifier = .empty F PublicIO

attribute [circuit_norm] SoundEnsemble.finished_consistent SoundEnsemble.finished_subset SoundEnsemble.subset_finished
  SoundEnsemble.ordered_channels SoundEnsemble.verifier_empty

namespace SoundEnsemble
variable [DecidableEq F]

lemma soundChannels (ens : SoundEnsemble F PublicIO) : ens.SoundChannels ens.finished := by
  rcases ens with
    ⟨ ens, finished, finished_consistent, finished_subset, subset_finished, ordered_channels, verifier_empty ⟩
  rw [ens.channelsWithGuarantees_subset_iff] at subset_finished
  simp_all only [circuit_norm]

def empty (F : Type) [Field F] [DecidableEq F] (PublicIO : TypeMap) [ProvableType PublicIO] :
  SoundEnsemble F PublicIO where
    ensemble := .empty F PublicIO
    finished := []
    finished_consistent := by simp
    finished_subset := List.Subset.refl _
    subset_finished := by simp [circuit_norm, Ensemble.channelsWithGuarantees]
    ordered_channels := by simp [circuit_norm]
    verifier_empty := by simp [circuit_norm]

@[circuit_norm] lemma empty_tables  : (empty F PublicIO).tables = [] := rfl
@[circuit_norm] lemma empty_channels : (empty F PublicIO).channels = [] := rfl
@[circuit_norm] lemma empty_finished : (empty F PublicIO).finished = [] := rfl
@[circuit_norm] lemma empty_verifier : (empty F PublicIO).verifier = .empty F PublicIO := rfl

def addTable (soundEns : SoundEnsemble F PublicIO) (table : Component F)
    (grts_subset_finished : table.circuit.channelsWithGuarantees ⊆ soundEns.finished
      := by simp [circuit_norm])
    (reqs_disjoint_finished : ∀ channel ∈ soundEns.finished, channel ∉ table.circuit.channelsWithRequirements
      := by simp [circuit_norm])
    : SoundEnsemble F PublicIO where
  ensemble := soundEns.ensemble.addTable table
  finished := soundEns.finished
  finished_consistent := soundEns.finished_consistent
  finished_subset := soundEns.finished_subset
  subset_finished := by
    have h := soundEns.subset_finished
    simp_all [circuit_norm, Ensemble.channelsWithGuarantees_eq_verifier_append]
  ordered_channels := soundEns.orderedChannels_of_soundChannels_addTable table soundEns.soundChannels
    soundEns.verifier_empty grts_subset_finished reqs_disjoint_finished
  verifier_empty := soundEns.verifier_empty

variable {soundEns : SoundEnsemble F PublicIO} {table : Component F}
    {gsf : table.circuit.channelsWithGuarantees ⊆ soundEns.finished}
    {rdf : ∀ channel ∈ soundEns.finished, channel ∉ table.circuit.channelsWithRequirements}

@[circuit_norm] lemma addTable_tables :
  (soundEns.addTable table gsf rdf).tables = table :: soundEns.tables := rfl
@[circuit_norm] lemma addTable_channels :
  (soundEns.addTable table gsf rdf).channels = soundEns.channels := rfl
@[circuit_norm] lemma addTable_finished :
  (soundEns.addTable table gsf rdf).finished = soundEns.finished := rfl
@[circuit_norm] lemma addTable_verifier :
  (soundEns.addTable table gsf rdf).verifier = soundEns.verifier := rfl

def addChannel (soundEns : SoundEnsemble F PublicIO) (channel : RawChannel F) : SoundEnsemble F PublicIO where
  ensemble := { soundEns.ensemble with channels := channel :: soundEns.channels }
  finished := soundEns.finished
  finished_consistent := soundEns.finished_consistent
  finished_subset := by simp [soundEns.finished_subset]
  subset_finished := soundEns.subset_finished
  ordered_channels := soundEns.ordered_channels
  verifier_empty := soundEns.verifier_empty

@[circuit_norm] lemma addChannel_channels {channel : RawChannel F} :
  (soundEns.addChannel channel).channels = channel :: soundEns.channels := rfl
@[circuit_norm] lemma addChannel_tables {channel : RawChannel F} :
  (soundEns.addChannel channel).tables = soundEns.tables := rfl
@[circuit_norm] lemma addChannel_finished {channel : RawChannel F} :
  (soundEns.addChannel channel).finished = soundEns.finished := rfl

def markFinished (soundEns : SoundEnsemble F PublicIO) (channel : RawChannel F) [channel.Consistent]
  (h_mem : channel ∈ soundEns.channels := by simp [circuit_norm]) :
    SoundEnsemble F PublicIO where
  ensemble := soundEns.ensemble
  finished := channel :: soundEns.finished
  finished_consistent := by
    intro channel' h_mem_channel
    rw [List.mem_cons] at h_mem_channel
    rcases h_mem_channel with rfl | h_mem_tail
    · assumption
    · exact soundEns.finished_consistent channel' h_mem_tail
  finished_subset := by simp [h_mem, soundEns.finished_subset]
  subset_finished := by simp [soundEns.subset_finished]
  ordered_channels := by
    intro channel' hc
    have : channel'.Consistent := by
      simp at hc
      rcases hc with rfl | hc_tail
      · assumption
      · exact soundEns.finished_consistent channel' hc_tail
    have := soundEns.soundChannels_markFinished soundEns.soundChannels channel'
    exact this.right.left channel' (by simp)
  verifier_empty := soundEns.verifier_empty

variable {channel : RawChannel F} [channel.Consistent] {h_mem : channel ∈ soundEns.channels}

@[circuit_norm] lemma markFinished_channels :
  (soundEns.markFinished channel h_mem).channels = soundEns.channels := rfl
@[circuit_norm] lemma markFinished_tables :
  (soundEns.markFinished channel h_mem).tables = soundEns.tables := rfl
@[circuit_norm] lemma markFinished_finished :
  (soundEns.markFinished channel h_mem).finished = channel :: soundEns.finished := rfl

def addFinishedChannel (soundEns : SoundEnsemble F PublicIO) (channel : RawChannel F)
  [channel.Consistent] : SoundEnsemble F PublicIO :=
  soundEns
    |>.addChannel channel
    |>.markFinished channel

@[circuit_norm] lemma addFinishedChannel_channels {channel : RawChannel F} [channel.Consistent] :
  (soundEns.addFinishedChannel channel).channels = channel :: soundEns.channels := rfl
@[circuit_norm] lemma addFinishedChannel_tables {channel : RawChannel F} [channel.Consistent] :
  (soundEns.addFinishedChannel channel).tables = soundEns.tables := rfl
@[circuit_norm] lemma addFinishedChannel_finished {channel : RawChannel F} [channel.Consistent] :
  (soundEns.addFinishedChannel channel).finished = channel :: soundEns.finished := rfl

def toFormal (soundEns : SoundEnsemble F PublicIO)
    (Assumptions Spec : PublicIO F → Prop)
    (assumptionsConsistency : soundEns.AssumptionsConsistency Assumptions)
    (specConsistency : soundEns.SpecConsistency Spec) :
    FormalEnsemble F PublicIO where
  ensemble := soundEns.ensemble
  Assumptions := Assumptions
  Spec := Spec
  soundness := by
    apply soundEns.soundness_of_tableSoundness_and_specConsistency
      Assumptions Spec ?_ assumptionsConsistency specConsistency
    apply soundEns.tableSoundness_of_soundChannels
    use soundEns.finished, soundEns.finished_subset
    exact soundEns.soundChannels
end SoundEnsemble

/-
VM-like ensembles have a "main channel" that stores the VM state, which we'll call a _VM channel_.
One or more tables pull from, then push to, this channel in their row circuit; thereby performing one VM transition.

The public input/output of such an ensemble is the initial push (initial state) and the final pull (final state).
The statement to prove is that there exists a sequence of valid VM transitions from the initial state to the final state.
Note that this does not, in general, require that every row in the trace participates in a single transition path!
In addition to the main (valid) transition path, there can be additional closed cycles of VM steps.

What is more, the unused cycles can be "invalid" in the sense that we generally cannot prove that their guarantees are satisfied,
because we get a circular implication sequence of the form ... → guarantees → requirements → guarantees → ...

Consequently, from the assumptions (constraints + balance), we _cannot_ prove global soundness for a VM channel in the sense that
all guarantees for that channel must hold (like we did above for the `SoundChannels` case).

This is why we need a weaker statement about VM channels which still allows us to prove soundness of the overall ensemble.
Essentially, it amounts to the simple idea that for any cycle, if just _one_ of the guarantees or requirements hold,
then all of them do.
This holds in a very general sense and is applied to the "cycle" which contains the input + output interactions as
start and end points.
Thus, assuming the _input satisfies the requirements_ (a very sensible assumption), we can conclude that
the _output satisfies the guarantees_. The latter can usually be engineered to be exactly the statement we actually care about.

The main proof idea is captured by the following definitions, culminating in
`guarantees_of_requirements_of_requirements_of_guarantees`,
a theorem which states the VM interaction situation in a rather abstract setting.

Below that, we introduce the `VmTables` structure (capturing basic assumptions we put on a VM definition) as well as the
`SoundVmChannel` class (capturing what we mean with soundness for a VM), and then go on to prove our main theorem,
`addVm_soundVmChannel_of_soundChannels`, which shows soundness for a VM added on top of a `SoundChannels` ensemble.
-/

/--
Soundness for a VM ensemble is simple:
- the ensemble spec is just the verifier spec
- the verifier spec can be proven from constraints + balance for all tables/channels
-/
def Ensemble.SoundVmChannel [DecidableEq F] (ens : Ensemble F PublicIO) : Prop :=
  ∀ (witness : EnsembleWitness ens),
    witness.Assumptions →
    witness.Constraints →
    witness.BalancedChannels →
      ens.VerifierGuarantees witness.publicInput witness.data

structure SoundVmEnsemble (F : Type) [Field F] [DecidableEq F] (PublicIO : TypeMap) [ProvableType PublicIO]
    extends ensemble : Ensemble F PublicIO where
  soundVmChannel : ensemble.SoundVmChannel

namespace SoundVmEnsemble
def toFormal (F : Type) [Field F] [DecidableEq F] (ens : SoundVmEnsemble F PublicIO)
    -- TODO is this useful in practice? Right now, tables don't have access to public input so that's weird
    (ExtraAssumptions : PublicIO F → ProverData F → Prop)
    (extraAssumptionsConsistency :
      ∀ publicInput data, ExtraAssumptions publicInput data →
        ∀ table ∈ ens.ensemble.tables, ∀ input data, table.circuit.Assumptions input data) :
    FormalEnsemble F PublicIO where
  ensemble := ens.ensemble
  Assumptions publicInput := ∀ data,
    ens.verifier.Assumptions publicInput data ∧
    ExtraAssumptions publicInput data
  Spec publicInput := ∃ data, ens.VerifierSpec publicInput data
  soundness := by
    simp only [Ensemble.Soundness, Ensemble.Statement]
    intro input assumptions ⟨witness, input_eq, constraints, balance⟩
    use witness.data
    obtain ⟨verifier_assumptions, extra_assumptions⟩ := assumptions witness.data
    simp only [← input_eq, circuit_norm] at *
    have soundVm := ens.soundVmChannel witness ?assumptions constraints balance
    convert (ens.verifier.original_full_soundness _ _ _ ?_ ?_ soundVm).1
    · rw [ProvableType.eval_fromInput_varFromOffset_zero]
    · rw [ProvableType.eval_fromInput_varFromOffset_zero]
      exact verifier_assumptions
    · exact EnsembleWitness.verifierConstraints_of_constraints constraints
    simp only [EnsembleWitness.Assumptions]
    rw [EnsembleWitness.forall_mem_allTables_iff,
      ← EnsembleWitness.verifierAssumptions_iff_verifierTable_assumptions]
    use verifier_assumptions
    intro table h_table row h_row
    apply extraAssumptionsConsistency witness.publicInput witness.data extra_assumptions
    exact EnsembleWitness.mem_tables_component_of_mem_tables h_table

variable [DecidableEq F] {ens : SoundVmEnsemble F PublicIO} {ExtraAssumptions : PublicIO F → ProverData F → Prop}
  {eac : ∀ publicInput data, ExtraAssumptions publicInput data →
    ∀ table ∈ ens.tables, ∀ input data, table.circuit.Assumptions input data}

@[circuit_norm] lemma toFormal_spec publicInput :
  (ens.toFormal F ExtraAssumptions eac).Spec publicInput ↔
    ∃ data, ens.ensemble.VerifierSpec publicInput data := by
  simp only [toFormal]

@[circuit_norm] lemma toFormal_assumptions publicInput :
  (ens.toFormal F ExtraAssumptions eac).Assumptions publicInput ↔
    ∀ data, ens.ensemble.verifier.Assumptions publicInput data ∧ ExtraAssumptions publicInput data := by
  simp only [toFormal, circuit_norm]
end SoundVmEnsemble

structure VmTables (F : Type) [Field F] [DecidableEq F] (PublicIO : TypeMap) [ProvableType PublicIO] where
  {Message : TypeMap} [provableMessage : ProvableType Message]
  channel : Channel F Message

  tables : List (Component F)
  verifier : GeneralFormalCircuit F PublicIO unit
  verifier_length_zero : ∀ pi, (verifier pi).localLength 0 = 0 := by
    simp only [circuit_norm]

  tables_channel : ∀ table ∈ tables,
    ∃ m1 m2, ⟨ channel, [(channel.pulled m1).toRaw, (channel.pushed m2).toRaw] ⟩ ∈
      table.circuit.exposedChannels table.rowInputVar table.rowOffset

  -- the verifier pulls and pushes to the channel, and doesn't push anything else
  verifier_channel : ∃ m1 m2, ⟨ channel, [(channel.pulled m1).toRaw, (channel.pushed m2).toRaw] ⟩ ∈
    verifier.exposedChannels (varFromOffset PublicIO 0) (size PublicIO)

  -- verifier requirements follow _unconditionally_ from constraints (without relying on guarantees)
  -- essentially a modified soundness theorem for the verifier
  verifier_requirements :
    let offset := size PublicIO;
    let input_var := varFromOffset PublicIO 0;
    ∀ env,
      Operations.ConstraintsHold env (verifier.main input_var |>.operations offset) →
      Operations.ChannelRequirements channel env (verifier.main input_var |>.operations offset)

instance [DecidableEq F] (vm : VmTables F PublicIO) : ProvableType vm.Message := vm.provableMessage

lemma Component.interactionsWith_of_exposedChannels {table : Component F} {channel : RawChannel F}
  {interactions : List (AbstractInteraction F)}
  (h_exposed : ⟨ channel, interactions ⟩ ∈ table.exposedChannels) :
    table.operations.interactionsWith channel = interactions := by
  rw [Component.interactionsWith_eq]
  simp only [circuit_norm, Component.exposedChannels] at *
  convert table.circuit.interactionsWith_eq_of_mem_exposedChannels _ _ _ h_exposed
end Air.Flat

def List.flattenPairs {α : Type} (pairs : List (α × α)) : List α :=
  pairs.map (fun (a, b) => [a, b]) |>.flatten

lemma flattenPairs_cons {α : Type} (a b : α) (pairs : List (α × α)) :
    List.flattenPairs ((a, b) :: pairs) = [a, b] ++ List.flattenPairs pairs := by
  simp [List.flattenPairs]

lemma zip_flattenPairs_perm {α : Type} {as bs : List α} :
    bs.length = as.length → List.Perm (List.zip as bs).flattenPairs (as ++ bs) := by
  open List in
  suffices ∀ n, as.length = n → bs.length = n →
    Perm (zip as bs).flattenPairs (as ++ bs) from this as.length rfl
  intro n as_len bs_len
  induction n generalizing as bs with
  | zero => simp_all [flattenPairs]
  | succ n ih =>
    rcases as with rfl | ⟨ a, as ⟩; nomatch as_len
    rcases bs with rfl | ⟨ b, bs ⟩; nomatch bs_len
    simp only [length_cons, Nat.add_right_cancel_iff] at as_len bs_len
    specialize ih as_len bs_len
    simp only [zip_cons_cons, flattenPairs_cons, cons_append, nil_append]
    grw [perm_cons, ← perm_cons_append_cons _ perm_rfl, perm_cons, ih]

/-- Instead of first map-flattening on the inside, then on the outside,
we can map to a 3D array, then flatten the outside, and only then the inside.
Good if you want to preserve the inner structure. -/
lemma flatMap_flatMap {α β γ : Type*} (l : List γ) (g : γ → List α) (f : γ → α → List β) :
  l.flatMap (fun x => (g x).flatMap (f x)) = (l.map (fun x => (g x).map (f x))).flatten.flatten := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp [ih]
    rfl

namespace Air.Flat

namespace Table
noncomputable def interactionssWith (table : Table F)
    (channel : RawChannel F) : List (List (Interaction F)) :=
  table.table.map fun row =>
    table.component.operations.interactionValuesWith channel (table.environment row)
end Table

/-- Ensemble interactions preserving the per-row structure until the final flatten. -/
lemma EnsembleWitness.flatMap_interactionsWith_eq_flatten {ens : Ensemble F PublicIO}
  (witness : EnsembleWitness ens) {channel : RawChannel F} :
  witness.interactionsWith channel =
    (witness.allTables.flatMap (·.interactionssWith channel)).flatten := by
  simp only [EnsembleWitness.interactionsWith, Table.interactionsWith, Table.interactionssWith]
  rw [flatMap_flatMap, List.flatMap_def]

lemma zip_flatten_flatten {α : Type} (as bs : List (List (α)))
  (same_lengths : as.length = bs.length ∧ (∀ i (hi : i < as.length) (hi' : i < bs.length), as[i].length = bs[i].length)) :
    List.zip as.flatten bs.flatten = ((as.zip bs).map (fun (t, s) => t.zip s)).flatten := by
  revert same_lengths
  suffices ∀ n, (_ : as.length = n) → (_ : bs.length = n) →
    (∀ i (hi : i < n), as[i].length = bs[i].length) →
      List.zip as.flatten bs.flatten = ((as.zip bs).map (fun t => t.1.zip t.2)).flatten by
    rintro ⟨ same_length, same_lengths ⟩
    apply this as.length rfl same_length.symm
    intro i hi
    exact same_lengths i hi (by linarith)
  intro n alen blen same_lengths
  induction n generalizing as bs with
  | zero =>
    simp at alen blen
    simp [alen, blen]
  | succ n ih =>
    rcases as with rfl | ⟨ a, as ⟩; simp
    rcases bs with rfl | ⟨ b, bs ⟩; simp
    simp at alen blen
    have same_length_zero : a.length = b.length := same_lengths 0 (by linarith)
    have same_length_succ i (hi : i < n) : as[i].length = bs[i].length := same_lengths (i + 1) (by linarith)
    simp only [List.flatten_cons, List.zip_cons_cons, List.map_cons]
    rw [List.zip_append same_length_zero]
    specialize ih as bs alen blen same_length_succ
    rw [ih]

def VmTables.toEnsemble [DecidableEq F] (vm : VmTables F PublicIO) : Ensemble F PublicIO where
  channels := [vm.channel.toRaw]
  tables := vm.tables
  verifier := vm.verifier
  verifier_length_zero := vm.verifier_length_zero

abbrev VmWitness [DecidableEq F] (vm : VmTables F PublicIO) := EnsembleWitness vm.toEnsemble

namespace VmTables
variable [DecidableEq F] {vm : VmTables F PublicIO}

@[circuit_norm] lemma toEnsemble_tables (vm : VmTables F PublicIO) : vm.toEnsemble.tables = vm.tables := rfl
@[circuit_norm] lemma toEnsemble_verifier (vm : VmTables F PublicIO) : vm.toEnsemble.verifier = vm.verifier := rfl

@[circuit_norm] abbrev allTables (vm : VmTables F PublicIO) : List (Component F) := vm.toEnsemble.allTables

theorem allTables_channel (vm : VmTables F PublicIO) : ∀ table ∈ vm.allTables,
  ∃ m1 m2, ⟨ vm.channel, [(vm.channel.pulled m1).toRaw, (vm.channel.pushed m2).toRaw] ⟩ ∈
    table.circuit.exposedChannels table.rowInputVar table.rowOffset := by
  intro table table_mem
  simp only [circuit_norm, Ensemble.allTables] at table_mem
  rcases table_mem with rfl | table_mem
  · simp only [circuit_norm]
    exact vm.verifier_channel
  · simp only [circuit_norm]
    exact vm.tables_channel table table_mem

noncomputable def interactionPair (vm : VmTables F PublicIO) (table : Component F) (table_mem : table ∈ vm.allTables) :
    Var vm.Message F × Var vm.Message F :=
  let h := vm.allTables_channel table table_mem
  ⟨ h.choose, h.choose_spec.choose ⟩

noncomputable def pull (vm : VmTables F PublicIO)
  {table : Component F} (table_mem : table ∈ vm.allTables) := vm.interactionPair table table_mem |>.fst

noncomputable def push (vm : VmTables F PublicIO)
  {table : Component F} (table_mem : table ∈ vm.allTables) := vm.interactionPair table table_mem |>.snd

/-- Concrete version of VmTables.allTables_channel -/
lemma allTables_channel' (vm : VmTables F PublicIO) {table} (_ : table ∈ vm.allTables) :
  ⟨ vm.channel.toRaw,
    [(vm.channel.pulled (vm.pull ‹_›)).toRaw, (vm.channel.pushed (vm.push ‹_›)).toRaw]
  ⟩ ∈ table.exposedChannels :=
  vm.allTables_channel table ‹_› |>.choose_spec.choose_spec

lemma interactionsWith_eq {vm : VmTables F PublicIO} {table} (_ : table ∈ vm.allTables) :
  table.operations.interactionsWith vm.channel.toRaw = [
    vm.channel.pulled (vm.pull ‹_›) |>.toRaw,
    vm.channel.pushed (vm.push ‹_›) |>.toRaw ] := by
  apply Component.interactionsWith_of_exposedChannels
  apply vm.allTables_channel'

lemma verifierInteractionsWith_eq {vm : VmTables F PublicIO} :
  vm.toEnsemble.verifierTable.operations.interactionsWith vm.channel.toRaw = [
    vm.channel.pulled (vm.pull Ensemble.mem_allTables_verifierTable) |>.toRaw,
    vm.channel.pushed (vm.push Ensemble.mem_allTables_verifierTable) |>.toRaw ] := by
  apply interactionsWith_eq
end VmTables

namespace VmWitness
variable [DecidableEq F] {vm : VmTables F PublicIO}
open EnsembleWitness

noncomputable def rowPull (witness : VmWitness vm) {table} (_ : table ∈ witness.allTables) (row : Array F) : vm.Message F :=
  eval (table.environment row) (vm.pull (witness.mem_allTables_component_of_mem_allTables ‹_›))

noncomputable def rowPush (witness : VmWitness vm) {table} (_ : table ∈ witness.allTables) (row : Array F) : vm.Message F :=
  eval (table.environment row) (vm.push (witness.mem_allTables_component_of_mem_allTables ‹_›))

noncomputable def verifierPull (witness : VmWitness vm) : vm.Message F :=
  eval (Environment.fromInput witness.publicInput witness.data) (vm.pull Ensemble.mem_allTables_verifierTable)

noncomputable def verifierPush (witness : VmWitness vm) : vm.Message F :=
  eval (Environment.fromInput witness.publicInput witness.data) (vm.push Ensemble.mem_allTables_verifierTable)

lemma interactionValuesWith_eq (witness : VmWitness vm)
    {table} (_ : table ∈ witness.allTables) (row : Array F) :
  table.component.operations.interactionValuesWith vm.channel.toRaw (table.environment row) = [
    vm.channel.pulledValue (witness.rowPull ‹_› row),
    vm.channel.pushedValue (witness.rowPush ‹_› row) ] := by
  simp only [circuit_norm, vm.interactionsWith_eq (witness.mem_allTables_component_of_mem_allTables ‹_›),
    rowPull, rowPush, AbstractInteraction.eval, ProvableType.toElements_eval]

lemma interactionValuesWith_length (witness : VmWitness vm)
    {table} (_ : table ∈ witness.allTables) (row : Array F) :
  (table.component.operations.interactionValuesWith vm.channel.toRaw (table.environment row)).length = 2 := by
  simp [witness.interactionValuesWith_eq ‹_› row]

noncomputable def pulls (witness : VmWitness vm) : List (Interaction F) :=
  witness.allTables.attach.flatMap fun ⟨ table, _ ⟩ =>
    table.table.map fun row => vm.channel.pulledValue (witness.rowPull ‹_› row)

noncomputable def pushes (witness : VmWitness vm) : List (Interaction F) :=
  witness.allTables.attach.flatMap fun ⟨ table, _ ⟩ =>
    table.table.map fun row => vm.channel.pushedValue (witness.rowPush ‹_› row)

def steps (witness : VmWitness vm) : ℕ := witness.tables.map (·.length) |>.sum

@[circuit_norm]
lemma pulls_length {witness : VmWitness vm} : witness.pulls.length = witness.steps + 1 := by
  simp [steps, pulls, allTables, circuit_norm]

@[circuit_norm]
lemma pushes_length {witness : VmWitness vm} : witness.pushes.length = witness.steps + 1 := by
  simp [steps, pushes, allTables, circuit_norm]

@[circuit_norm]
lemma pulls_mult {witness : VmWitness vm} : ∀ pull ∈ witness.pulls, pull.mult = -1 := by
  simp only [pulls, List.mem_flatMap, List.mem_attach, List.mem_map, true_and, Subtype.exists,
    forall_exists_index, and_imp]
  rintro pull _ _ _ _ rfl
  simp only [circuit_norm]

@[circuit_norm]
lemma pushes_mult {witness : VmWitness vm} : ∀ push ∈ witness.pushes, push.mult = 1 := by
  simp only [pushes, List.mem_flatMap, List.mem_attach, List.mem_map, true_and, Subtype.exists,
    forall_exists_index, and_imp]
  rintro push _ _ _ _ rfl
  simp only [circuit_norm]

@[circuit_norm]
lemma pulls_channel {witness : VmWitness vm} : ∀ pull ∈ witness.pulls, pull.channel = vm.channel.toRaw := by
  simp only [pulls, List.mem_flatMap, List.mem_attach, List.mem_map, true_and, Subtype.exists,
    forall_exists_index, and_imp]
  rintro pull _ _ _ _ rfl
  simp only [circuit_norm]

@[circuit_norm]
lemma pushes_channel {witness : VmWitness vm} : ∀ push ∈ witness.pushes, push.channel = vm.channel.toRaw := by
  simp only [pushes, List.mem_flatMap, List.mem_attach, List.mem_map, true_and, Subtype.exists,
    forall_exists_index, and_imp]
  rintro push _ _ _ _ rfl
  simp only [circuit_norm]

lemma interactionss_eq_pulls_pushes (witness : VmWitness vm) :
  witness.allTables.flatMap (·.interactionssWith vm.channel.toRaw) =
    (List.zip witness.pulls witness.pushes).map (fun ⟨pull, push⟩ => [pull, push]) := by
  simp only [pulls, pushes, List.flatMap_def]
  rw [zip_flatten_flatten _ _ (by simp), List.map_flatten]
  simp only [List.zip_map', List.map_map]
  rw [← List.pmap_eq_map (fun _ _ => trivial), List.pmap_eq_map_attach]
  congr
  funext ⟨ table, table_mem ⟩
  simp [Table.interactionssWith, List.zip_map',
    witness.interactionValuesWith_eq table_mem]

lemma interactions_eq_pulls_pushes (witness : VmWitness vm) :
  witness.interactionsWith vm.channel.toRaw =
    (List.zip witness.pulls witness.pushes).flattenPairs := by
  rw [witness.flatMap_interactionsWith_eq_flatten,
    interactionss_eq_pulls_pushes, List.flattenPairs]

lemma mem_zip_pulls_pushes_iff (witness : VmWitness vm) (pull push : Interaction F) :
  (pull, push) ∈ List.zip witness.pulls witness.pushes ↔
    ∃ table ∈ witness.allTables, ∃ row ∈ table.table,
      table.component.operations.interactionValuesWith vm.channel.toRaw (table.environment row) = [pull, push] := by
  trans [pull, push] ∈ (List.zip witness.pulls witness.pushes).map (fun ⟨pull, push⟩ => [pull, push])
  · simp
  simp [← interactionss_eq_pulls_pushes, Table.interactionssWith]

lemma pull_requirements (witness : VmWitness vm) : ∀ pull ∈ witness.pulls, pull.Requirements witness.data := by
  simp only [pulls, List.mem_flatMap, List.mem_attach, List.mem_map, true_and, Subtype.exists,
    forall_exists_index, and_imp]
  rintro pull _ _ _ _ rfl
  simp [circuit_norm, Interaction.Requirements, Channel.toRaw]

lemma push_guarantees (witness : VmWitness vm) : ∀ push ∈ witness.pushes, push.Guarantees witness.data := by
  simp only [pushes, List.mem_flatMap, List.mem_attach, List.mem_map, true_and, Subtype.exists,
    forall_exists_index, and_imp]
  rintro push _ _ _ _ rfl
  simp only [circuit_norm, Interaction.Guarantees]

lemma pulls_length_pos {witness : VmWitness vm} : witness.pulls.length > 0 := by
  simp [pulls_length]
lemma pushes_length_pos {witness : VmWitness vm} : witness.pushes.length > 0 := by
  simp [pushes_length]

lemma pulls_getElem_zero_eq (witness : VmWitness vm) :
    witness.pulls[0]'pulls_length_pos = vm.channel.pulledValue witness.verifierPull := by
  simp [pulls, allTables, circuit_norm, rowPull, verifierPull]

lemma pushes_getElem_zero_eq (witness : VmWitness vm) :
    witness.pushes[0]'pushes_length_pos = vm.channel.pushedValue witness.verifierPush := by
  simp [pushes, allTables, circuit_norm, rowPush, verifierPush]

/-- Translation of the VM soundness theorem to VmTables -/
theorem verifier_guarantees_of_requirements_of_requirements_of_guarantees
  [Fact (ringChar F ≠ 2)] (witness : VmWitness vm) :
  -- if the vm interactions with the vm channel are balanced
  BalancedInteractions (witness.interactionsWith vm.channel.toRaw) →
  -- and for every row, vm channel guarantees imply vm channel requirements
  -- (this will come from constraints + soundness of the existing ensemble)
  (∀ table ∈ witness.allTables, ∀ row ∈ table.table,
    table.component.operations.ChannelGuarantees vm.channel.toRaw (table.environment row) →
    table.component.operations.ChannelRequirements vm.channel.toRaw (table.environment row)) →
  -- vm channel verifier requirements imply vm channel verifier guarantees
  witness.verifierTable.ChannelRequirements vm.channel.toRaw →
    witness.verifierTable.ChannelGuarantees vm.channel.toRaw := by
  intro balance constraints
  -- prove balance of pulls + pushes
  replace balance : BalancedInteractions (witness.pulls ++ witness.pushes) := by
    rw [witness.interactions_eq_pulls_pushes] at balance
    apply balancedInteractions_of_perm balance
    apply zip_flattenPairs_perm <| witness.pushes_length ▸ witness.pulls_length.symm
  -- we fill in the conditions on pulls and pushes in `guarantees_of_requirements_of_requirements_of_guarantees`
  let n := witness.steps + 1
  have : witness.pulls.length = n := by simp [witness.pulls_length, n]
  have : witness.pushes.length = n := by simp [witness.pushes_length, n]
  have grts_of_reqs := guarantees_of_requirements_of_requirements_of_guarantees
    vm.channel.toRaw witness.pulls witness.pushes balance witness.data n
    witness.pulls_length witness.pushes_length witness.pulls_channel witness.pushes_channel
    witness.pulls_mult witness.pushes_mult
  -- it remains to prove the (grts → reqs) assumption. this is a reformulation of our `constraints`
  have reqs_of_grts : (∀ i (hi : i < n),
      witness.pulls[i].Guarantees witness.data → witness.pushes[i].Requirements witness.data) := by
    suffices ∀ pair ∈ (witness.pulls.zip witness.pushes), pair.1.Guarantees witness.data → pair.2.Requirements witness.data by
      simp only [List.forall_mem_iff_getElem, List.getElem_zip] at this
      intro i hi
      exact this i (by simp [*])
    intro (pull, push) pair_mem
    simp only
    have ⟨ mem_pull, mem_push ⟩ := List.of_mem_zip pair_mem
    have push_grts := witness.push_guarantees push mem_push
    have pull_reqs := witness.pull_requirements pull mem_pull
    rw [witness.mem_zip_pulls_pushes_iff] at pair_mem
    obtain ⟨ table, table_mem, row, row_mem, interactions_eq ⟩ := pair_mem
    suffices (∀ i ∈ [pull, push], i.Guarantees witness.data) → (∀ i ∈ [pull, push], i.Requirements witness.data) by
      simp_all
    rw [← interactions_eq, Operations.interactionValuesWith_eq_map, List.forall_mem_map, List.forall_mem_map]
    have env_data_eq : (table.environment row).data = witness.data := witness.data_eq_of_mem_allTables _ table_mem
    simp only [← env_data_eq, AbstractInteraction.eval_guarantees, AbstractInteraction.eval_requirements,
      Operations.forall_interactionsWith_iff]
    convert constraints table table_mem row row_mem
  -- to get the conclusion about the verifier, we specialize to index 0
  specialize grts_of_reqs reqs_of_grts 0 (by simp [n])
  rw [witness.pulls_getElem_zero_eq, witness.pushes_getElem_zero_eq] at grts_of_reqs
  simp only [VmWitness.verifierPush, VmWitness.verifierPull] at grts_of_reqs
  rw [← Channel.eval_pushed, AbstractInteraction.eval_requirements] at grts_of_reqs
  rw [← Channel.eval_pulled, AbstractInteraction.eval_guarantees] at grts_of_reqs
  simp only [Table.ChannelGuarantees, Table.ChannelRequirements, circuit_norm]
  simp only [← Operations.forall_interactionsWith_iff, vm.verifierInteractionsWith_eq]
  simp_all only [List.mem_cons, List.not_mem_nil, forall_eq_or_imp]
  tauto
end VmWitness

namespace Ensemble
variable [DecidableEq F]

def addVm (ens : Ensemble F PublicIO) (vm : VmTables F PublicIO) : Ensemble F PublicIO where
  channels := vm.channel :: ens.channels
  tables := vm.tables ++ ens.tables
  verifier := vm.verifier
  verifier_length_zero := vm.verifier_length_zero

@[circuit_norm] lemma addVm_channels (ens : Ensemble F PublicIO) (vm : VmTables F PublicIO) :
  (ens.addVm vm).channels = vm.channel.toRaw :: ens.channels := rfl
@[circuit_norm] lemma addVm_tables (ens : Ensemble F PublicIO) (vm : VmTables F PublicIO) :
  (ens.addVm vm).tables = vm.tables ++ ens.tables := rfl
@[circuit_norm] lemma addVm_verifier (ens : Ensemble F PublicIO) (vm : VmTables F PublicIO) :
  (ens.addVm vm).verifier = vm.verifier := rfl
@[circuit_norm] lemma addVm_verifierTable (ens : Ensemble F PublicIO) (vm : VmTables F PublicIO) :
  (ens.addVm vm).verifierTable = vm.toEnsemble.verifierTable := rfl

/-- split up the witness of `Ensemble.addVm _ _` -/
lemma addVm_witness (ens : Ensemble F PublicIO) (vm : VmTables F PublicIO)
  (witness : EnsembleWitness (ens.addVm vm)) :
    ∃ (vmWitness : VmWitness vm) (witness' : EnsembleWitness ens),
      witness.tables = vmWitness.tables ++ witness'.tables ∧
      witness.allTables = vmWitness.allTables ++ witness'.tables ∧
      vmWitness.publicInput = witness.publicInput ∧
      witness'.publicInput = witness.publicInput ∧
      vmWitness.data = witness.data ∧
      witness'.data = witness.data := by
  have h_len : (ens.addVm vm).tables.length = vm.tables.length + ens.tables.length := by
    simp [addVm]
  have h_witlen : witness.tables.length = vm.tables.length + ens.tables.length := by
    simp [← witness.same_length, addVm]
  let vmWitness : VmWitness vm := {
    tables := witness.tables.take vm.tables.length
    publicInput := witness.publicInput
    data := witness.data
    same_length := by
      simp [VmTables.toEnsemble, List.length_take, h_witlen]
    same_circuits := by
      intro i hi
      have hi' : i < vm.tables.length := by
        simpa [VmTables.toEnsemble] using hi
      have : i < (ens.addVm vm).tables.length := by
        omega
      rw [List.getElem_take, ← witness.same_circuits _ this]
      simp [VmTables.toEnsemble, addVm, hi']
    same_data := by
      intro table h_table
      apply witness.same_data
      exact List.mem_of_mem_take h_table
  }
  let witness' : EnsembleWitness ens := {
    tables := witness.tables.drop vm.tables.length
    publicInput := witness.publicInput
    data := witness.data
    same_length := by
      simp [List.length_drop, h_witlen]
    same_circuits := by
      intro i hi
      have : vm.tables.length + i < (ens.addVm vm).tables.length := by
        omega
      rw [List.getElem_drop, ← witness.same_circuits _ this]
      simp [addVm]
    same_data := by
      intro table h_table
      apply witness.same_data
      exact List.mem_of_mem_drop h_table
  }
  refine ⟨vmWitness, witness', ?_, ?_, rfl, rfl, rfl, rfl ⟩
  · simp [vmWitness, witness', List.take_append_drop]
  · simp [EnsembleWitness.allTables, EnsembleWitness.verifierTable,
      Ensemble.addVm, VmTables.toEnsemble, vmWitness, witness', List.take_append_drop]

theorem addVm_soundVmChannel_of_soundChannels [Fact (ringChar F ≠ 2)] (ens : Ensemble F PublicIO)
      -- given a sound channels ensemble with a list of finished, consistent channels
    {finished : List (RawChannel F)} (soundChannels : ens.SoundChannels finished)
    (consistent : ∀ channel ∈ finished, channel.Consistent)
    (finished_subset : finished ⊆ ens.channels)
    (verifier_empty : ens.verifier = .empty F PublicIO)
    -- and given a VM channel + tables + verifier
    (vm : VmTables F PublicIO) :
    -- assuming that none of the existing tables interacted with the VM channel
    (∀ table ∈ ens.tables, vm.channel.toRaw ∉ table.circuit.channels) →
    -- assuming that the VM tables' and verifier's channelsWithGuarantees are either finished or the VM channel
    (vm.verifier.channelsWithGuarantees ⊆ vm.channel.toRaw :: finished ∧
      ∀ table ∈ vm.tables, table.circuit.channelsWithGuarantees ⊆ vm.channel.toRaw :: finished) →
    -- and assuming the VM tables' channelsWithRequirements contain none of the finished ones
    (∀ channel ∈ finished, channel ∉ vm.verifier.channelsWithRequirements ∧
      ∀ table ∈ vm.tables, channel ∉ table.circuit.channelsWithRequirements) →
    -- the ensemble with the VM tables satisfies SoundVmChannel
    (ens.addVm vm).SoundVmChannel := by
  intro not_mem_vm_channel grts_subset reqs_disjoint witness assumptions constraints balance
  /-
  the high level plan is to apply
  `verifier_guarantees_of_requirements_of_requirements_of_guarantees`.

  1) we need to narrow vm channel balance to just the vm tables
  2) guarantees for finished channels follows from soundChannels + constraints, using
     `spec_and_guarantees_of_soundChannels` and `guarantees_of_requirements_append`
     as the key lemmas.
  3) the combination of guarantees for finished channels + vm constraints gives us the main condition:
     "vm guarantees → vm requirements", by invoking `requirements_of_partial_guarantees_of_constraints`.
  4) finally, `VmTables.verifier_requirements` gives us the requirements for the verifier,
     from which the conclusion follows.
  -/
  obtain ⟨ vmWitness, witness', _, allTables_split, publicInput_eq_vm, _, data_eq_vm, data_eq_old ⟩ :=
    addVm_witness ens vm witness
  have data_eq : vmWitness.data = witness'.data := by rw [data_eq_vm, data_eq_old]
  have verifierTable_eq : vmWitness.verifierTable = witness.verifierTable := by
    simp only [circuit_norm, EnsembleWitness.verifierTable, Ensemble.addVm,
      data_eq_vm, publicInput_eq_vm]
  set vmTables := vmWitness.tables
  set vmChannel := vm.channel.toRaw
  -- the vm channel interactions are constrained to vm tables
  have vmInteractions_eq : witness.interactionsWith vmChannel = vmWitness.interactionsWith vmChannel := by
    simp only [EnsembleWitness.interactionsWith, allTables_split, List.flatMap_append]
    suffices witness'.tables.flatMap (·.interactionsWith vmChannel) = [] by
      rw [this, List.append_nil]
    simp only [List.flatMap_eq_nil_iff]
    intro table mem_table
    apply Table.interactionsWith_nil_of_channel_not_mem
    apply not_mem_vm_channel table.component
    exact EnsembleWitness.mem_tables_component_of_mem_tables mem_table
  -- this already lets us supply the balance condition
  have vm_balance := balance vmChannel (by simp [vmChannel, Ensemble.addVm])
  simp only [circuit_norm, vmInteractions_eq] at vm_balance
  have verifier_guarantees := vmWitness
    |>.verifier_guarantees_of_requirements_of_requirements_of_guarantees vm_balance
  -- next, we work on instantiating `requirements_of_partial_guarantees_of_constraints`
  -- which will give us exactly the second hypothesis of `verifier_guarantees`
  -- first, unify channel subset assumptions to all tables
  have grts_subset_all : ∀ table ∈ vmWitness.allTables,
      table.channelsWithGuarantees ⊆ vmChannel :: finished := by
    simp only [circuit_norm, EnsembleWitness.allTables]
    use grts_subset.1
    intro table h_table
    apply grts_subset.2 table.component
    apply EnsembleWitness.mem_tables_component_of_mem_tables h_table
  replace reqs_disjoint : ∀ channel ∈ finished, ∀ table ∈ vmWitness.allTables,
      channel ∉ table.channelsWithRequirements := by
    intro channel channel_mem
    simp only [circuit_norm, VmTables.toEnsemble, EnsembleWitness.allTables]
    use (reqs_disjoint channel channel_mem).1
    intro table table_mem
    apply (reqs_disjoint channel channel_mem).2
    apply EnsembleWitness.mem_tables_component_of_mem_tables table_mem
  -- specialize constraints and assumptions to both old and vm ensemble
  have constraints' : witness'.Constraints := by
    simp only [EnsembleWitness.Constraints, allTables_split, List.mem_append] at constraints ⊢
    simp only [EnsembleWitness.forall_mem_allTables_iff]
    use witness'.verifierTable_constraints_of_verifier_empty verifier_empty
    intro table table_mem
    exact constraints table (.inr table_mem)
  have vm_constraints : vmWitness.Constraints := by
    simp only [EnsembleWitness.Constraints, allTables_split, List.mem_append] at constraints ⊢
    intro table table_mem
    exact constraints table (.inl table_mem)
  have assumptions' : witness'.Assumptions := by
    simp only [EnsembleWitness.Assumptions, allTables_split, List.mem_append] at assumptions ⊢
    simp only [EnsembleWitness.forall_mem_allTables_iff]
    use witness'.verifierTable_assumptions_of_verifier_empty verifier_empty
    intro table table_mem
    exact assumptions table (.inr table_mem)
  have vm_assumptions : vmWitness.Assumptions := by
    simp only [EnsembleWitness.Assumptions, allTables_split, List.mem_append] at assumptions ⊢
    intro table table_mem
    exact assumptions table (.inl table_mem)
  -- establish partial balance + specialize to old ensemble
  have partial_balance : ∀ channel ∈ finished,
      PartialBalancedChannel (.append vmWitness witness' data_eq) channel := by
    intro channel channel_mem
    apply partialBalancedChannel_of_balancedInteractions
    convert balance channel ?_ using 1 <;> simp only [circuit_norm]
    · rw [EnsembleWitness.interactionsWith_of_verifier_empty verifier_empty]
      simp only [EnsembleWitness.interactionsWith, allTables_split, circuit_norm]
    exact .inr (finished_subset channel_mem)
  have partial_balance' : ∀ channel ∈ finished,
      PartialBalancedChannel witness' channel := by
    intro channel' channel_mem'
    apply partialBalancedChannel_of_sublist (partial_balance _ channel_mem')
    use vmWitness.allTables
    simp only [circuit_norm, List.perm_append_comm]
    exact reqs_disjoint _ channel_mem'
  -- invoke old tables soundness to get reqs for finished channels from constraints
  -- uses `soundChannels`, `constraints'`, `partial_balance'`
  have finished_reqs : ∀ channel ∈ finished, ∀ table ∈ witness'.allTables,
      table.ChannelRequirements channel := by
    intro channel channel_mem table table_mem
    refine spec_and_guarantees_of_soundChannels (witness := witness'.allTablesWitness)
      ?soundChannels assumptions' constraints' partial_balance' table table_mem
      |>.right channel channel_mem |>.right
    convert soundChannels
    simp [circuit_norm]
  -- invoke `guarantees_of_requirements_append` to get grts for finished channels in vm tables
  have finished_grts : ∀ table ∈ vmWitness.allTables, ∀ channel ∈ finished,
      table.ChannelGuarantees channel := by
    intro table table_mem channel channel_mem
    have : channel.Consistent := consistent channel channel_mem
    apply guarantees_of_requirements_append (ts := vmWitness.allTablesWitness)
      (ss := witness'.allTablesWitness) data_eq (reqs_disjoint _ channel_mem)
      (partial_balance _ channel_mem) (finished_reqs _ channel_mem) _ table_mem
  -- invoke `requirements_of_partial_guarantees_of_constraints` to get per-row grts → reqs for the vm channel,
  -- and use it in `verifier_guarantees`
  have reqs_of_grts (table) (h_table : table ∈ vmWitness.allTables) :=
    table.requirements_of_partial_guarantees_of_constraints (unfinished := vmChannel)
    (vm_assumptions table h_table) (vm_constraints table h_table)
    (grts_subset_all table h_table) (finished_grts table h_table)
  specialize verifier_guarantees reqs_of_grts
  -- massage the conclusion so it matches that of `verifier_guarantees`.
  -- mainly, we need to use (again) that all guarantees apart from the VM channel are satisfied
  rw [EnsembleWitness.verifierGuarantees_iff_verifierTable_guarantees, ← verifierTable_eq,
    Table.guarantees_iff_channelGuarantees]
  simp only [circuit_norm]
  suffices vmWitness.verifierTable.ChannelRequirements vm.channel.toRaw by
    intro channel channel_mem
    replace channel_mem := grts_subset.1 channel_mem
    rcases List.mem_cons.mp channel_mem with rfl | channel_mem
    · exact verifier_guarantees this
    · exact finished_grts _ vmWitness.mem_allTables_verifierTable _ channel_mem
  -- finally, we prove the verifier requirements using `VmTables.verifier_requirements`
  rw [← EnsembleWitness.verifierChannelRequirements_iff]
  apply vm.verifier_requirements
  show vm.toEnsemble.VerifierConstraints vmWitness.publicInput vmWitness.data
  rw [EnsembleWitness.verifierConstraints_iff_verifierTable_constraints]
  exact vm_constraints _ vmWitness.mem_allTables_verifierTable
end Ensemble

namespace SoundEnsemble
variable [DecidableEq F]

def addVm [Fact (ringChar F ≠ 2)] (ens : SoundEnsemble F PublicIO) (vm : VmTables F PublicIO)
    (ne_mem_vm_channel : ∀ table ∈ ens.tables, vm.channel.toRaw ∉ table.circuit.channels
      := by simp [circuit_norm])
    (grts_subset_finished : vm.verifier.channelsWithGuarantees ⊆ vm.channel.toRaw :: ens.finished ∧
      ∀ table ∈ vm.tables, table.circuit.channelsWithGuarantees ⊆ vm.channel.toRaw :: ens.finished
      := by simp [circuit_norm])
    (reqs_disjoint_finished : ∀ channel ∈ ens.finished, channel ∉ vm.verifier.channelsWithRequirements ∧
      ∀ table ∈ vm.tables, channel ∉ table.circuit.channelsWithRequirements
      := by simp [circuit_norm]) :
    SoundVmEnsemble F PublicIO where
  __ := ens.ensemble.addVm vm
  soundVmChannel := ens.ensemble.addVm_soundVmChannel_of_soundChannels
    ens.soundChannels ens.finished_consistent ens.finished_subset ens.verifier_empty vm ne_mem_vm_channel
    grts_subset_finished reqs_disjoint_finished

variable {soundEns : SoundEnsemble F PublicIO} {vm : VmTables F PublicIO}
  {nmv : ∀ table ∈ soundEns.ensemble.tables, vm.channel.toRaw ∉ table.circuit.channels}
  {gsf : vm.verifier.channelsWithGuarantees ⊆ vm.channel.toRaw :: soundEns.finished ∧
    ∀ table ∈ vm.tables, table.circuit.channelsWithGuarantees ⊆ vm.channel.toRaw :: soundEns.finished}
  {rdf : ∀ channel ∈ soundEns.finished, channel ∉ vm.verifier.channelsWithRequirements ∧
    ∀ table ∈ vm.tables, channel ∉ table.circuit.channelsWithRequirements}

@[circuit_norm] lemma addVm_tables [Fact (ringChar F ≠ 2)] :
  (soundEns.addVm vm nmv gsf rdf).tables = vm.tables ++ soundEns.tables := rfl
@[circuit_norm] lemma addVm_channels [Fact (ringChar F ≠ 2)] :
  (soundEns.addVm vm nmv gsf rdf).channels = vm.channel.toRaw :: soundEns.channels := rfl
@[circuit_norm] lemma addVm_verifier [Fact (ringChar F ≠ 2)] :
  (soundEns.addVm vm nmv gsf rdf).verifier = vm.verifier := rfl
@[circuit_norm] lemma addVm_ensemble [Fact (ringChar F ≠ 2)] :
  (soundEns.addVm vm nmv gsf rdf).ensemble = soundEns.ensemble.addVm vm := rfl

end SoundEnsemble
end Air.Flat
end

-- CONCRETE EXAMPLE STARTS HERE

instance (p : ℕ) [pGt : Fact (p > 512)] : Fact (ringChar (F p) ≠ 2) := .mk <| by
  simp [F, ZMod.ringChar_zmod_n]
  linarith [pGt.out]

variable {p : ℕ} [Fact p.Prime] [pGt: Fact (p > 512)]

def BytesTable : StaticLookupChannel (F p) field where
  name := "bytes"
  table := List.finRange 256 |>.map ByteUtils.fromByte
  Guarantees msg := msg.val < 256
  guarantees_iff := by
    intro (msg : F p)
    simp only [List.mem_map, List.mem_finRange, true_and]
    constructor
    · intro h_lt
      exact ⟨⟨ msg.val, h_lt ⟩, ByteUtils.fromByte_eq ..⟩
    · intro ⟨ ⟨ b, hb ⟩, h_eq ⟩
      rw [← h_eq]
      apply ByteUtils.fromByte_lt

abbrev BytesChannel := Channel.fromStatic (F p) field BytesTable

-- bytes "circuit" that just pushes all bytes
-- probably shouldn't be a "circuit" at all
def pushBytes : GeneralFormalCircuit (F p) (fields 256) unit where
  main multiplicities := do
    let _  ← .mapFinRange 256 fun ⟨ i, _ ⟩ =>
      BytesChannel.emit multiplicities[i] (const i)

  localLength _ := 0
  localLength_eq := by simp +arith only [circuit_norm]
  output _ _ := ()
  ProverAssumptions _ _ _ := True
  Spec _ _ _ := True
  soundness := by circuit_proof_start [BytesTable]
  completeness := by circuit_proof_start
  channelsWithRequirements := [ BytesChannel.toRaw ]

instance Add8Channel : Channel (F p) fieldTriple where
  name := "add8"
  Guarantees
  | (x, y, z), _ =>
    x.val < 256 → y.val < 256 → z.val = (x.val + y.val) % 256

structure Add8Inputs F where
  x : F
  y : F
  z : F
  m : F -- multiplicity
deriving ProvableStruct

def add8 : GeneralFormalCircuit (F p) Add8Inputs unit where
  main | { x, y, z, m } => do
    -- range-check z using the bytes channel
    -- (x and y are guaranteed to be range-checked from earlier interactions)
    BytesChannel.pull z
    -- witness the output carry
    let carry ← witness fun eval => floorDiv256 (eval (x + y))
    assertBool carry
    -- assert correctness
    x + y - z - carry * 256 === 0
    -- emit to the add8 channel with multiplicity `m`
    Add8Channel.emit m (x, y, z)

  localLength _ := 1
  output _ _ := ()
  -- TODO make coercion work without .toRaw
  channelsWithGuarantees := [ BytesChannel.toRaw ]
  channelsWithRequirements := [ Add8Channel.toRaw ]
  -- TODO feels weird to put the entire spec in the completeness assumptions
  -- can we get something from the channel interactions??
  ProverAssumptions
  | { x, y, z, m }, _, _ => x.val < 256 ∧ y.val < 256 ∧ z.val < 256 ∧ z.val = (x.val + y.val) % 256
  Spec _ _ _ := True

  soundness := by
    circuit_proof_start [BytesTable, Add8Channel]
    set carry := env.get i₀
    obtain ⟨ hz, hcarry, heq ⟩ := h_holds
    intro hm hx hy
    have add_soundness := Theorems.soundness input_x input_y input_z 0 carry hx hy hz (by left; trivial) hcarry
    simp_all
  completeness := by
    circuit_proof_start [BytesTable]
    set carry := env.get i₀
    rcases h_assumptions with ⟨ hx, hy, hz, heq ⟩
    have add_completeness_bool := Theorems.completeness_bool input_x input_y 0 hx hy (by simp)
    have add_completeness_add := Theorems.completeness_add input_x input_y 0 hx hy (by simp)
    simp only [add_zero] at add_completeness_bool add_completeness_add
    have h_input_z : input_z = mod256 (input_x + input_y) := by
      apply FieldUtils.ext
      rw [heq, mod256, FieldUtils.mod, FieldUtils.natToField_val, ZMod.val_add_of_lt, PNat.val_ofNat]
      linarith [hx, hy, ‹Fact (p > 512)›.elim]
    refine ⟨ hz, ?_⟩
    refine ⟨ ?_, ?_ ⟩
    · simpa [floorDiv256, h_env] using add_completeness_bool
    · simpa [h_input_z, floorDiv256, h_env] using add_completeness_add

example (input : Var Add8Inputs (F p)) :
    ExplicitCircuit (add8.main input) := by
  infer_explicit_circuit

-- define valid Fibonacci state transitions

def fibonacci : ℕ → (ℕ × ℕ)
  | 0 => (0, 1)
  | n + 1 =>
    let (x, y) := fibonacci n
    (y, (x + y) % 256)

/-- helper lemma: fibonacci states are bytes -/
lemma fibonacci_bytes {n x y : ℕ} : (x, y) = fibonacci n → x < 256 ∧ y < 256 := by
  induction n generalizing x y with
  | zero => simp_all [fibonacci]
  | succ n ih =>
    specialize ih rfl
    simp_all [fibonacci, Nat.mod_lt]

instance FibonacciChannel : Channel (F p) fieldTriple where
  name := "fibonacci"
  -- when pulling, we want the guarantee that the input is a valid Fibonacci step
  Guarantees
  | (n, x, y), _ =>
    ∃ k : ℕ, (x.val, y.val) = fibonacci k ∧ k % p = n.val

def fib8 : GeneralFormalCircuit (F p) fieldTriple unit where
  main | (n, x, y) => do
    -- pull the current Fibonacci state
    FibonacciChannel.pull (n, x, y)
    -- witness the next Fibonacci value
    let z ← witness fun eval => mod256 (eval (x + y))
    -- pull from the Add8 channel to check addition
    Add8Channel.pull (x, y, z)
    -- push the next Fibonacci state
    FibonacciChannel.push (n + 1, y, z)

  localLength _ := 1
  output _ _ := ()
  channelsWithGuarantees := [ Add8Channel.toRaw, FibonacciChannel.toRaw ]
  channelsWithRequirements := [ FibonacciChannel.toRaw ]
  exposedChannels
  | (n, x, y), i₀ =>
    let z := var ⟨ i₀ ⟩
    expose FibonacciChannel [ pulled (n, x, y), pushed (n + 1, y, z) ]
  channelsLawful := by
    simp only [circuit_norm, Add8Channel, FibonacciChannel]

  ProverAssumptions
  | (n, x, y), _, _ =>
    ∃ k : ℕ, (x.val, y.val) = fibonacci k ∧ k % p = n.val
  Spec _ _ _ := True

  soundness := by
    circuit_proof_start
    rcases input with ⟨ n, x, y ⟩ -- TODO circuit_proof_start should have done this
    simp only [Prod.mk.injEq] at h_input
    simp_all only [circuit_norm]
    set z := env.get i₀
    simp only [circuit_norm, FibonacciChannel, Add8Channel] at h_holds ⊢
    obtain ⟨ ⟨k, fiby, hk⟩, hadd ⟩ := h_holds
    have ⟨ hx, hy ⟩ := fibonacci_bytes fiby
    use k + 1
    simp only [fibonacci, ← fiby]
    rw [ZMod.val_add, ← hk, Nat.mod_add_mod, ZMod.val_one]
    simp_all

  completeness := by
    circuit_proof_start
    rcases input with ⟨ n, x, y ⟩
    simp only [Prod.mk.injEq] at h_input
    simp_all only [circuit_norm, FibonacciChannel, Add8Channel]
    intro hx hy
    rw [mod256, FieldUtils.mod, FieldUtils.natToField_val, ZMod.val_add_of_lt, PNat.val_ofNat]
    linarith [hx, hy, ‹Fact (p > 512)›.elim]

example (input : Var fieldTriple (F p)) :
    ExplicitCircuit (fib8.main input) := by
  infer_explicit_circuit

-- additional circuits that pull/push remaining channel interactions
-- these really wouldn't have to be circuits, need to find a better place for tying together channels

-- completing Fibonacci channel with input and output
def fibonacciVerifier : GeneralFormalCircuit (F p) fieldTriple unit where
  main | (n, x, y) => do
    -- push initial state, pull the final state
    FibonacciChannel.pull (n, x, y)
    FibonacciChannel.push (0, 0, 1)

  localLength _ := 0
  output _ _ := ()
  channelsWithGuarantees := [ FibonacciChannel.toRaw ]
  channelsWithRequirements := [ FibonacciChannel.toRaw ]
  exposedChannels
  | (n, x, y), _ =>
    expose FibonacciChannel [ pulled (n, x, y), pushed (0, 0, 1) ]
  channelsLawful := by simp only [circuit_norm, FibonacciChannel]
  ProverAssumptions
  | (n, x, y), _, _ => ∃ k : ℕ, (x.val, y.val) = fibonacci k ∧ k % p = n.val
  Spec
  | (n, x, y), _, _ => ∃ k : ℕ, (x.val, y.val) = fibonacci k ∧ k % p = n.val
  soundness := by
    circuit_proof_start [FibonacciChannel]
    rcases input with ⟨ n, x, y ⟩
    simp only [Prod.mk.injEq] at h_input
    simp_all only [circuit_norm, ZMod.val_zero, ZMod.val_one]
    exact ⟨ 0, rfl, rfl ⟩
  completeness := by
    circuit_proof_start [FibonacciChannel]
    rcases input with ⟨ n, x, y ⟩
    simp only [Prod.mk.injEq] at h_input
    simpa [circuit_norm, reduceIte] using h_assumptions

example (input : Var fieldTriple (F p)) :
    ExplicitCircuit (fibonacciVerifier.main input) := by
  infer_explicit_circuit

def fibonacciVm : VmTables (F p) fieldTriple where
  channel := FibonacciChannel
  tables := [⟨ fib8 ⟩]
  verifier := fibonacciVerifier
  verifier_length_zero := by simp [circuit_norm, fibonacciVerifier]
  tables_channel := by simp [circuit_norm, fib8]
  verifier_channel := by simp [circuit_norm, fibonacciVerifier]
  verifier_requirements env := by
    simp only [circuit_norm, fibonacciVerifier, FibonacciChannel, ZMod.val_zero, ZMod.val_one]
    exact ⟨ 0, rfl, rfl ⟩

def fibonacciEnsemble := SoundEnsemble.empty (F p) fieldTriple
  |>.addTable ⟨ pushBytes ⟩
    (by simp [circuit_norm, pushBytes]) (by simp [circuit_norm, pushBytes])
  |>.addFinishedChannel BytesChannel.toRaw
  |>.addTable ⟨ add8 ⟩
    (by simp [circuit_norm, add8]) (by simp [circuit_norm, add8])
  |>.addFinishedChannel Add8Channel.toRaw
  |>.addVm fibonacciVm
    (by simp [circuit_norm, fibonacciVm, add8, pushBytes, Add8Channel, FibonacciChannel])
    (by simp [circuit_norm, fibonacciVm, fib8, fibonacciVerifier])
    (by simp [circuit_norm, fibonacciVm, fib8, fibonacciVerifier, Add8Channel, FibonacciChannel])

abbrev fibonacciFormalEnsemble := fibonacciEnsemble.toFormal (F p) (fun _ _ => True) (by
  simp [circuit_norm, fibonacciEnsemble, fibonacciVm, add8, pushBytes, fib8])

/--
Fibonacci soundness, concretely: if someone gives you a proof of the ensemble statement,
then you know that the public input is a Fibonacci number.

TODO: find a generic strategy to show that k < p, so the statement simplifies to
`(x.val, y.val) = fibonacci n.val`
The problem is that the row-transition circuit currently can't prove this: it receives any field elements n and
pushes n+1, so a priori it can overflow.

It would make sense to provide a guarantee that mentions the total interaction length "before" running the row circuit,
and prove a requirement about the total interaction length after:
pre: 2*n ≤ total_length_before
post: 2*(n + 1) ≤ total_length_after = total_length_before + 2 :check_mark:
But that massively complicates the guarantees/requirements system, since they now need access to global information.

And idea could be to define a "global state" per channel, and define how every interaction transforms that state.
Then let the guarantees/requirements access that state (the guarantees _before_ and the requiremtns _after_ the interaction).
-/
theorem fibonacci_soundness : ∀ (n x y : F p),
  fibonacciEnsemble.Statement (n, x, y) →
    ∃ k : ℕ, (x.val, y.val) = fibonacci k ∧ k % p = n.val := by
  intro n x y statement
  convert fibonacciFormalEnsemble.soundness (n, x, y) ?assumptions statement
  · simp only [circuit_norm, fibonacciEnsemble, fibonacciVm, fibonacciVerifier]
    tauto
  · simp only [circuit_norm, fibonacciEnsemble, fibonacciVm, fibonacciVerifier]

-- everything below is a remainder of the original AI slop proof of fibonacci soundness
-- TODO port non-overflow proof to the general case and remove

/-- Sum of a list where every element is -1 equals -(length) as a field element -/
lemma sum_neg_ones {F : Type} [Ring F] (l : List F) (h : ∀ x ∈ l, x = (-1 : F)) :
    l.sum = -(l.length : F) := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.sum_cons, List.length_cons, Nat.cast_succ, neg_add_rev]
    rw [h hd (List.mem_cons.mpr (Or.inl rfl)), ih (fun x hx => h x (List.mem_cons.mpr (Or.inr hx)))]

omit [Fact (p > 512)] in
/-- In a list of interactions where all multiplicities are 1 or -1,
    if the per-message sum is 0 and (-1, msg) appears, then (1, msg) also appears.
    Requires that the characteristic is larger than the list length. -/
lemma exists_push_of_pull' {n : ℕ}
    (interactions : List (F p × Vector (F p) n)) (msg : Vector (F p) n)
    (h_mults : ∀ entry ∈ interactions, entry.2 = msg → entry.1 = 1 ∨ entry.1 = -1)
    (h_balance : ((interactions.filter (fun x => x.2 = msg)).map Prod.fst).sum = 0)
    (h_pull : (-1, msg) ∈ interactions)
    (h_bound : interactions.length < p) :
    (1, msg) ∈ interactions := by
  by_contra h_no_push
  -- Every entry for msg has mult = -1
  have h_all_neg : ∀ entry ∈ interactions, entry.2 = msg → entry.1 = -1 := by
    intro entry h_mem h_eq
    rcases h_mults entry h_mem h_eq with h | h
    · exact absurd (show (1, msg) ∈ interactions by rwa [← h_eq, ← h]) h_no_push
    · exact h
  -- The filtered list has all multiplicities = -1
  have h_neg_mults : ∀ m ∈ (interactions.filter (fun x => x.2 = msg)).map Prod.fst, m = (-1 : F p) := by
    intro m h_mem
    rw [List.mem_map] at h_mem
    obtain ⟨ ⟨ m', v ⟩, h_mem', rfl ⟩ := h_mem
    simp only [List.mem_filter, decide_eq_true_eq] at h_mem'
    exact h_all_neg _ h_mem'.1 h_mem'.2
  -- The filtered list is non-empty
  have h_nonempty : 0 < (interactions.filter (fun x => x.2 = msg)).length :=
    List.length_pos_of_mem (List.mem_filter.mpr ⟨ h_pull, by simp ⟩)
  -- The sum equals -(filtered_length : F p)
  have h_sum := sum_neg_ones _ h_neg_mults
  rw [h_balance] at h_sum
  -- So (filtered_length : F p) = 0, but 0 < filtered_length < p, contradiction
  set filtered := (interactions.filter (fun x => x.2 = msg)).map Prod.fst with h_filtered_def
  have h_len_lt_p : filtered.length < p := by
    simp only [h_filtered_def, List.length_map]
    exact lt_of_le_of_lt (List.length_filter_le _ _) h_bound
  have h_cast_zero : (filtered.length : F p) = 0 := by
    have := h_sum; -- 0 = -(filtered.length : F p)
    rw [eq_comm, neg_eq_zero] at this; exact this
  rw [ZMod.natCast_eq_zero_iff filtered.length p] at h_cast_zero
  -- p | filtered.length, but 0 < filtered.length < p, contradiction
  have h_pos : filtered.length > 0 := by
    simp only [h_filtered_def, List.length_map]; exact h_nonempty
  exact absurd (Nat.le_of_dvd h_pos h_cast_zero) (not_le.mpr h_len_lt_p)

omit [Fact (p > 512)] in
/-- The step counter of any valid fibonacci state is bounded by the number of interactions.

    The fibonacci sequence forms a chain: 0 → 1 → 2 → ... → n where each step
    contributes at least 2 entries to fibInteractions. Since fibInteractions.length < p,
    any step counter n_i satisfies n_i.val < p/2 < p - 1, hence n_i.val + 1 < p. -/
lemma fib_step_counter_bounded
    (fibInteractions : List (F p × Vector (F p) 3))
    (h_bound : fibInteractions.length < p)
    (h_mults : ∀ e ∈ fibInteractions, e.1 = 1 ∨ e.1 = -1)
    (h_balanced : ∀ msg, (fibInteractions.filter (·.2 = msg) |>.map (·.1)).sum = 0)
    (h_push_pred :
      ∀ entry ∈ fibInteractions, entry.1 = 1 →
        entry.2 = (#v[(0 : F p), 0, 1] : Vector (F p) 3) ∨
        ∃ (n x y : F p), ((-1 : F p), (#v[n, x, y] : Vector (F p) 3)) ∈ fibInteractions ∧
          entry.2[0] = n + 1)
    (entry : F p × Vector (F p) 3)
    (h_mem : entry ∈ fibInteractions)
    (h_push : entry.1 = 1)
    (n_i : F p)
    (h_n_eq : entry.2[0] = n_i) :
    n_i.val + 1 < p := by
  -- Prove a stronger statement by induction on Nat counters < p
  suffices h : ∀ n : ℕ, n < p →
      ∀ entry ∈ fibInteractions, entry.1 = 1 → entry.2[0] = (n : F p) → (n + 1 ≤ fibInteractions.length) by
    have h_step : entry.2[0] = (n_i.val : F p) := by
      exact h_n_eq.trans (ZMod.natCast_zmod_val n_i).symm
    have h_le := h n_i.val (ZMod.val_lt n_i) entry h_mem h_push h_step
    exact lt_of_le_of_lt h_le h_bound
  intro n h_n_lt
  suffices h : ∀ entry ∈ fibInteractions,
    entry.1 = 1 → entry.2[0] = (n : F p) → ∀ k ≤ n, ∃ entry' ∈ fibInteractions, entry'.2[0].val = k by
    intro entry h_mem h_push h_step
    -- this is should be very easy: there are n+1 distinct entries in the chain (0..n),
    -- therefore the chain length is at least n+1
    specialize h entry h_mem h_push h_step
    clear h_mem h_push h_step entry h_n_lt h_n_eq
    clear h_mem h_push entry n_i h_push_pred
    -- let's map the list to ℕ counters and use List.map_length
    -- and then talk about Finsets
    let as := fibInteractions.map (fun e => ZMod.val e.2[0])
    suffices h_natList : (∀ k ≤ n, k ∈ as) → n + 1 ≤ as.length by simp_all [as]
    intro hk
    simp only [← List.mem_toFinset] at hk
    suffices n + 1 ≤ as.toFinset.card by
      grw [List.toFinset_card_le] at this
      linarith
    generalize as.toFinset = s at *
    rw [← Finset.card_range (n + 1)]
    apply Finset.card_le_card
    intro k hk'
    simp_all only [Finset.mem_range]
    exact hk k (by linarith)

  induction n with
  | zero =>
    intro entry h_mem h_push h_step k k_le_0
    have hk : k = 0 := by linarith
    subst hk
    use entry, h_mem
    simp only [Nat.cast_zero] at h_step
    simp [h_step, ZMod.val_zero]
  | succ n ih =>
    intro entry h_mem h_push h_step k hk
    have h_pred := h_push_pred entry h_mem h_push
    rcases h_pred with h_base | ⟨n_prev, x, y, h_pull, h_step_prev⟩
    · -- base push contradicts counter n+1
      exfalso
      have h0 : entry.2[0] = 0 := by simp [h_base]
      have h_cast : ((n + 1 : ℕ) : F p) = 0 := by simpa [h_step] using h0
      have hval := ZMod.val_cast_of_lt h_n_lt
      have : (n + 1 : ℕ) = 0 := by simp [h_cast] at hval
      exact Nat.succ_ne_zero _ this
    · -- predecessor pull gives predecessor push
      have h_push_prev : (1, (#v[n_prev, x, y] : Vector (F p) 3)) ∈ fibInteractions :=
        exists_push_of_pull' fibInteractions (#v[n_prev, x, y])
          (fun e h _ => h_mults e h) (h_balanced _) h_pull h_bound
      have h_eq : n_prev = (n : F p) := by
        have h' : n_prev + 1 = (n + 1 : F p) := by simpa [h_step_prev] using h_step
        have h'' : n_prev + 1 = (n : F p) + 1 := by simpa [Nat.cast_add] using h'
        exact add_right_cancel h''
      -- if k = n+1, use current entry; otherwise use IH on predecessor
      have hk_cases : k = n + 1 ∨ k ≤ n := by
        exact Nat.lt_or_eq_of_le hk |>.elim (fun hlt => Or.inr (Nat.le_of_lt_succ hlt)) (fun heq => Or.inl heq)
      cases hk_cases with
      | inl hk_eq =>
          subst hk_eq
          use entry, h_mem
          -- counter value is n+1
          have hval := ZMod.val_cast_of_lt h_n_lt
          simpa [h_step] using hval
      | inr hk_le =>
          have h_step_prev' : (#v[n_prev, x, y] : Vector (F p) 3)[0] = (n : F p) := by
            simp [h_eq]
          have := ih (Nat.lt_of_succ_lt h_n_lt)
            (1, (#v[n_prev, x, y] : Vector (F p) 3)) h_push_prev rfl h_step_prev' k hk_le
          exact this
