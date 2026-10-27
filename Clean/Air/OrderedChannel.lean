module

public import Clean.Air.FlatEnsemble

@[expose] public section

open Air.Flat (Component Table Tables ChannelInterface)
open Air.Flat.ChannelInterface (channelsWithGuarantees channelsWithRequirements)
variable {F : Type} {α β : Type*} [ChannelInterface α F] [ChannelInterface β F]

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
def OrderedChannel (channel : RawChannel F) (tables : List α) : Prop :=
  ∀ i (hi : i < tables.length) j (hj : j < tables.length),
    channel ∈ channelsWithGuarantees tables[i] →
    channel ∈ channelsWithRequirements tables[j] →
      i < j

@[circuit_norm]
lemma orderedChannel_nil (channel : RawChannel F) : OrderedChannel channel ([] : List α) := by
  simp [OrderedChannel]

@[circuit_norm]
abbrev OrderedChannelRefl (channel : RawChannel F) (table : α) : Prop :=
  channel ∉ channelsWithGuarantees table ∨ channel ∉ channelsWithRequirements table

abbrev OrderedChannelLt (channel : RawChannel F) (tables₁ : List α) (tables₂ : List β) : Prop :=
  channel ∉ tables₁.flatMap channelsWithGuarantees ∨
    channel ∉ tables₂.flatMap channelsWithRequirements

@[circuit_norm]
lemma orderedChannelLt_nil_right (channel : RawChannel F) (tables : List α) :
    OrderedChannelLt channel tables ([] : List β) := by simp [OrderedChannelLt]

@[circuit_norm]
lemma orderedChannelLt_nil_left (channel : RawChannel F) (tables : List β) :
    OrderedChannelLt channel ([] : List α) tables := by simp [OrderedChannelLt]

@[circuit_norm]
lemma orderedChannelLt_cons_right (channel : RawChannel F) {table : β} {ts : List β} {ss : List α} :
  OrderedChannelLt channel ss (table :: ts) ↔
    (channel ∉ ss.flatMap channelsWithGuarantees ∨ channel ∉ channelsWithRequirements table) ∧
    OrderedChannelLt channel ss ts := by
  simp [OrderedChannelLt, circuit_norm]
  tauto

@[circuit_norm]
lemma orderedChannelLt_append_left {channel : RawChannel F} {ts₁ ts₂ : List α} {ss : List β} :
  OrderedChannelLt channel (ts₁ ++ ts₂) ss ↔
    OrderedChannelLt channel ts₁ ss ∧ OrderedChannelLt channel ts₂ ss := by
  simp only [OrderedChannelLt, circuit_norm]
  tauto

@[circuit_norm]
lemma orderedChannelLt_append_right {channel : RawChannel F} {ts : List α} {ss₁ ss₂ : List β} :
  OrderedChannelLt channel ts (ss₁ ++ ss₂) ↔
    OrderedChannelLt channel ts ss₁ ∧ OrderedChannelLt channel ts ss₂ := by
  simp only [OrderedChannelLt, circuit_norm]
  tauto

@[circuit_norm]
lemma orderedChannel_cons (table : α) (tables : List α) (channel : RawChannel F) :
  OrderedChannel channel (table :: tables) ↔
  OrderedChannelRefl channel table ∧ OrderedChannel channel tables ∧ OrderedChannelLt channel tables [table] := by
  simp only [circuit_norm, OrderedChannel, OrderedChannelRefl, List.length_cons]
  -- Intuition: The `i < j` conclusion of `OrderedChannel` falsifies the hypotheses if `j = 0`,
  -- so apart from the "induction hypothesis" where `i, j > 0`, we get two distinct statements by specializing to `i = 0` and `i > 0` respectively
  simp only [Nat.forall_lt_succ_left', List.getElem_cons_zero, List.getElem_cons_succ]
  simp only [lt_self_iff_false, imp_false, lt_add_iff_pos_left, Order.lt_add_one_iff, zero_le,
    implies_true, and_true, not_lt_zero, Order.add_one_le_iff]
  rw [forall₂_and, List.forall_mem_iff_getElem, or_iff_not_imp_left, or_iff_not_imp_left]
  push Not
  simp only [exists_imp]
  tauto

lemma orderedChannel_singleton_iff (table : α) (channel : RawChannel F) :
    OrderedChannel channel [table] ↔ OrderedChannelRefl channel table := by
  simp [circuit_norm]

/-- Alternative, and sometimes more convenient, formulation of `OrderedChannel` -/
lemma orderedChannel_iff (tables : List α) (channel : RawChannel F) :
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
    push Not
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
    channel ∉ channelsWithGuarantees tables[i] ∨
    channel ∉ channelsWithRequirements tables[j] by grind
  rintro h
  rcases h with rfl | j_lt_i
  · exact ordered_channel'.left j hi
  have j_succ_lt : j + 1 < tables.length := by linarith
  replace ordered_channel' := ordered_channel'.right (tables.take (j + 1)) (tables.drop (j + 1)) (by simp)
  simp at ordered_channel'
  rcases ordered_channel' with no_grts | no_reqs
  · left
    specialize no_grts (i - (j + 1)) (by omega)
    have : i = j + 1 + (i - (j + 1)) := by omega
    convert no_grts
  · right
    specialize no_reqs j (by omega) hj
    exact no_reqs

/-- "Merge sort" for ordered channels -/
@[circuit_norm]
lemma orderedChannel_append (ts ss : List α) (channel : RawChannel F) :
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
lemma orderedChannel_of_no_requirements {channel : RawChannel F} {tables : List α} :
  (∀ table ∈ tables, channel ∉ channelsWithRequirements table) →
    OrderedChannel channel tables := by
  intro reqs
  rw [orderedChannel_iff]
  simp_all [OrderedChannelRefl, OrderedChannelLt]

/-- A sufficient condition for ordered channel is that there are no guarantees added -/
lemma orderedChannel_of_no_guarantees {channel : RawChannel F} {tables : List α} :
  (∀ table ∈ tables, channel ∉ channelsWithGuarantees table) →
    OrderedChannel channel tables := by
  intro grts
  rw [orderedChannel_iff]
  simp_all [OrderedChannelRefl, OrderedChannelLt]

/-- A sufficient condition for ordered channel lt is that there are no requirements added in the second list -/
lemma orderedChannelLt_of_no_requirements {channel : RawChannel F} {ts : List β} {ss : List α} :
  (∀ table ∈ ts, channel ∉ channelsWithRequirements table) →
    OrderedChannelLt channel ss ts := by
  intro no_reqs
  simp_all [OrderedChannelLt]

/-- A sufficient condition for ordered channel lt is that there are no guarantees added in the first list -/
lemma orderedChannelLt_of_no_guarantees {channel : RawChannel F} {ts : List β} {ss : List α} :
  (∀ table ∈ ss, channel ∉ channelsWithGuarantees table) →
    OrderedChannelLt channel ss ts := by
  intro no_grts
  simp_all [OrderedChannelLt]

variable [FiniteField F]

/--
Relaxed version of BalancedChannel that works with ensembles that aren't fully specified yet,
where we assume our interactions are a subset of some larger list which is balanced.

designed to be used for proving soundness by adding one table after another.
-/
def PartialBalancedChannel (tables : Tables F) (channel : RawChannel F) : Prop :=
  -- `extraInteractions` represents the unknown interactions from tables added later
  ∃ extraInteractions : List (Interaction F),
    -- the total of known + unknown interactions is balanced
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
lemma partialBalancedChannel_of_balancedInteractions {tables : Tables F} {channel : RawChannel F} :
    BalancedInteractions (tables.interactionsWith channel) → PartialBalancedChannel tables channel := by
  intro balanced
  use []
  simp [balanced]

/--
For ordered channels, we can always instantiate partial balance at an initial sublist.
-/
theorem partialBalancedChannel_of_cons_of_orderedChannelLt
  {table : Table F} {tables : Tables F} (same_data : table.data = tables.data)
  {channel : RawChannel F} :
  table.Constraints →
  PartialBalancedChannel (.cons table tables same_data) channel →
  OrderedChannelLt channel tables.components [table.component] →
    PartialBalancedChannel tables channel := by
  rintro table_constraints ⟨ extraInteractions, balanced, same_channel, extra_reqs_or_no_grts ⟩
    not_in_reqs_or
  use table.interactionsWith channel ++ extraInteractions
  simp only [circuit_norm] at *
  simp [or_imp] at ⊢ not_in_reqs_or extra_reqs_or_no_grts
  constructor
  · apply BalancedInteractions.of_perm balanced
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
    have channel_reqs := table.requirements_of_not_mem_of_constraints table_constraints channel_not_in_reqs
    rw [Table.channelRequirements_iff_forall, same_data] at channel_reqs
    exact ⟨ channel_reqs, extra_reqs ⟩

/--
For ordered channels, we can always instantiate partial balance at an initial sublist.
-/
lemma partialBalancedChannel_of_cons_of_orderedChannel
  {table : Table F} {tables : Tables F} (same_data : table.data = tables.data)
  {channel : RawChannel F} :
  table.Constraints →
  PartialBalancedChannel (tables.cons table same_data) channel →
  OrderedChannel channel (table.component :: tables.components) →
    PartialBalancedChannel tables channel := by
  intro table_constraints partial_balance ordered_channel
  apply partialBalancedChannel_of_cons_of_orderedChannelLt same_data table_constraints partial_balance
  simp_all [circuit_norm]

/--
The significance of `OrderedChannel` is that it lets us prove soundness
on a list of tables by induction. This lemma captures the main step.
-/
lemma guarantees_of_requirements_cons
  -- given a list of tables, and one additional table
  {table : Table F} {tables : Tables F} (same_data : table.data = tables.data)
  -- and a channel that is consistent, ordered on the new table, and partially balanced on the combined tables
  {channel : RawChannel F} [channel.Consistent] :
  table.Constraints →
  OrderedChannelRefl channel table.component →
  PartialBalancedChannel (tables.cons table same_data) channel →
  -- the channel requirements on the old tables imply guarantees on the new table
  (∀ table ∈ tables.tables, table.ChannelRequirements channel) →
    table.ChannelGuarantees channel := by
  rintro table_constraints ordered_channel partial_balance ih
  /-
  thanks to ordered channel, we know that channel cannot add _both_ grts and reqs for the new table.
  1) if the channel does not add grts, we're done as the grts are trivially satisifed.
  2) if the channel does not add reqs, we can prove that _all_ reqs of that channel are satisfied.
      using consistent channels, we conclude the channel's guarantees.
  -/
  simp only [circuit_norm] at ordered_channel
  rcases ordered_channel with grts | reqs
  · exact table.guarantees_of_not_mem grts
  replace reqs := table.requirements_of_not_mem_of_constraints table_constraints reqs
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
lemma partialBalancedChannel_of_sublist {subtables tables : Tables F} {channel : RawChannel F} :
  PartialBalancedChannel tables channel →
  (∃ otherTables, tables.tables.Perm (subtables.tables ++ otherTables) ∧
    (∀ table ∈ otherTables, table.Constraints) ∧
    ∀ table ∈ otherTables, channel ∉ table.channelsWithRequirements) →
    PartialBalancedChannel subtables channel := by
  rintro ⟨ extraInteractions, balanced, same_channel, no_grts_or_extra_reqs ⟩ subset_tables
  obtain ⟨ otherTables, perm, otherConstraints, otherReqs ⟩ := subset_tables
  by_cases subtables_empty : subtables.tables = []
  · simp [subtables_empty, circuit_norm, PartialBalancedChannel, Tables.interactionsWith]
    use []
    simp [BalancedInteractions.nil]
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
    apply Table.requirements_of_not_mem_of_constraints
    exact otherConstraints _ ht
    exact otherReqs _ ht
  -- balance
  apply BalancedInteractions.of_perm balanced
  simp only [Tables.interactionsWith]
  grw [← List.append_assoc, List.perm_append_right_iff, ← List.flatMap_append, perm.flatMap]
  exact fun _ _ => List.Perm.refl _

/--
The argument of `guarantees_of_requirements_cons`
also works for adding multiple new tables, if we make the assumption a bit stronger:
We can no longer continue to introduce guarantees for the channel.

This is relevant later when we add VM channels on top of an already finished, sound ensemble.
-/
lemma guarantees_of_requirements_append
  -- given two lists of tables
  {ts ss : Tables F} (same_data : ts.data = ss.data)
  -- and a channel that is consistent, _doesn't add requirements_ on the new tables,
  -- and is partially balanced on the combined tables
  {channel : RawChannel F} [channel.Consistent] :
  (∀ table ∈ ts.tables, table.Constraints) →
  (∀ table ∈ ts.tables, channel ∉ table.component.circuit.channelsWithRequirements) →
  PartialBalancedChannel (ts.append ss same_data) channel →
  -- the channel requirements on the old tables imply guarantees on the new tables
  (∀ table ∈ ss.tables, table.ChannelRequirements channel) →
    ∀ table ∈ ts.tables, table.ChannelGuarantees channel := by
  -- we show that for each (t, ss) pair, the assumptions of `*_cons` hold
  rintro constraints reqs partial_balance ih table h_table
  have same_data' : table.data = ss.data := by
    rw [ts.same_data _ h_table, same_data]
  apply guarantees_of_requirements_cons (tables := ss) same_data' (constraints _ h_table) ?_ ?_ ih
  · right; exact reqs _ h_table
  -- get partial balance by sublist/permutation argument
  apply partialBalancedChannel_of_sublist partial_balance
  obtain ⟨ i, hi, h' ⟩ := List.getElem_of_mem h_table
  symm at h'; subst h'
  use ts.tables.eraseIdx i
  constructor
  · simp [circuit_norm]
    grw [List.perm_append_comm, List.perm_cons_append_cons _ List.perm_rfl,
      List.perm_append_left_iff, List.perm_comm]
    apply List.getElem_cons_eraseIdx_perm
  constructor
  · intro t' ht'
    exact constraints _ (List.mem_of_mem_eraseIdx ht')
  · intro t' ht'
    apply reqs _ (List.mem_of_mem_eraseIdx ht')

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
def SoundChannels (tables : List α) (finished closed : List (RawChannel F)) : Prop :=
  (∀ table ∈ tables, channelsWithGuarantees table ⊆ finished ++ closed) ∧
  (∀ channel ∈ finished, OrderedChannel channel tables) ∧
  ∀ channel ∈ finished, channel.Consistent

/-- `SoundChannels` lets us prove a soundness theorem, given the guarantees on the closed channels.
-/
theorem spec_and_guarantees_of_soundChannels {witness : Tables F}
    {finished closed : List (RawChannel F)} :
  SoundChannels (witness.tables.map (·.component)) finished closed →
  -- constraints + partial balance
  witness.Assumptions →
  witness.Constraints →
  (∀ channel ∈ finished, PartialBalancedChannel witness channel) →
  (∀ channel ∈ closed, ∀ table ∈ witness.tables, table.ChannelGuarantees channel) →
    -- implies the spec, and the guarantees and requirements on all finished channels
    ∀ table ∈ witness.tables, table.Spec ∧ ∀ channel ∈ finished,
    table.ChannelGuarantees channel ∧ table.ChannelRequirements channel := by
  -- by induction on the tables
  rintro ⟨ subset_finished, ordered_channels, consistent_channels ⟩
    assumptions constraints partial_balance closed_guarantees
  induction witness using Tables.induct
  · intro _ h_table; nomatch h_table
  -- induction step
  rename_i table tables same_data ih
  simp only [Tables.Assumptions, Tables.Constraints, circuit_norm] at *
  simp only [forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] at *
  -- first, we use the IH
  have partial_balance' c hc := by
    apply partialBalancedChannel_of_cons_of_orderedChannelLt same_data constraints.left
      (partial_balance c hc)
    rw [OrderedChannelLt]
    simp only [Tables.components, List.flatMap_singleton]
    rcases (ordered_channels c hc).2.2 with no_grts | no_reqs
    · left
      intro h_component
      rcases List.mem_flatMap.mp h_component with ⟨component, h_component, h_channel⟩
      rcases List.mem_map.mp h_component with ⟨table, h_table, rfl⟩
      exact no_grts table h_table h_channel
    · right
      exact no_reqs
  specialize ih subset_finished.right (fun c hc => (ordered_channels c hc).right.left)
    assumptions.right constraints.right partial_balance'
    (fun c hc => (closed_guarantees c hc).2)
  constructor; swap
  · exact ih
  -- the guarantees of the finished channels follow from `guarantees_of_requirements_cons`
  have finished_guarantees : ∀ channel ∈ finished, table.ChannelGuarantees channel := by
    intro channel h_channel
    have : channel.Consistent := consistent_channels _ h_channel
    have orderedChannelRefl : OrderedChannelRefl channel table.component := by
      simp only [circuit_norm, ordered_channels channel h_channel]
    apply guarantees_of_requirements_cons same_data
      constraints.left orderedChannelRefl (partial_balance channel h_channel)
    intro t ht
    exact (ih t ht).right _ h_channel |>.right
  -- with the guarantees of the closed channels, the constraints imply the requirements
  have results := (iff_guarantees_of_constraints assumptions.left constraints.left
    subset_finished.left).mpr fun channel h_channel =>
      (List.mem_append.mp h_channel).elim (finished_guarantees channel)
        fun h_closed => (closed_guarantees channel h_closed).1
  exact ⟨ results.left, fun channel h_channel =>
    results.right channel (List.mem_append_left _ h_channel) ⟩

namespace Air.Flat
variable {PublicIO : TypeMap} [ProvableType PublicIO]

namespace Ensemble
@[circuit_norm]
def OrderedChannel (ens : Ensemble F PublicIO) (channel : RawChannel F) : Prop :=
  _root_.OrderedChannelRefl channel ens.verifier ∧
  _root_.OrderedChannel channel ens.tables ∧
  _root_.OrderedChannelLt channel ens.tables [ens.verifier]

@[circuit_norm]
abbrev OrderedChannels (ens : Ensemble F PublicIO) (finished : List (RawChannel F)) : Prop :=
  ∀ channel ∈ finished, ens.OrderedChannel channel

/-- The `ordered` channels are ordered and consistent, and every guarantee comes from an ordered or
a `closed` channel. -/
@[circuit_norm]
def SoundChannels (ens : Ensemble F PublicIO) (ordered closed : List (RawChannel F)) : Prop :=
  ens.channelsWithGuarantees ⊆ ordered ++ closed ∧
  ens.OrderedChannels ordered ∧
  ∀ channel ∈ ordered, channel.Consistent

lemma partialBalancedChannel_of_balancedChannel {ens : Ensemble F PublicIO}
    {witness : EnsembleWitness ens} {channel : RawChannel F} :
    ens.OrderedChannel channel →
    witness.BalancedChannel channel →
      PartialBalancedChannel witness.toTables channel := by
  intro ordered balanced
  use witness.verifierInteractionsWith channel
  constructor
  · apply BalancedInteractions.of_perm balanced
    apply List.perm_append_comm
  constructor
  · intro interaction h_interaction
    apply witness.channel_eq_of_mem_interactionsWith
    simp [EnsembleWitness.interactionsWith, h_interaction]
  rcases ordered.right.right with no_table_guarantees | no_verifier_requirements
  · left
    simp only [circuit_norm, Table.channelsWithGuarantees] at no_table_guarantees ⊢
    exact fun table h_table =>
      no_table_guarantees _ (EnsembleWitness.component_mem_tables_of_mem h_table)
  · right
    rw [witness.toTables_data, ← witness.verifierChannelRequirements_iff_forall]
    apply ens.verifierChannelRequirements_of_not_mem
    simp_all [circuit_norm]

lemma verifierChannelGuarantees_of_tableRequirements {ens : Ensemble F PublicIO}
    {witness : EnsembleWitness ens} {channel : RawChannel F} [channel.Consistent] :
    OrderedChannelRefl channel ens.verifier →
    witness.BalancedChannel channel →
    (∀ table ∈ witness.tables, table.ChannelRequirements channel) →
      ens.VerifierChannelGuarantees witness.publicInput witness.data channel := by
  intro ordered balanced table_requirements
  rcases ordered with no_verifier_guarantees | no_verifier_requirements
  · exact ens.verifierChannelGuarantees_of_not_mem _ _ no_verifier_guarantees
  have verifier_requirements :=
    ens.verifierChannelRequirements_of_not_mem witness.publicInput witness.data
      no_verifier_requirements
  rw [witness.verifierChannelRequirements_iff_forall] at verifier_requirements
  -- all interactions satisfy their requirements, so by consistency they satisfy their guarantees
  have all_guarantees :=
    ‹channel.Consistent›.consistent (witness.interactionsWith channel) witness.data balanced (by
    intro interaction h_interaction
    refine ⟨witness.channel_eq_of_mem_interactionsWith h_interaction, ?_⟩
    rw [witness.mem_interactionsWith] at h_interaction
    rcases h_interaction with h_verifier | ⟨table, h_table, h_interaction⟩
    · exact verifier_requirements interaction h_verifier
    have requirements := table_requirements table h_table
    rw [Table.channelRequirements_iff_forall, witness.same_data table h_table] at requirements
    exact requirements interaction h_interaction)
  rw [witness.verifierChannelGuarantees_iff_forall]
  exact fun interaction h_interaction =>
    all_guarantees interaction (by simp [EnsembleWitness.interactionsWith, h_interaction])

/--
Main result of this section:
`SoundChannels` (an easily checkable property) implies
`TableSoundness`, a complex ensemble-level soundness statement, given the guarantees on the closed
channels.
-/
theorem tableSoundness_of_soundChannels {ens : Ensemble F PublicIO} {balance : Balance F}
    {ordered closed : List (RawChannel F)} (ordered_subset : ordered ⊆ ens.channels)
    (sound_channels : ens.SoundChannels ordered closed)
    (closed_guarantees : ∀ witness : EnsembleWitness ens, witness.Assumptions →
      witness.Constraints → witness.Balanced balance →
      ∀ channel ∈ closed, ∀ i ∈ witness.interactionsWith channel, i.Guarantees witness.data) :
    ens.TableSoundness balance := by
  obtain ⟨ subset_finished, ordered_channels, consistent ⟩ := sound_channels
  intro witness assumptions constraints balanced
  have balance := witness.balancedChannels_of_balanced balanced
  have closed_grts := closed_guarantees witness assumptions constraints balanced
  rw [channelsWithGuarantees_subset_iff] at subset_finished
  -- the tables are sound by themselves, given partial balance
  have table_results := spec_and_guarantees_of_soundChannels (witness := witness.toTables)
    (closed := closed) (by simp_all [circuit_norm, witness.tables_map_component])
    assumptions constraints
    (fun channel h_channel =>
      partialBalancedChannel_of_balancedChannel
        (ordered_channels channel h_channel) (balance _ (ordered_subset h_channel)))
    (fun channel h_channel table h_table => by
      rw [Table.channelGuarantees_iff_forall, witness.same_data table h_table]
      intro i h_i
      apply closed_grts channel h_channel i
      rw [witness.mem_interactionsWith]
      exact .inr ⟨table, h_table, h_i⟩)
  -- their requirements imply the verifier guarantees
  refine ⟨ens.verifierSpec_of_verifierGuarantees _ _ ?_,
    fun table h_table => (table_results table h_table).left⟩
  rw [verifierGuarantees_iff]
  intro channel h_channel
  rcases List.mem_append.mp (subset_finished.left h_channel) with h_ordered | h_closed
  · have := consistent channel h_ordered
    apply verifierChannelGuarantees_of_tableRequirements (ordered_channels channel h_ordered).left
      (balance channel (ordered_subset h_ordered))
    exact fun table h_table => ((table_results table h_table).right channel h_ordered).right
  · rw [witness.verifierChannelGuarantees_iff_forall]
    intro i h_i
    apply closed_grts channel h_closed i
    rw [witness.mem_interactionsWith]
    exact .inl h_i

/-- Empty ensemble satisfies SoundChannels -/
theorem empty_soundChannels : (empty F PublicIO).SoundChannels [] [] := by
  simp only [circuit_norm]

-- adding one table to a SoundChannels ensemble preserves SoundChannels under some
-- easy-to-prove assumptions on what channels the new table uses
theorem orderedChannels_of_soundChannels_addTable (ens : Ensemble F PublicIO)
  (table : Component F) (fresh : table.circuit.name ∉ ens.tables.map (·.circuit.name))
  (table_channels : table.circuit.channels ⊆ ens.channels) {finished : List (RawChannel F)} :
    -- given an ensemble with ordered channels and empty verifier,
    ens.OrderedChannels finished →
    ens.verifier = .empty F PublicIO →
    -- assuming that the table's channelsWithRequirements contain none of the ordered ones
    -- (so that we don't get new requirements to prove)
    (∀ channel ∈ finished, channel ∉ table.circuit.channelsWithRequirements) →
    -- the ensemble with the new table has the same ordered channels!
    (ens.addTable table fresh table_channels).OrderedChannels finished := by
  intro h_sound verifier_empty reqs_disjoint_finished channel h_channel
  -- we need to make use of soundness of the original ensemble; that'll give us most of what we need
  simp only [circuit_norm, verifier_empty] at h_sound ⊢
  -- proof is a trivial combination of the hypotheses
  simp_all

theorem orderedChannels_of_soundChannels_merge (ens1 ens2 : Ensemble F PublicIO)
  (unique_names : ((ens2.tables ++ ens1.tables).map (·.circuit.name)).Nodup)
  (unique_channel_names : ((ens2.channels ++ ens1.channels).map (·.name)).Nodup)
  {finished : List (RawChannel F)} :
    -- given an ensemble with ordered channels and empty verifier,
    ens1.OrderedChannels finished →
    ens1.verifier = .empty F PublicIO →
    -- assuming that the new tables' channelsWithRequirements contain none of the finished channels
    (∀ channel ∈ finished, channel ∉ ens2.channelsWithRequirements) →
    -- the merged ensemble with the new table satisfies OrderedChannels!
    (ens1.merge ens2 unique_names unique_channel_names).OrderedChannels finished := by
  intro h_sound verifier_empty reqs_disjoint_finished channel h_channel
  simp only [circuit_norm] at h_sound ⊢
  simp only [channelsWithRequirements_eq_verifier_append, circuit_norm] at reqs_disjoint_finished
  simp_all only [not_false_eq_true, or_true, true_and, and_true]
  constructor
  · apply orderedChannel_of_no_requirements
    simp_all [circuit_norm]
  · apply orderedChannelLt_of_no_requirements
    simp_all [circuit_norm]

theorem soundChannels_markFinished (ens : Ensemble F PublicIO)
    -- given a sound channels ensemble with lists of ordered and closed channels
    {ordered closed : List (RawChannel F)} (h_sound : ens.SoundChannels ordered closed)
    -- and given a new consistent channel to mark as finished
    (channel : RawChannel F) [channel.Consistent] (h_closed : channel ∉ closed) :
    -- the ensemble also satisfies SoundChannels including the new channel in the ordered list
    ens.SoundChannels (channel :: ordered) closed := by
  rcases h_sound with ⟨subset_finished, ordered_channels, consistent_channels⟩
  refine ⟨fun c h_c => ?_, ?_, by simp_all⟩
  · rcases List.mem_append.mp (subset_finished h_c) with h | h
    · exact List.mem_append_left _ (List.mem_cons_of_mem _ h)
    · exact List.mem_append_right _ h
  by_cases h_finished : channel ∈ ordered
  · simp_all [OrderedChannels]
  -- the new channel has no guarantees, so it is trivially ordered
  have no_guarantees : channel ∉ ens.channelsWithGuarantees := fun h =>
    (List.mem_append.mp (subset_finished h)).elim h_finished h_closed
  simp only [channelsWithGuarantees_eq_verifier_append, circuit_norm] at no_guarantees
  simp_all [circuit_norm, orderedChannel_of_no_guarantees]
end Ensemble

/--
A closed channel: a channel whose guarantees follow from the balance check by an argument about the
components that push to it, its owners, like offline memory checking. Other components may pull
from it, but not push: in a witness where they and the verifier satisfy their requirements on the
channel, every interaction gets its guarantee.
-/
structure ClosedChannel (F : Type) [FiniteField F] (balance : Balance F) where
  channel : RawChannel F
  owners : List (Component F)
  guarantees_of_balanced : ∀ {PublicIO : TypeMap} [ProvableType PublicIO]
    {ens : Ensemble F PublicIO} (witness : EnsembleWitness ens),
    witness.Assumptions → witness.Constraints →
    balance.Balanced (witness.interactionsWith channel) →
    (∀ table ∈ witness.tables, table.component ∉ owners → table.ChannelRequirements channel) →
    ens.VerifierChannelRequirements witness.publicInput witness.data channel →
    ∀ i ∈ witness.interactionsWith channel, i.Guarantees witness.data

/--
An ensemble that is sound under a balance check, built up one component at a time. Its finished
channels are those that tables added later may pull from, but not push to: the `ordered` channels,
sound by the ordered-channel argument, and the `closed` channels, sound by their own argument.
-/
structure SoundEnsemble (F : Type) [FiniteField F] (PublicIO : TypeMap) [ProvableType PublicIO]
    (balance : Balance F) extends ensemble : Ensemble F PublicIO where
  ordered : List (RawChannel F)
  ordered_consistent : ∀ channel ∈ ordered, channel.Consistent
  ordered_subset : ordered ⊆ channels
  ordered_channels : ensemble.OrderedChannels ordered
  closed : List (ClosedChannel F balance)
  closed_subset : closed.map (·.channel) ⊆ channels
  closed_requirements : ∀ closedChannel ∈ closed, ∀ table ∈ tables, table ∉ closedChannel.owners →
    closedChannel.channel ∉ table.circuit.channelsWithRequirements
  subset_finished : ensemble.channelsWithGuarantees ⊆ ordered ++ closed.map (·.channel)
  -- TODO get rid of this assumption, by being more flexible about table order
  -- => use "∃ permutation, s.t. ordered" instead of "ordered" in Ensemble.OrderedChannels
  verifier_empty : ensemble.verifier = .empty F PublicIO

attribute [circuit_norm] SoundEnsemble.ordered_consistent SoundEnsemble.ordered_subset
  SoundEnsemble.subset_finished SoundEnsemble.ordered_channels SoundEnsemble.verifier_empty

namespace SoundEnsemble
variable {balance : Balance F}

/-- The finished channels: tables added later may pull from them, but not push. -/
@[circuit_norm]
def finished (soundEns : SoundEnsemble F PublicIO balance) : List (RawChannel F) :=
  soundEns.ordered ++ soundEns.closed.map (·.channel)

lemma finished_subset (soundEns : SoundEnsemble F PublicIO balance) :
    soundEns.finished ⊆ soundEns.channels :=
  List.append_subset.mpr ⟨soundEns.ordered_subset, soundEns.closed_subset⟩

lemma soundChannels (soundEns : SoundEnsemble F PublicIO balance) :
    soundEns.SoundChannels soundEns.ordered (soundEns.closed.map (·.channel)) :=
  ⟨soundEns.subset_finished, soundEns.ordered_channels, soundEns.ordered_consistent⟩

theorem tableSoundness (soundEns : SoundEnsemble F PublicIO balance) :
    soundEns.TableSoundness balance := by
  apply soundEns.tableSoundness_of_soundChannels soundEns.ordered_subset soundEns.soundChannels
  intro witness assumptions constraints balanced channel h_channel
  obtain ⟨closedChannel, h_closed, rfl⟩ := List.mem_map.mp h_channel
  apply closedChannel.guarantees_of_balanced witness assumptions constraints
    (balanced _ (soundEns.closed_subset h_channel))
  · intro table h_table h_owner
    exact table.requirements_of_not_mem_of_constraints (constraints table h_table)
      (soundEns.closed_requirements closedChannel h_closed _
        (witness.component_mem_tables_of_mem h_table) h_owner)
  · apply soundEns.verifierChannelRequirements_of_not_mem
    simp [soundEns.verifier_empty, circuit_norm]

def empty (F : Type) [FiniteField F] (PublicIO : TypeMap) [ProvableType PublicIO]
    (balance : Balance F) : SoundEnsemble F PublicIO balance where
  ensemble := .empty F PublicIO
  ordered := []
  ordered_consistent := by simp
  ordered_subset := List.Subset.refl _
  ordered_channels := by simp [circuit_norm]
  closed := []
  closed_subset := by simp
  closed_requirements := by simp
  subset_finished := by simp [circuit_norm, Ensemble.channelsWithGuarantees]
  verifier_empty := by simp [circuit_norm]

@[circuit_norm] lemma empty_tables : (empty F PublicIO balance).tables = [] := rfl
@[circuit_norm] lemma empty_channels : (empty F PublicIO balance).channels = [] := rfl
@[circuit_norm] lemma empty_ordered : (empty F PublicIO balance).ordered = [] := rfl
@[circuit_norm] lemma empty_closed : (empty F PublicIO balance).closed = [] := rfl
@[circuit_norm] lemma empty_verifier : (empty F PublicIO balance).verifier = .empty F PublicIO :=
  rfl

/-- A table whose guarantees come from finished channels, and whose requirements go to channels of
the ensemble, only uses channels of the ensemble. -/
theorem table_channels_subset (soundEns : SoundEnsemble F PublicIO balance) (table : Component F)
    (grts_subset_finished : table.circuit.channelsWithGuarantees ⊆ soundEns.finished)
    (reqs_unfinished : ∀ channel ∈ table.circuit.channelsWithRequirements,
      channel ∈ soundEns.channels ∧ channel ∉ soundEns.finished) :
    table.circuit.channels ⊆ soundEns.channels := by
  intro channel h_channel
  rcases List.mem_append.mp h_channel with h_channel | h_channel
  · exact soundEns.finished_subset (grts_subset_finished h_channel)
  · exact (reqs_unfinished channel h_channel).1

/-- Add a table whose guarantees come from finished channels, and whose requirements go to channels
of the ensemble that aren't finished yet. -/
@[circuit_norm]
def addTable (soundEns : SoundEnsemble F PublicIO balance) (table : Component F)
    (grts_subset_finished : table.circuit.channelsWithGuarantees ⊆ soundEns.finished
      := by simp [circuit_norm])
    (reqs_unfinished : ∀ channel ∈ table.circuit.channelsWithRequirements,
      channel ∈ soundEns.channels ∧ channel ∉ soundEns.finished := by simp [circuit_norm])
    (fresh : table.circuit.name ∉ soundEns.tables.map (·.circuit.name) := by simp [circuit_norm])
    : SoundEnsemble F PublicIO balance where
  ensemble := soundEns.ensemble.addTable table fresh
    (soundEns.table_channels_subset table grts_subset_finished reqs_unfinished)
  ordered := soundEns.ordered
  ordered_consistent := soundEns.ordered_consistent
  ordered_subset := soundEns.ordered_subset
  ordered_channels := soundEns.orderedChannels_of_soundChannels_addTable table fresh _
    soundEns.ordered_channels soundEns.verifier_empty
    fun channel h_ordered h_channel =>
      (reqs_unfinished channel h_channel).2 (List.mem_append_left _ h_ordered)
  closed := soundEns.closed
  closed_subset := soundEns.closed_subset
  closed_requirements := by
    intro closedChannel h_closed table' h_table' h_owner h_channel
    rcases List.mem_cons.mp h_table' with rfl | h_table'
    · exact (reqs_unfinished _ h_channel).2
        (List.mem_append_right _ (List.mem_map_of_mem h_closed))
    · exact soundEns.closed_requirements closedChannel h_closed table' h_table' h_owner h_channel
  subset_finished := by
    have h := soundEns.subset_finished
    rw [Ensemble.channelsWithGuarantees_subset_iff] at h ⊢
    simp only [Ensemble.addTable_verifier, Ensemble.addTable_tables, List.forall_mem_cons]
    exact ⟨h.1, grts_subset_finished, h.2⟩
  verifier_empty := soundEns.verifier_empty

variable {soundEns : SoundEnsemble F PublicIO balance} {table : Component F}
    {gsf : table.circuit.channelsWithGuarantees ⊆ soundEns.finished}
    {reqs : ∀ channel ∈ table.circuit.channelsWithRequirements,
      channel ∈ soundEns.channels ∧ channel ∉ soundEns.finished}
    {fresh : table.circuit.name ∉ soundEns.tables.map (·.circuit.name)}

@[circuit_norm] lemma addTable_tables :
  (soundEns.addTable table gsf reqs fresh).tables = table :: soundEns.tables := rfl
@[circuit_norm] lemma addTable_channels :
  (soundEns.addTable table gsf reqs fresh).channels = soundEns.channels := rfl
@[circuit_norm] lemma addTable_ordered :
  (soundEns.addTable table gsf reqs fresh).ordered = soundEns.ordered := rfl
@[circuit_norm] lemma addTable_closed :
  (soundEns.addTable table gsf reqs fresh).closed = soundEns.closed := rfl
@[circuit_norm] lemma addTable_verifier :
  (soundEns.addTable table gsf reqs fresh).verifier = soundEns.verifier := rfl

/-- Add a channel, whose name must be new. -/
def addChannel (soundEns : SoundEnsemble F PublicIO balance) (channel : RawChannel F)
    (fresh : channel.name ∉ soundEns.channels.map (·.name) := by simp [circuit_norm]) :
    SoundEnsemble F PublicIO balance where
  ensemble := { soundEns.ensemble with
    channels := channel :: soundEns.channels
    unique_channel_names := List.nodup_cons.mpr ⟨fresh, soundEns.unique_channel_names⟩
    tables_channels := fun table h_table =>
      List.Subset.trans (soundEns.tables_channels table h_table) (List.subset_cons_self _ _)
    verifier_channels := List.Subset.trans soundEns.verifier_channels (List.subset_cons_self _ _) }
  ordered := soundEns.ordered
  ordered_consistent := soundEns.ordered_consistent
  ordered_subset := List.Subset.trans soundEns.ordered_subset (List.subset_cons_self _ _)
  ordered_channels := soundEns.ordered_channels
  closed := soundEns.closed
  closed_subset := List.Subset.trans soundEns.closed_subset (List.subset_cons_self _ _)
  closed_requirements := soundEns.closed_requirements
  subset_finished := soundEns.subset_finished
  verifier_empty := soundEns.verifier_empty

section
variable {channel : RawChannel F} {fresh : channel.name ∉ soundEns.channels.map (·.name)}

@[circuit_norm] lemma addChannel_channels :
  (soundEns.addChannel channel fresh).channels = channel :: soundEns.channels := rfl
@[circuit_norm] lemma addChannel_tables :
  (soundEns.addChannel channel fresh).tables = soundEns.tables := rfl
@[circuit_norm] lemma addChannel_ordered :
  (soundEns.addChannel channel fresh).ordered = soundEns.ordered := rfl
@[circuit_norm] lemma addChannel_closed :
  (soundEns.addChannel channel fresh).closed = soundEns.closed := rfl
@[circuit_norm] lemma addChannel_verifier :
  (soundEns.addChannel channel fresh).verifier = soundEns.verifier := rfl
end

/-- Finish a consistent channel: from now on, tables may only pull from it. -/
def markFinished (soundEns : SoundEnsemble F PublicIO balance) (channel : RawChannel F)
    [channel.Consistent]
    (h_mem : channel ∈ soundEns.channels := by simp [circuit_norm])
    (not_closed : channel ∉ soundEns.closed.map (·.channel) := by simp [circuit_norm]) :
    SoundEnsemble F PublicIO balance where
  ensemble := soundEns.ensemble
  ordered := channel :: soundEns.ordered
  ordered_consistent := by
    intro channel' h_mem_channel
    rw [List.mem_cons] at h_mem_channel
    rcases h_mem_channel with rfl | h_mem_tail
    · assumption
    · exact soundEns.ordered_consistent channel' h_mem_tail
  ordered_subset := List.cons_subset.mpr ⟨h_mem, soundEns.ordered_subset⟩
  ordered_channels :=
    (soundEns.soundChannels_markFinished soundEns.soundChannels channel not_closed).right.left
  closed := soundEns.closed
  closed_subset := soundEns.closed_subset
  closed_requirements := soundEns.closed_requirements
  subset_finished :=
    (soundEns.soundChannels_markFinished soundEns.soundChannels channel not_closed).left
  verifier_empty := soundEns.verifier_empty

section
variable {channel : RawChannel F} [channel.Consistent] {h_mem : channel ∈ soundEns.channels}
  {not_closed : channel ∉ soundEns.closed.map (·.channel)}

@[circuit_norm] lemma markFinished_channels :
  (soundEns.markFinished channel h_mem not_closed).channels = soundEns.channels := rfl
@[circuit_norm] lemma markFinished_tables :
  (soundEns.markFinished channel h_mem not_closed).tables = soundEns.tables := rfl
@[circuit_norm] lemma markFinished_ordered :
  (soundEns.markFinished channel h_mem not_closed).ordered = channel :: soundEns.ordered := rfl
@[circuit_norm] lemma markFinished_closed :
  (soundEns.markFinished channel h_mem not_closed).closed = soundEns.closed := rfl
end

/-- Add a channel that no table pushes to, as finished. Its name must be new. -/
def addFinishedChannel (soundEns : SoundEnsemble F PublicIO balance) (channel : RawChannel F)
    [channel.Consistent]
    (fresh : channel.name ∉ soundEns.channels.map (·.name) := by simp [circuit_norm]) :
    SoundEnsemble F PublicIO balance :=
  soundEns
    |>.addChannel channel fresh
    |>.markFinished channel (List.mem_cons_self ..)
      fun h => fresh (List.mem_map.mpr ⟨channel, soundEns.closed_subset h, rfl⟩)

section
variable {channel : RawChannel F} [channel.Consistent]
  {fresh : channel.name ∉ soundEns.channels.map (·.name)}

@[circuit_norm] lemma addFinishedChannel_channels :
  (soundEns.addFinishedChannel channel fresh).channels = channel :: soundEns.channels := rfl
@[circuit_norm] lemma addFinishedChannel_tables :
  (soundEns.addFinishedChannel channel fresh).tables = soundEns.tables := rfl
@[circuit_norm] lemma addFinishedChannel_ordered :
  (soundEns.addFinishedChannel channel fresh).ordered = channel :: soundEns.ordered := rfl
@[circuit_norm] lemma addFinishedChannel_closed :
  (soundEns.addFinishedChannel channel fresh).closed = soundEns.closed := rfl
end

/-- Add a closed channel with its owners, which may push to it and pull from it. Other guarantees
of the owners come from finished channels, and their other requirements go to channels of the
ensemble that aren't finished yet. -/
def addClosedChannel (soundEns : SoundEnsemble F PublicIO balance)
    (closed : ClosedChannel F balance)
    (fresh_channel : closed.channel.name ∉ soundEns.channels.map (·.name) := by simp [circuit_norm])
    (grts_subset_finished : ∀ owner ∈ closed.owners,
      owner.circuit.channelsWithGuarantees ⊆ closed.channel :: soundEns.finished
      := by simp [circuit_norm])
    (reqs_unfinished : ∀ owner ∈ closed.owners, ∀ channel ∈ owner.circuit.channelsWithRequirements,
      channel = closed.channel ∨ channel ∈ soundEns.channels ∧ channel ∉ soundEns.finished
      := by simp [circuit_norm])
    (names : ((closed.owners ++ soundEns.tables).map (·.circuit.name)).Nodup
      := by simp [circuit_norm]) :
    SoundEnsemble F PublicIO balance :=
  have not_mem : closed.channel ∉ soundEns.channels :=
    fun h => fresh_channel (List.mem_map_of_mem h)
  have ne_of_mem {channel} (h : channel ∈ soundEns.channels) : channel ≠ closed.channel :=
    fun h_eq => not_mem (h_eq ▸ h)
  have owner_reqs (owner) (h_owner : owner ∈ closed.owners) (channel) (h : channel ∈ soundEns.finished) :
      channel ∉ owner.circuit.channelsWithRequirements := fun h_req =>
    (reqs_unfinished owner h_owner channel h_req).elim
      (ne_of_mem (soundEns.finished_subset h)) (fun h' => h'.2 h)
  { ensemble := { soundEns.ensemble with
      channels := closed.channel :: soundEns.channels
      unique_channel_names := List.nodup_cons.mpr ⟨fresh_channel, soundEns.unique_channel_names⟩
      tables := closed.owners ++ soundEns.tables
      unique_names := names
      tables_channels := by
        intro table h_table channel h_channel
        rcases List.mem_append.mp h_table with h_owner | h_table
        · rcases List.mem_append.mp h_channel with h_channel | h_channel
          · rcases List.mem_cons.mp (grts_subset_finished table h_owner h_channel) with rfl | h
            · exact List.mem_cons_self ..
            · exact List.mem_cons_of_mem _ (soundEns.finished_subset h)
          · rcases reqs_unfinished table h_owner channel h_channel with rfl | h
            · exact List.mem_cons_self ..
            · exact List.mem_cons_of_mem _ h.1
        · exact List.mem_cons_of_mem _ (soundEns.tables_channels table h_table h_channel)
      verifier_channels :=
        List.Subset.trans soundEns.verifier_channels (List.subset_cons_self _ _) }
    ordered := soundEns.ordered
    ordered_consistent := soundEns.ordered_consistent
    ordered_subset := List.Subset.trans soundEns.ordered_subset (List.subset_cons_self _ _)
    ordered_channels := by
      intro channel h_ordered
      have h_finished : channel ∈ soundEns.finished := List.mem_append_left _ h_ordered
      have ordered := soundEns.ordered_channels channel h_ordered
      simp only [Ensemble.OrderedChannel, soundEns.verifier_empty] at ordered ⊢
      refine ⟨ordered.1, ?_, ?_⟩
      · rw [orderedChannel_append]
        refine ⟨orderedChannel_of_no_requirements fun owner h_owner =>
          owner_reqs owner h_owner channel h_finished, ordered.2.1,
          orderedChannelLt_of_no_requirements fun owner h_owner =>
            owner_reqs owner h_owner channel h_finished⟩
      · rw [orderedChannelLt_append_left]
        refine ⟨?_, ordered.2.2⟩
        apply orderedChannelLt_of_no_requirements
        simp [circuit_norm]
    closed := closed :: soundEns.closed
    closed_subset := by
      intro channel h_channel
      rcases List.mem_cons.mp h_channel with rfl | h_channel
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (soundEns.closed_subset h_channel)
    closed_requirements := by
      intro closedChannel h_closed table h_table h_owner h_channel
      rcases List.mem_cons.mp h_closed with rfl | h_closed
      · rcases List.mem_append.mp h_table with h_table | h_table
        · exact h_owner h_table
        · exact not_mem (soundEns.tables_channels table h_table (List.mem_append_right _ h_channel))
      · rcases List.mem_append.mp h_table with h_table | h_table
        · exact owner_reqs table h_table _
            (List.mem_append_right _ (List.mem_map_of_mem h_closed)) h_channel
        · exact soundEns.closed_requirements closedChannel h_closed table h_table h_owner h_channel
    subset_finished := by
      have h := soundEns.subset_finished
      rw [Ensemble.channelsWithGuarantees_subset_iff] at h ⊢
      refine ⟨fun channel h_channel => ?_, fun table h_table channel h_channel => ?_⟩
      · rcases List.mem_append.mp (h.1 h_channel) with h | h
        · exact List.mem_append_left _ h
        · exact List.mem_append_right _ (List.mem_cons_of_mem _ h)
      rcases List.mem_append.mp h_table with h_owner | h_table
      · rcases List.mem_cons.mp (grts_subset_finished table h_owner h_channel) with rfl | h
        · simp
        · rcases List.mem_append.mp h with h | h
          · exact List.mem_append_left _ h
          · exact List.mem_append_right _ (List.mem_cons_of_mem _ h)
      · rcases List.mem_append.mp (h.2 table h_table h_channel) with h | h
        · exact List.mem_append_left _ h
        · exact List.mem_append_right _ (List.mem_cons_of_mem _ h)
    verifier_empty := soundEns.verifier_empty }

section
variable {closed : ClosedChannel F balance}
  {fresh : closed.channel.name ∉ soundEns.channels.map (·.name)}
  {grts : ∀ owner ∈ closed.owners,
    owner.circuit.channelsWithGuarantees ⊆ closed.channel :: soundEns.finished}
  {reqs : ∀ owner ∈ closed.owners, ∀ channel ∈ owner.circuit.channelsWithRequirements,
    channel = closed.channel ∨ channel ∈ soundEns.channels ∧ channel ∉ soundEns.finished}
  {names : ((closed.owners ++ soundEns.tables).map (·.circuit.name)).Nodup}

@[circuit_norm] lemma addClosedChannel_channels :
  (soundEns.addClosedChannel closed fresh grts reqs names).channels =
    closed.channel :: soundEns.channels := rfl
@[circuit_norm] lemma addClosedChannel_tables :
  (soundEns.addClosedChannel closed fresh grts reqs names).tables =
    closed.owners ++ soundEns.tables := rfl
@[circuit_norm] lemma addClosedChannel_ordered :
  (soundEns.addClosedChannel closed fresh grts reqs names).ordered = soundEns.ordered := rfl
@[circuit_norm] lemma addClosedChannel_closed :
  (soundEns.addClosedChannel closed fresh grts reqs names).closed = closed :: soundEns.closed :=
  rfl
@[circuit_norm] lemma addClosedChannel_verifier :
  (soundEns.addClosedChannel closed fresh grts reqs names).verifier = soundEns.verifier := rfl
end

/-- The formal ensemble, from the ensemble-level assumptions and spec, and the prover assumptions
that witness generation needs. -/
def toFormal (soundEns : SoundEnsemble F PublicIO balance)
    (Assumptions Spec : PublicIO F → Prop)
    (assumptionsConsistency : soundEns.AssumptionsConsistency Assumptions)
    (specConsistency : soundEns.SpecConsistency Spec)
    (ProverAssumptions : PublicIO F → soundEns.ProverInput F → Prop := fun _ _ => True) :
    FormalEnsemble F PublicIO balance where
  ensemble := soundEns.ensemble
  Assumptions := Assumptions
  Spec := Spec
  ProverAssumptions
  soundness := soundEns.soundness_of_tableSoundness_and_specConsistency
    balance Assumptions Spec soundEns.tableSoundness assumptionsConsistency specConsistency
end SoundEnsemble
end Air.Flat
