module

public import Clean.Air.Memory

@[expose] public section

/-!
# Counter channels

A counter channel is a channel of states that carry a counter, like the state channel of a VM with
a clock: every row of its owners pulls a state and pushes a successor, whose counter is the pulled
counter times a primitive element `g`. Each row is sound on its own, in that the guarantee of the
pulled state implies the requirement of the pushed one.

Such a channel is closed: all its guarantees hold, not just those on the cycle through the
verifier's states. A pull whose guarantee fails can only be matched by a row whose own pull fails,
with the counter divided by `g`, so failures form a cycle of `orderOf g` rows, more than there can
be interactions.
-/

variable {F : Type} [FiniteField F]

namespace Air.Flat.CounterChannel

/--
The counting argument of counter channels. Messages that are pulled, pushed, and each pushed by a
step from another such message, with the counter times `g`, would form a chain of `orderOf g`
distinct messages, each pulled and pushed: more interactions than there are.
-/
theorem not_bad {α : Type} {g : F} (h_order : orderOf g = FiniteField.size F - 1)
    (counter : α → F) (key : Interaction F → α) (interactions : List (Interaction F))
    (length_lt : interactions.length < FiniteField.size F) (Bad : α → Prop)
    (h_bad : ∀ message, Bad message →
      (∃ i ∈ interactions, i.direction = .pull ∧ key i = message) ∧
      (∃ i ∈ interactions, i.direction = .push ∧ key i = message) ∧
      ∃ previous, Bad previous ∧ counter previous ≠ 0 ∧ counter message = counter previous * g) :
    ∀ message, ¬Bad message := by
  classical
  intro first h_first
  have size_pos := FiniteField.fieldSize_pos (F := F)
  have g_ne_zero : g ≠ 0 := by
    rintro rfl
    have : orderOf (0 : F) = 0 := orderOf_eq_zero_iff'.mpr fun n hn => by simp [hn.ne']
    omega
  -- the chain of bad messages, following each one's previous message
  let previous (message : {message // Bad message}) : {message // Bad message} :=
    ⟨(h_bad _ message.2).2.2.choose, (h_bad _ message.2).2.2.choose_spec.1⟩
  let chain (k : ℕ) : {message // Bad message} := previous^[k] ⟨first, h_first⟩
  have counter_ne_zero (message : {message // Bad message}) : counter message.1 ≠ 0 := by
    obtain ⟨-, h_ne, h_eq⟩ := (h_bad _ message.2).2.2.choose_spec
    rw [h_eq]
    exact mul_ne_zero h_ne g_ne_zero
  have counter_chain (k : ℕ) : counter first = counter (chain k).1 * g ^ k := by
    induction k with
    | zero => simp [chain]
    | succ k ih =>
      have h_eq := ((h_bad _ (chain k).2).2.2.choose_spec).2.2
      rw [ih, h_eq, pow_succ', mul_assoc]
      simp only [chain, Function.iterate_succ_apply', previous]
  have injOn : Set.InjOn (fun k => (chain k).1) (Finset.range (orderOf g)) := by
    intro k hk j hj h_eq
    have h := (counter_chain k).symm.trans (counter_chain j)
    simp only at h_eq
    rw [h_eq, mul_right_inj' (counter_ne_zero _)] at h
    exact pow_injOn_Iio_orderOf (by simpa using hk) (by simpa using hj) h
  let messages := (Finset.range (orderOf g)).image fun k => (chain k).1
  have card_messages : messages.card = orderOf g := by
    rw [Finset.card_image_of_injOn injOn, Finset.card_range]
  -- each message is pulled and pushed
  have card_le (direction : Direction)
      (h : ∀ message ∈ messages, ∃ i ∈ interactions, i.direction = direction ∧ key i = message) :
      orderOf g ≤ (interactions.filter (·.direction = direction)).length := by
    rw [← card_messages]
    calc messages.card ≤ ((interactions.filter (·.direction = direction)).map key).toFinset.card := by
          apply Finset.card_le_card
          intro message h_message
          obtain ⟨i, h_i, h_direction, rfl⟩ := h message h_message
          simp only [List.mem_toFinset, List.mem_map, List.mem_filter, decide_eq_true_eq]
          exact ⟨i, ⟨h_i, h_direction⟩, rfl⟩
      _ ≤ _ := (List.toFinset_card_le _).trans (by simp)
  have pulls := card_le .pull fun message h_message => by
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp h_message
    exact (h_bad _ (chain k).2).1
  have pushes := card_le .push fun message h_message => by
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp h_message
    exact (h_bad _ (chain k).2).2.1
  have bound := Memory.length_filter_add_length_filter_le interactions
    (fun i => decide (i.direction = .push)) (fun i => decide (i.direction = .pull))
    (fun i _ h_push h_pull => by simp_all)
  omega

end Air.Flat.CounterChannel

namespace Air.Flat
variable {Message : TypeMap} [ProvableType Message]

/-- A channel of states with a counter, which every row of its owners advances by a primitive
element, see `Clean.Air.CounterChannel`. -/
structure CounterChannel (F : Type) [FiniteField F] (Message : TypeMap) [ProvableType Message] where
  channel : Channel F Message
  owners : List (Component F)
  counter : Message F → F
  generator : F
  orderOf_generator : orderOf generator = FiniteField.size F - 1
  /-- Every row pulls a state and pushes its successor, if enabled: the counter is nonzero and
  advances by `generator`, and the guarantee of the pulled state implies that of the pushed one. -/
  exists_step_of_constraintsHold : ∀ owner ∈ owners, ∀ env, owner.operations.ConstraintsHold env →
    ∃ (enabled : F) (pull push : Message F),
      owner.operations.interactionValuesWith channel.toRaw env =
        [channel.pulledIfValue enabled pull, channel.pushedIfValue enabled push] ∧
      IsBool enabled ∧
      (enabled = 1 → counter pull ≠ 0 ∧ counter push = counter pull * generator ∧
        (channel.Guarantees pull env.data → channel.Guarantees push env.data))

namespace CounterChannel
variable (counterChannel : CounterChannel F Message)

/-- A message as an element of `Message`, read from its elements. -/
def decode (message : Array F) : Message F :=
  fromElements (Vector.ofFn fun j : Fin (size Message) => message[j.val]?.getD 0)

lemma decode_toArray (value : Message F) :
    decode (toElements value).toArray = value := by
  rw [decode, ← ProvableType.fromElements_toElements value]
  congr 1
  ext j hj
  simp [ProvableType.fromElements_toElements]

variable {counterChannel} in
/-- Soundness of counter channels: in a witness where all components other than the owners satisfy
their requirements on the channel, all its guarantees hold. -/
theorem guarantees_of_isBalanced {balance : Balance F} [balance.LengthLtSize]
    {PublicIO : TypeMap} [ProvableType PublicIO] {ens : Ensemble F PublicIO}
    (witness : EnsembleWitness ens) (_ : witness.Assumptions)
    (constraints : witness.Constraints)
    (balanced : balance.isBalanced (ringChar F)
      (witness.interactionsWith counterChannel.channel.toRaw))
    (requirements : ∀ table ∈ witness.tables, table.component ∉ counterChannel.owners →
      table.ChannelRequirements counterChannel.channel.toRaw)
    (verifier_requirements : ens.VerifierChannelRequirements witness.publicInput witness.data
      counterChannel.channel.toRaw) :
    ∀ i ∈ witness.interactionsWith counterChannel.channel.toRaw, i.Guarantees witness.data := by
  set channel := counterChannel.channel
  set interactions := witness.interactionsWith channel.toRaw
  have kernel := balance.balancedInteractions_of_isBalanced _ balanced
  have h_channel (i) (h_i : i ∈ interactions) : i.channel = channel.toRaw :=
    witness.channel_eq_of_mem_interactionsWith h_i
  -- an interaction is from a row of an owner, or satisfies its requirements
  have h_source (b) (h_b : b ∈ interactions) : b.Requirements witness.data ∨
      ∃ table ∈ witness.tables, table.component ∈ counterChannel.owners ∧ ∃ row ∈ table.table,
        b ∈ table.component.operations.interactionValuesWith channel.toRaw
          (table.environment row) := by
    rcases witness.mem_interactionsWith.mp h_b with h_verifier | ⟨table, h_table, h_row⟩
    · rw [witness.verifierChannelRequirements_iff_forall] at verifier_requirements
      exact .inl (verifier_requirements b h_verifier)
    by_cases h_owner : table.component ∈ counterChannel.owners
    · obtain ⟨row, h_row, h_b⟩ := List.mem_flatMap.mp h_row
      exact .inr ⟨table, h_table, h_owner, row, h_row, h_b⟩
    · have reqs := requirements table h_table h_owner
      rw [Table.channelRequirements_iff_forall, witness.same_data table h_table] at reqs
      exact .inl (reqs b h_row)
  let Bad (message : Array F) : Prop :=
    ∃ a ∈ interactions, a.IsUnitPull ∧ a.msg = message ∧ ¬a.Guarantees witness.data
  have not_bad := CounterChannel.not_bad counterChannel.orderOf_generator
    (fun message => counterChannel.counter (decode message)) (·.msg) interactions
    (Balance.LengthLtSize.length_lt_size _ balanced) Bad (by
      rintro message ⟨a, a_mem, a_pull, rfl, a_bad⟩
      obtain ⟨b, b_mem, b_msg, b_provides⟩ := kernel.exists_provides_of_isUnitPull a a_mem a_pull
      have a_of_b (b_reqs : b.Requirements witness.data) : a.Guarantees witness.data :=
        RawChannel.Normal.guarantees_of_requirements a b witness.data (h_channel a a_mem)
          (h_channel b b_mem) b_msg.symm a_pull b_provides b_reqs
      rcases h_source b b_mem with b_reqs | ⟨table, h_table, h_owner, row, h_row, h_b⟩
      · exact absurd (a_of_b b_reqs) a_bad
      obtain ⟨enabled, pull, push, h_interactions, h_bool, h_step⟩ :=
        counterChannel.exists_step_of_constraintsHold _ h_owner _ (constraints table h_table row h_row)
      have h_data : (table.environment row).data = witness.data := witness.same_data table h_table
      have h_mem (i) (h_i : i ∈ table.component.operations.interactionValuesWith channel.toRaw
          (table.environment row)) : i ∈ interactions :=
        witness.mem_interactionsWith.mpr (.inr ⟨table, h_table, List.mem_flatMap.mpr ⟨row, h_row, h_i⟩⟩)
      rw [h_interactions] at h_b
      rcases List.mem_pair.mp h_b with rfl | rfl
      · rcases h_bool with h | h <;>
          simp [Interaction.Provides, Channel.pulledIfValue, h] at b_provides
      have h_one : enabled = 1 := h_bool.resolve_left b_provides.1
      obtain ⟨h_ne, h_counter, h_grt⟩ := h_step h_one
      rw [h_data] at h_grt
      have pull_bad : ¬channel.Guarantees pull witness.data := fun h =>
        a_bad (a_of_b ((Channel.pushedIfValue_requirements_iff b_provides.1).mpr (h_grt h)))
      refine ⟨⟨a, a_mem, a_pull.1, rfl⟩, ⟨_, b_mem, rfl, b_msg⟩, (toElements pull).toArray,
        ⟨channel.pulledIfValue 1 pull, ?_, ⟨rfl, rfl⟩, rfl,
          fun h => pull_bad (Channel.pulledIfValue_one_guarantees_iff.mp h)⟩, ?_, ?_⟩
      · apply h_mem
        rw [h_interactions, ← h_one]
        exact List.mem_cons_self ..
      · rwa [decode_toArray]
      · rw [← b_msg]
        simp only [Channel.pushedIfValue, decode_toArray, h_counter])
  intro i h_i
  by_cases h_pull : i.IsUnitPull
  · by_contra h_bad
    exact not_bad i.msg ⟨i, h_i, h_pull, rfl, h_bad⟩
  · exact RawChannel.Normal.guarantees_of_not_isUnitPull i _ (h_channel i h_i) h_pull

/-- The counter channel, closed by `guarantees_of_isBalanced`. -/
def closedChannel (balance : Balance F) [balance.LengthLtSize] : ClosedChannel F balance where
  channel := counterChannel.channel.toRaw
  owners := counterChannel.owners
  guarantees_of_isBalanced := guarantees_of_isBalanced

@[circuit_norm] lemma closedChannel_channel (balance : Balance F) [balance.LengthLtSize] :
    (counterChannel.closedChannel balance).channel = counterChannel.channel.toRaw := rfl
@[circuit_norm] lemma closedChannel_owners (balance : Balance F) [balance.LengthLtSize] :
    (counterChannel.closedChannel balance).owners = counterChannel.owners := rfl

end CounterChannel
end Air.Flat
