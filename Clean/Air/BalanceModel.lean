module

public import Clean.Air.FlatEnsemble

/-!
# Balance models

A `BalanceModel` packages the relation a proof-system verifier establishes on one channel's
interactions, its side conditions, a reading of interactions as events (`view`), and the
derivations of `PullsSupported` and `CountBalanced` (`Clean.Air.Balance`) from it.
`BalanceModel.logUp` is `BalancedInteractions` under the sign reading; `BalanceModel.multiset`
is a permutation of active provided and received payloads under the directed reading
`Interaction.directedEvent`, with no characteristic bound.

The structure does not relate `view` to the channel contract, so a model only fits the
encoding it reads: the multiset model on a legacy channel accepts messages that never matched,
and the LogUp model on a directed channel is met only by traces with no active interaction.
`RawChannel.ConsistentWith` is the per-channel soundness obligation under a model,
`BalanceModel.Reads` ties each model to its typed channel constructor, and the model-aware
ensemble statements (`Ensemble.StatementWith` and friends) take the model explicitly, with no
default.
-/

@[expose] public section

variable {F : Type} [FiniteField F] [DecidableEq F]
variable {Message : TypeMap} [ProvableType Message]

/--
A balance model: the per-channel relation a verifier establishes, the side conditions the
soundness argument needs, the reading of interactions as events, and the derivations of
`PullsSupported` and `CountBalanced`. `SideCondition` is kept apart from `Verified` so that a
capacity bound established by the verifier can discharge it.
-/
structure BalanceModel (F : Type) [FiniteField F] [DecidableEq F] where
  /-- The per-channel relation the proof-system verifier establishes. -/
  Verified : List (Interaction F) → Prop
  /-- Side conditions the soundness argument needs in addition to `Verified`. -/
  SideCondition : List (Interaction F) → Prop
  /-- How this model reads an interaction as a bus event. The structure does not tie this
  reading to the channel contract; `RawChannel.ConsistentWith` does. -/
  view : Interaction F → Event F
  /-- The multiplicity discipline under which one interaction is one event. -/
  UnitEvent : Interaction F → Prop
  verified_of_perm : ∀ {l l' : List (Interaction F)}, Verified l → l.Perm l' → Verified l'
  sideCondition_of_perm : ∀ {l l' : List (Interaction F)},
    SideCondition l → l.Perm l' → SideCondition l'
  /-- Lookup kernel: every active receive is supported by an active provide. -/
  pullsSupported : ∀ l : List (Interaction F), Verified l → SideCondition l →
    PullsSupported view l
  /-- VM kernel: with unit events, active provides and receives occur equally often. -/
  countBalanced : ∀ l : List (Interaction F), Verified l → SideCondition l →
    (∀ i ∈ l, UnitEvent i) → CountBalanced view l

namespace BalanceModel
/-- What an ensemble statement requires of one channel's interactions under a model. -/
def Balanced (model : BalanceModel F) (l : List (Interaction F)) : Prop :=
  model.SideCondition l ∧ model.Verified l

theorem balanced_of_perm (model : BalanceModel F) {l l' : List (Interaction F)} :
    model.Balanced l → l.Perm l' → model.Balanced l' :=
  fun ⟨side, verified⟩ perm =>
    ⟨model.sideCondition_of_perm side perm, model.verified_of_perm verified perm⟩

theorem pullsSupported_of_balanced (model : BalanceModel F) {l : List (Interaction F)} :
    model.Balanced l → PullsSupported model.view l :=
  fun ⟨side, verified⟩ => model.pullsSupported l verified side

theorem countBalanced_of_balanced (model : BalanceModel F) {l : List (Interaction F)} :
    model.Balanced l → (∀ i ∈ l, model.UnitEvent i) → CountBalanced model.view l :=
  fun ⟨side, verified⟩ unit => model.countBalanced l verified side unit

/-- The LogUp model: field-sum balance with the no-wrap guard, under the legacy sign reading. -/
def logUp (F : Type) [FiniteField F] [DecidableEq F] : BalanceModel F where
  Verified l := ∀ msg : Array F, balanceOf l msg = 0
  SideCondition l := l.length < ringChar F ∨ ringChar F = 0
  view := Interaction.legacyEvent
  UnitEvent i := i.mult = 0 ∨ i.mult = 1 ∨ i.mult = -1
  verified_of_perm := by
    intro l l' verified perm msg
    rw [← balanceOf_perm perm]
    exact verified msg
  sideCondition_of_perm := by
    intro l l' side perm
    rwa [← perm.length_eq]
  pullsSupported l verified side :=
    pullsSupported_legacyEvent_of_balancedInteractions ⟨side, verified⟩
  countBalanced l verified side unit :=
    countBalanced_legacyEvent_of_balancedInteractions ⟨side, verified⟩ unit

/-- The LogUp model's balance predicate is `BalancedInteractions`, by definition. -/
theorem logUp_balanced_iff (l : List (Interaction F)) :
    (logUp F).Balanced l ↔ BalancedInteractions l := Iff.rfl
end BalanceModel

/-
## The directed reading

A `DirectedChannel` interaction stores its direction as the last message element; see
`Clean.Circuit.DirectedChannel`. The directed reading recovers payload and direction from
there. An interaction whose last element is not the provide tag is read as a receive, so
that a malformed tag can never play the role of a provider.
-/

/-- The directed reading of an interaction as a bus event. -/
def Interaction.directedEvent (i : Interaction F) : Event F where
  payload := i.msg.pop
  direction := if i.msg.back? = some Direction.provide.tag then .provide else .receive
  active := i.mult ≠ 0

namespace Interaction
@[circuit_norm] lemma directedEvent_payload (i : Interaction F) :
  i.directedEvent.payload = i.msg.pop := rfl
@[circuit_norm] lemma directedEvent_active (i : Interaction F) :
  i.directedEvent.active = decide (i.mult ≠ 0) := rfl
private lemma directedEvent_direction (i : Interaction F) :
    i.directedEvent.direction =
      if i.msg.back? = some Direction.provide.tag then .provide else .receive := rfl
@[circuit_norm] lemma directedEvent_direction_eq_provide (i : Interaction F) :
    i.directedEvent.direction = .provide ↔ i.msg.back? = some Direction.provide.tag := by
  simp only [directedEvent_direction]; split_ifs <;> simp_all
@[circuit_norm] lemma directedEvent_direction_eq_receive (i : Interaction F) :
    i.directedEvent.direction = .receive ↔ i.msg.back? ≠ some Direction.provide.tag := by
  simp only [directedEvent_direction]; split_ifs <;> simp_all
end Interaction

namespace DirectedChannel
variable {channel : DirectedChannel F Message}

/-- The directed reading of an evaluated directed interaction is the event it was built from. -/
@[circuit_norm]
lemma directedEvent_emittedValue (direction : Direction) (enabled : F) (msg : Message F)
    (assumeGuarantees : Bool) :
    (channel.emittedValue direction enabled msg assumeGuarantees).directedEvent =
      { payload := (toElements msg).toArray, direction, active := enabled ≠ 0 } := by
  cases direction
  all_goals
    simp [Interaction.directedEvent, emittedValue, Vector.toArray_push, Array.back?_push,
      Array.pop_push, Direction.tag]
    by_cases h : enabled = 0 <;> simp [h]

/--
Lookup-style consistency of a directed channel: if every active receive is supported by an
active provide of the same payload, the requirements of all interactions imply their
guarantees. The directed counterpart of `RawChannel.consistent_of_normal`.
-/
theorem guarantees_of_requirements_of_pullsSupported (channel : DirectedChannel F Message)
    (interactions : List (Interaction F)) (data : ProverData F) :
    PullsSupported Interaction.directedEvent interactions →
    (∀ i ∈ interactions, i.channel = channel.toRaw ∧ i.Requirements data) →
    ∀ i ∈ interactions, i.Guarantees data := by
  intro support reqs a a_mem
  -- state the guarantee of `a` on `channel.toRaw`: it is conditional on the receive tag and
  -- an active gate
  rw [Interaction.guarantees_iff_of_channel_eq (reqs a a_mem).left]
  intro _ (a_tag : a.msg.back? = some Direction.receive.tag) (a_active : a.mult ≠ 0)
  -- `a` is an active receive in the directed reading, so it has an active provider `b`
  have a_receive : a.directedEvent.direction = .receive := by
    simp [Interaction.directedEvent_direction_eq_receive, a_tag, Direction.tag]
  have a_active' : a.directedEvent.active = true := by
    simp [Interaction.directedEvent_active, a_active]
  obtain ⟨b, b_mem, b_provide, b_active, b_payload⟩ := support a a_mem a_receive a_active'
  simp only [Interaction.directedEvent_direction_eq_provide, Interaction.directedEvent_active,
    Interaction.directedEvent_payload, decide_eq_true_eq] at b_provide b_active b_payload
  -- the requirement of `b`, stated on `channel.toRaw`, is: boolean gate, well-formed tag, and
  -- the guarantee on its payload if it is an active provider
  obtain ⟨b_channel, b_reqs⟩ := reqs b b_mem
  rw [Interaction.requirements_iff_of_channel_eq b_channel] at b_reqs
  obtain ⟨-, -, b_grt⟩ := b_reqs
  -- and the two payloads agree
  convert b_grt b_provide b_active using 2
  apply Vector.toArray_inj.mp
  simp only [Vector.toArray_pop]
  exact b_payload.symm
end DirectedChannel

/--
The multiset model: active provided and received payloads are a permutation of each other, in
the directed reading, with no side condition and no characteristic bound. `UnitEvent` (a gate
of `0` or `1`) does not affect the relation, which reads any nonzero gate as one active event;
the boolean gate is enforced by the directed channel's local contract.
-/
def BalanceModel.multiset (F : Type) [FiniteField F] [DecidableEq F] : BalanceModel F where
  Verified l := (activePayloads Interaction.directedEvent l .provide).Perm
    (activePayloads Interaction.directedEvent l .receive)
  SideCondition _ := True
  view := Interaction.directedEvent
  UnitEvent i := i.mult = 0 ∨ i.mult = 1
  verified_of_perm := by
    intro l l' verified perm
    unfold activePayloads at *
    exact ((perm.filter _).map _).symm.trans (verified.trans ((perm.filter _).map _))
  sideCondition_of_perm _ _ := trivial
  pullsSupported l verified _ :=
    pullsSupported_of_countBalanced (countBalanced_of_perm_activePayloads verified)
  countBalanced l verified _ _ := countBalanced_of_perm_activePayloads verified

theorem BalanceModel.multiset_balanced_iff (l : List (Interaction F)) :
    (multiset F).Balanced l ↔
      (activePayloads Interaction.directedEvent l .provide).Perm
        (activePayloads Interaction.directedEvent l .receive) := by
  simp [Balanced, multiset]

@[circuit_norm] lemma BalanceModel.multiset_unitEvent_iff (i : Interaction F) :
    (multiset F).UnitEvent i ↔ i.mult = 0 ∨ i.mult = 1 := Iff.rfl

/-
## The VM argument on a directed channel
-/

namespace DirectedChannel
/--
The VM argument for a directed channel, over any field: the counterpart of
`guarantees_of_requirements_of_requirements_of_guarantees`. Given receives `pulls` and provides
`pushes` paired by index, count balance on their concatenation and the row implications
`G pulls[i] → R pushes[i]`, every row also satisfies the converse.

`pulls_receive` is necessary (`pull_role_necessary` in `Clean/Air/Test/BusBalance.lean`).
`pushes_provide` is needed by `count_eq_of_countBalanced`, though the conclusion also holds
without it.
-/
theorem guarantees_of_requirements_of_requirements_of_guarantees
    (channel : DirectedChannel F Message) (pulls pushes : List (Interaction F))
    (balance : CountBalanced Interaction.directedEvent (pulls ++ pushes)) (data : ProverData F)
    (n : ℕ) (len_pulls : pulls.length = n) (len_pushes : pushes.length = n)
    (pulls_channel : ∀ a ∈ pulls, a.channel = channel.toRaw)
    (pushes_channel : ∀ b ∈ pushes, b.channel = channel.toRaw)
    (pulls_receive : ∀ a ∈ pulls, a.directedEvent.direction = .receive)
    (pushes_provide : ∀ b ∈ pushes, b.directedEvent.direction = .provide) :
    (∀ (i : ℕ) (hi : i < n), pulls[i].Guarantees data → pushes[i].Requirements data) →
    ∀ (i : ℕ) (hi : i < n), pushes[i].Requirements data → pulls[i].Guarantees data := by
  refine guarantees_of_requirements_of_count_eq (fun i => i.directedEvent.key)
    (·.Guarantees data) (·.Requirements data) pulls pushes n len_pulls len_pushes
    (count_eq_of_countBalanced balance (len_pulls.trans len_pushes.symm) pulls_receive
      pushes_provide) ?_
  intro a a_mem b b_mem key_eq b_req
  -- the guarantee of `a` on `channel.toRaw` is conditional on the receive tag and an active gate
  rw [Interaction.guarantees_iff_of_channel_eq (pulls_channel a a_mem)]
  intro _ _ (a_active : a.mult ≠ 0)
  -- `a` is active, so its key is its payload, and `b` is an active event with the same payload
  have a_key : a.directedEvent.key = some a.msg.pop := by
    simp [Event.key_eq_some_iff, Interaction.directedEvent_active,
      Interaction.directedEvent_payload, a_active]
  rw [a_key, Event.key_eq_some_iff, Interaction.directedEvent_active,
    Interaction.directedEvent_payload, decide_eq_true_eq] at key_eq
  obtain ⟨b_active, b_payload⟩ := key_eq
  -- `b` is a provide, so its requirement establishes the guarantee on its payload
  have b_provide := pushes_provide b b_mem
  rw [Interaction.directedEvent_direction_eq_provide] at b_provide
  rw [Interaction.requirements_iff_of_channel_eq (pushes_channel b b_mem)] at b_req
  obtain ⟨-, -, b_grt⟩ := b_req
  -- and the two payloads agree
  convert b_grt b_provide b_active using 2
  apply Vector.toArray_inj.mp
  simp only [Vector.toArray_pop]
  exact b_payload.symm
end DirectedChannel

/-
## Consistency of a channel under a model
-/

/--
A raw channel is consistent under a balance model if balance under the model and the
requirements of all interactions on the channel imply their guarantees. This is
`RawChannel.Consistent` with the model as a parameter.
-/
class RawChannel.ConsistentWith (channel : RawChannel F) (model : BalanceModel F) : Prop where
  consistent : ∀ (interactions : List (Interaction F)) (data : ProverData F),
    model.Balanced interactions →
    (∀ i ∈ interactions, i.channel = channel ∧ i.Requirements data) →
    (∀ i ∈ interactions, i.Guarantees data)

/-- The legacy `Consistent` is consistency under the LogUp model, by definition. -/
theorem RawChannel.consistent_iff_consistentWith_logUp (channel : RawChannel F) :
    channel.Consistent ↔ channel.ConsistentWith (.logUp F) :=
  ⟨fun h => ⟨h.consistent⟩, fun h => ⟨h.consistent⟩⟩

/-- Legacy-consistent channels, in particular all typed `Channel`s, under the LogUp model. -/
instance (channel : RawChannel F) [channel.Consistent] : channel.ConsistentWith (.logUp F) :=
  (RawChannel.consistent_iff_consistentWith_logUp channel).mp inferInstance

/-- Directed channels under the multiset model, over any field. -/
instance (channel : DirectedChannel F Message) : channel.toRaw.ConsistentWith (.multiset F) where
  consistent interactions data balanced reqs :=
    channel.guarantees_of_requirements_of_pullsSupported interactions data
      ((BalanceModel.multiset F).pullsSupported_of_balanced balanced) reqs

/-
## The channel kind a model reads
-/

/--
The typed channel constructor whose erasure a balance model reads, with the erasure and the
consistency law for it. A builder taking channels through this class rejects a channel of the
wrong kind as a type error; `RawChannel.ConsistentWith` alone does not, since it holds
vacuously for the LogUp model on every directed channel.
-/
class BalanceModel.Reads (model : BalanceModel F)
    (Ch : (Message : TypeMap) → [ProvableType Message] → Type) where
  /-- Erasure of a typed channel of this kind to the raw channel the model reads. -/
  toRaw {Message : TypeMap} [ProvableType Message] : Ch Message → RawChannel F
  /-- Every channel of this kind is consistent under the model. -/
  consistentWith {Message : TypeMap} [ProvableType Message] (channel : Ch Message) :
    (toRaw channel).ConsistentWith model

/-- The LogUp model reads legacy typed channels. -/
instance : (BalanceModel.logUp F).Reads (Channel F) where
  toRaw channel := channel.toRaw
  consistentWith _ := inferInstance

/-- The multiset model reads directed channels, over any field. -/
instance : (BalanceModel.multiset F).Reads (DirectedChannel F) where
  toRaw channel := channel.toRaw
  consistentWith _ := inferInstance

@[circuit_norm]
lemma BalanceModel.logUp_reads_toRaw (channel : Channel F Message) :
    BalanceModel.Reads.toRaw (model := .logUp F) channel = channel.toRaw := rfl

@[circuit_norm]
lemma BalanceModel.multiset_reads_toRaw (channel : DirectedChannel F Message) :
    BalanceModel.Reads.toRaw (model := .multiset F) channel = channel.toRaw := rfl

/-
## Model-aware ensemble statements

These are the explicitly model-selected counterparts of `EnsembleWitness.BalancedChannels`,
`Ensemble.Statement`, `Ensemble.Soundness`, `Ensemble.Completeness` and `FormalEnsemble`.
The legacy definitions are their `BalanceModel.logUp` instances, definitionally.
-/

namespace Air.Flat
variable {PublicIO : TypeMap} [ProvableType PublicIO]

/-- All ensemble interactions with all ensemble channels are balanced under `model`. -/
@[circuit_norm]
def EnsembleWitness.BalancedChannelsWith {ens : Ensemble F PublicIO} (model : BalanceModel F)
    (witness : EnsembleWitness ens) : Prop :=
  ∀ channel ∈ ens.channels, model.Balanced (witness.allTablesWitness.interactionsWith channel)

theorem EnsembleWitness.balancedChannels_iff_balancedChannelsWith_logUp {ens : Ensemble F PublicIO}
    (witness : EnsembleWitness ens) :
    witness.BalancedChannels ↔ witness.BalancedChannelsWith (.logUp F) := Iff.rfl

namespace Ensemble
/-- The raw statement of an ensemble under an explicit balance model. -/
def StatementWith (model : BalanceModel F) (ens : Ensemble F PublicIO)
    (publicInput : PublicIO F) : Prop :=
  ∃ witness : EnsembleWitness ens,
    witness.publicInput = publicInput ∧
    witness.Constraints ∧
    witness.BalancedChannelsWith model

/-- Soundness under an explicit balance model. -/
def SoundnessWith (model : BalanceModel F) (ens : Ensemble F PublicIO)
    (Assumptions Spec : PublicIO F → Prop) : Prop :=
  ∀ publicInput, Assumptions publicInput → ens.StatementWith model publicInput → Spec publicInput

/-- Completeness under an explicit balance model. -/
def CompletenessWith (model : BalanceModel F) (ens : Ensemble F PublicIO)
    (Assumptions Spec : PublicIO F → Prop) : Prop :=
  ∀ publicInput, Assumptions publicInput → Spec publicInput → ens.StatementWith model publicInput

/-- The legacy statement is the LogUp instance of the model-aware statement. -/
theorem statement_iff_statementWith_logUp (ens : Ensemble F PublicIO) (publicInput : PublicIO F) :
    ens.Statement publicInput ↔ ens.StatementWith (.logUp F) publicInput := Iff.rfl

theorem soundness_iff_soundnessWith_logUp (ens : Ensemble F PublicIO)
    (Assumptions Spec : PublicIO F → Prop) :
    ens.Soundness Assumptions Spec ↔ ens.SoundnessWith (.logUp F) Assumptions Spec := Iff.rfl

theorem completeness_iff_completenessWith_logUp (ens : Ensemble F PublicIO)
    (Assumptions Spec : PublicIO F → Prop) :
    ens.Completeness Assumptions Spec ↔ ens.CompletenessWith (.logUp F) Assumptions Spec := Iff.rfl
end Ensemble

/--
A formal ensemble whose soundness proof is bound to an explicit balance model. `consistent` is
found by instance search for a correct model/channel pairing. It also holds, vacuously, for the
LogUp model on directed channels, so a bundle built by hand rather than through
`SoundEnsembleWith` should come with a satisfiability witness for its statement.
-/
structure FormalEnsembleWith (F : Type) [FiniteField F] [DecidableEq F] (model : BalanceModel F)
    (PublicIO : TypeMap) [ProvableType PublicIO] where
  ensemble : Ensemble F PublicIO
  Assumptions : PublicIO F → Prop := fun _ => True
  Spec : PublicIO F → Prop
  consistent : ∀ channel ∈ ensemble.channels, channel.ConsistentWith model
  soundness : ensemble.SoundnessWith model Assumptions Spec

/-- A legacy formal ensemble with consistent channels is a formal ensemble under the LogUp
model. -/
def FormalEnsemble.withLogUp (ens : FormalEnsemble F PublicIO)
    (consistent : ∀ channel ∈ ens.ensemble.channels, channel.Consistent) :
    FormalEnsembleWith F (.logUp F) PublicIO where
  ensemble := ens.ensemble
  Assumptions := ens.Assumptions
  Spec := ens.Spec
  consistent channel h :=
    (RawChannel.consistent_iff_consistentWith_logUp channel).mp (consistent channel h)
  soundness := ens.soundness
end Air.Flat
