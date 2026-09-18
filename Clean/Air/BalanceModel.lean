import Clean.Air.FlatEnsemble

/-!
# Balance models

A `BalanceModel` packages what a proof-system verifier establishes about the interactions
on one channel, the side conditions the soundness argument needs in addition, the reading
of interactions as bus events, and the two derivations that feed the shared kernel of
`Clean.Air.Balance` (`PullsSupported` and `CountBalanced`).

## An abstract count/support interface

The structure fixes only the shape of the argument. Its `view` is supplied by the model, and
its two kernel derivations are stated relative to that view; nothing in the structure relates
the view to the raw channel contract, `Interaction.Guarantees` and `Interaction.Requirements`.
A model that reads every interaction as an inactive event satisfies every field, and its
`Balanced` then accepts an active receive that no provider supports (see `blindModel` in
`Clean/Air/Test/BusBalance.lean`).

What makes a model usable in a channel soundness argument is a correspondence law for the
encoding it reads, proved separately from this structure: the view recovers the payload,
direction and activity of every evaluated interaction of the channel; the argument is applied
per raw channel, to `interactionsWith channel`; permission to assume the guarantee stays with
`assumeGuarantees`; and `PullsSupported view` transports the requirement of the supporting
provider to the guarantee of the receive. For the directed encoding, the local contract
rejects malformed tags (`DirectedChannel.toRaw`), `DirectedChannel.directedEvent_emittedValue`
is the recovery lemma and `DirectedChannel.guarantees_of_requirements_of_pullsSupported` is
the transport theorem, both below.

## A model only fits the encoding it reads

A model and a channel are chosen independently, and after erasure to `RawChannel` nothing
records which encoding a channel uses. The multiset model applied to a legacy channel strips
the last payload element as if it were a tag, and accepts interactions whose messages never
matched; the LogUp model applied to a directed channel is balanced only by inactive traces.
`RawChannel.ConsistentWith` is the obligation that rules this out: balance under the model
and the requirements of all interactions on the channel imply their guarantees. It is the
legacy `RawChannel.Consistent` with the model as a parameter, it has exactly two instances
(legacy-consistent channels under `logUp`, erased directed channels under `multiset`), and
`FormalEnsembleWith` demands it of every channel. For a mismatched pairing no instance exists,
and where the channel's guarantee says anything the obligation is false (see
`legacy_not_consistentWith_multiset` in `Clean/Air/Test/BusBalance.lean`).

## The two models

* `BalanceModel.logUp` is today's `BalancedInteractions`, split into its field-sum relation
  and its no-wrap guard, under the legacy sign reading of direction
  (`Interaction.legacyEvent`). Its `Balanced` predicate is `BalancedInteractions` by
  definition, so the legacy ensemble statement is the LogUp instance of the model-aware one.
* `BalanceModel.multiset` is the permutation of active provided and received payloads under
  the directed reading (`Interaction.directedEvent`) of `DirectedChannel` interactions. It
  has no side condition and no characteristic bound.

The model-aware ensemble entry points (`Ensemble.StatementWith` and friends) take the model
explicitly. There is deliberately no default model instance: a user of a characteristic-2
field has to name the model, and cannot pick LogUp by omission.
-/

variable {F : Type} [FiniteField F] [DecidableEq F]
variable {Message : TypeMap} [ProvableType Message]

/--
A balance model: the per-channel relation a verifier establishes, the side conditions the
soundness argument needs, the reading of interactions as events, and the derivations of the
kernel facts.

The split between `Verified` and `SideCondition` is what leaves room for a capacity premise
(Clean issue #452): an ensemble-wide bound computed by the verifier can be bridged to the
per-channel `SideCondition` of the LogUp model without touching the multiset model.
-/
structure BalanceModel (F : Type) [FiniteField F] [DecidableEq F] where
  /-- The per-channel relation the proof-system verifier establishes. -/
  Verified : List (Interaction F) → Prop
  /-- Side conditions the soundness argument needs in addition to `Verified`. -/
  SideCondition : List (Interaction F) → Prop
  /-- How this model reads an interaction as a bus event. The structure does not tie this
  reading to the raw channel contract; the model's correspondence law does. -/
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

/-- The LogUp model's balance predicate is today's `BalancedInteractions`, by definition. -/
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
  · simp [Interaction.directedEvent, emittedValue, Vector.toArray_push, Array.back?_push,
      Array.pop_push, Direction.tag]
    by_cases h : enabled = 0 <;> simp [h]
  · simp [Interaction.directedEvent, emittedValue, Vector.toArray_push, Array.back?_push,
      Array.pop_push, Direction.tag]
    by_cases h : enabled = 0 <;> simp [h]

/--
The lookup-style consistency of a directed channel: if every active receive is supported
by an active provide of the same payload (which any balance model derives from its
`Balanced` relation), then the requirements of all interactions imply their guarantees.
This is the directed counterpart of `RawChannel.consistent_of_normal`; it needs no
characteristic assumption.
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

/-- The multiset model: active provided and received payloads are a permutation of each
other, in the directed reading. No side condition and no characteristic bound. -/
def BalanceModel.multiset (F : Type) [FiniteField F] [DecidableEq F] : BalanceModel F where
  Verified l := (activePayloads Interaction.directedEvent l .provide).Perm
    (activePayloads Interaction.directedEvent l .receive)
  SideCondition _ := True
  view := Interaction.directedEvent
  UnitEvent _ := True
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

/-
## Consistency of a channel under a model
-/

/--
A raw channel is consistent under a balance model if, for any interactions on that channel,
balance under the model together with the requirements of all interactions implies the
guarantees of all interactions: what the receivers assumed is justified by what the providers
proved. This is the legacy `RawChannel.Consistent` with the model as a parameter.

It is the obligation that ties a model to the encoding it reads. It mentions no circuit: it
relates the channel's two predicates, the model's reading and the model's relation.
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
A formal ensemble whose soundness proof is bound to an explicit balance model.

`consistent` ties the model to the channels: the statement of an ensemble describes what the
verifier enforces only if the model reads every channel in the encoding that channel uses.
Instances exist for legacy channels under `logUp` and for directed channels under `multiset`,
so for a correct pairing the field is found by instance search (`fun _ _ => inferInstance`
after a case split on the channel list); for a mismatched pairing it cannot be supplied.
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
