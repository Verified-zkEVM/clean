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
already rejects malformed tags (`DirectedChannel.toRaw`); the directed reading, its recovery
lemma and its transport theorem are the next layer of the bus-balance roadmap and are not
part of this file.

The model-aware ensemble entry points (`Ensemble.StatementWith` and friends) take the model
explicitly. There is deliberately no default model instance: a user of a characteristic-2
field has to name the model, and cannot pick LogUp by omission.
-/

variable {F : Type} [FiniteField F] [DecidableEq F]

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
end BalanceModel

/-
## Model-aware ensemble statements

These are the explicitly model-selected counterparts of `EnsembleWitness.BalancedChannels`,
`Ensemble.Statement`, `Ensemble.Soundness`, `Ensemble.Completeness` and `FormalEnsemble`.
-/

namespace Air.Flat
variable {PublicIO : TypeMap} [ProvableType PublicIO]

/-- All ensemble interactions with all ensemble channels are balanced under `model`. -/
def EnsembleWitness.BalancedChannelsWith {ens : Ensemble F PublicIO} (model : BalanceModel F)
    (witness : EnsembleWitness ens) : Prop :=
  ∀ channel ∈ ens.channels, model.Balanced (witness.allTablesWitness.interactionsWith channel)

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
end Ensemble

/-- A formal ensemble whose soundness proof is bound to an explicit balance model. -/
structure FormalEnsembleWith (F : Type) [FiniteField F] [DecidableEq F] (model : BalanceModel F)
    (PublicIO : TypeMap) [ProvableType PublicIO] where
  ensemble : Ensemble F PublicIO
  Assumptions : PublicIO F → Prop := fun _ => True
  Spec : PublicIO F → Prop
  soundness : ensemble.SoundnessWith model Assumptions Spec
end Air.Flat
