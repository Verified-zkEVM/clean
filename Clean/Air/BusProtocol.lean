module

public import Clean.Air.BalanceModel
public import Clean.Circuit.Json

/-!
# The bus export protocol, version 1

The per-channel information a backend needs to enforce the balance relation assumed by the
soundness proofs of `Clean.Air.OrderedChannelWith` and `Clean.Air.VmWith`. The exported
interactions do not identify it: a directed interaction serializes as a legacy interaction with
one more message element, and over a binary field the two relations disagree (two provides of
one payload sum to zero under LogUp but are rejected by the multiset relation).

The protocol records the interpretation beside the interaction bytes: a
`ChannelSchema` per channel (name, raw arity and `ChannelLayout`, from `Channel.schema` or
`DirectedChannel.schema`) and a `BusProtocol` per ensemble (the layout of its balance model and
its channel schemas). The last section proves each clause of the directed layout as a fact about
the encoding; the gate and tag rules are local-contract obligations, so a backend enforcing them
rejects only traces that no sound row produces.
-/

@[expose] public section

open Lean

/-- How a channel's raw messages are laid out and which relation the verifier enforces on
them. -/
inductive ChannelLayout where
  /-- A legacy `Channel`: message = payload, signed multiplicity, field-sum relation with the
  no-wrap guard (`BalanceModel.logUp`). -/
  | signed
  /-- A `DirectedChannel`: message = payload followed by the direction tag at the last index,
  `0`/`1` gate, natural-number multiset relation on tag-stripped payloads
  (`BalanceModel.multiset`), tags outside `{0, 1}` rejected. -/
  | directed
  deriving DecidableEq, Repr

namespace ChannelLayout
/-- The name of the relation the backend enforces, as exported. -/
def relationName : ChannelLayout → String
  | .signed => "logup"
  | .directed => "multiset"
end ChannelLayout

/-- The exported description of one channel. -/
structure ChannelSchema where
  name : String
  /-- The raw arity, as the interactions carry it: the payload arity plus one for a directed
  channel. -/
  arity : ℕ
  layout : ChannelLayout
  deriving DecidableEq, Repr

namespace ChannelSchema
def toJson (s : ChannelSchema) : Json :=
  match s.layout with
  | .signed => Json.mkObj [
      ("channel", s.name),
      ("arity", s.arity),
      ("relation", ChannelLayout.signed.relationName),
      ("multiplicity", "signed") ]
  | .directed => Json.mkObj [
      ("channel", s.name),
      ("arity", s.arity),
      ("relation", ChannelLayout.directed.relationName),
      ("payload_arity", Lean.toJson (s.arity - 1)),
      ("tag_index", Lean.toJson (s.arity - 1)),
      ("tags", Json.mkObj [("provide", (0 : ℕ)), ("receive", (1 : ℕ))]),
      ("multiplicity", "gate"),
      ("malformed_tag", "reject") ]

instance : ToJson ChannelSchema := ⟨ChannelSchema.toJson⟩
end ChannelSchema

/-- The exported bus protocol of one ensemble: the version, the layout of the model the
ensemble is balanced under, and its channels. -/
structure BusProtocol where
  layout : ChannelLayout
  channels : List ChannelSchema
  deriving DecidableEq, Repr

namespace BusProtocol
/-- The protocol version this module specifies. -/
def version : ℕ := 1

/-- Every channel has the layout the ensemble's model reads. -/
def WellFormed (p : BusProtocol) : Prop := ∀ c ∈ p.channels, c.layout = p.layout

instance (p : BusProtocol) : Decidable p.WellFormed :=
  inferInstanceAs (Decidable (∀ c ∈ p.channels, c.layout = p.layout))

instance : ToJson BusProtocol where
  toJson p := Json.mkObj [
    ("protocol", "clean-bus"),
    ("version", version),
    ("balance", p.layout.relationName),
    ("channels", Lean.toJson p.channels) ]
end BusProtocol

variable {F : Type} [FiniteField F] [DecidableEq F]
variable {Message : TypeMap} [ProvableType Message]

/-- The schema of a legacy typed channel. -/
def Channel.schema (channel : Channel F Message) : ChannelSchema :=
  ⟨ channel.name, size Message, .signed ⟩

/-- The schema of a directed channel: one more raw element than the payload, for the tag. -/
def DirectedChannel.schema (channel : DirectedChannel F Message) : ChannelSchema :=
  ⟨ channel.name, size Message + 1, .directed ⟩

omit [DecidableEq F] in
@[circuit_norm] lemma Channel.schema_arity (channel : Channel F Message) :
    channel.schema.arity = channel.toRaw.arity := rfl
omit [FiniteField F] [DecidableEq F] in
@[circuit_norm] lemma Channel.schema_layout (channel : Channel F Message) :
    channel.schema.layout = .signed := rfl
omit [DecidableEq F] in
@[circuit_norm] lemma DirectedChannel.schema_arity (channel : DirectedChannel F Message) :
    channel.schema.arity = channel.toRaw.arity := rfl
omit [FiniteField F] [DecidableEq F] in
@[circuit_norm] lemma DirectedChannel.schema_layout (channel : DirectedChannel F Message) :
    channel.schema.layout = .directed := rfl

/-- The layout a balance model exports. Declared for the two models only, like
`BalanceModel.Reads`. -/
class BalanceModel.Protocol (model : BalanceModel F) where
  layout : ChannelLayout

instance : (BalanceModel.logUp F).Protocol := ⟨.signed⟩
instance : (BalanceModel.multiset F).Protocol := ⟨.directed⟩

/-- The protocol object of an ensemble under a model, with the schemas of its channels. -/
def BusProtocol.ofModel (model : BalanceModel F) [model.Protocol] (channels : List ChannelSchema) :
    BusProtocol :=
  ⟨ BalanceModel.Protocol.layout model, channels ⟩

/-- A model and the channel kind it reads export the same layout: legacy channels under LogUp
... -/
theorem Channel.schema_layout_logUp (channel : Channel F Message) :
    channel.schema.layout = BalanceModel.Protocol.layout (BalanceModel.logUp F) := rfl

/-- ... and directed channels under the multiset model. -/
theorem DirectedChannel.schema_layout_multiset (channel : DirectedChannel F Message) :
    channel.schema.layout = BalanceModel.Protocol.layout (BalanceModel.multiset F) := rfl

/-! ## The clauses of the directed layout, as facts about the encoding -/

/-- Tag position: the directed reading looks at the last raw element, index `arity - 1`. -/
theorem Interaction.directedEvent_direction_eq_provide_iff_tagIndex (i : Interaction F) :
    i.directedEvent.direction = .provide ↔
      i.msg[i.channel.arity - 1]? = some Direction.provide.tag := by
  rw [Interaction.directedEvent_direction_eq_provide, ← i.same_size]
  rfl

/-- Tag removal: the payload the relation compares has `arity - 1` elements. -/
theorem Interaction.directedEvent_payload_size (i : Interaction F) :
    i.directedEvent.payload.size = i.channel.arity - 1 := by
  rw [Interaction.directedEvent_payload, Array.size_pop, i.same_size]

omit [DecidableEq F] in
/-- Gate handling: a sound row's gate is `0` or `1`. -/
theorem DirectedChannel.gate_of_requirements (channel : DirectedChannel F Message) (mult : F)
    (msg : Vector F channel.toRaw.arity) (data : ProverData F) :
    channel.toRaw.Requirements mult msg data → mult = 0 ∨ mult = 1 :=
  fun h => h.1

omit [DecidableEq F] in
/-- Malformed tags: a sound row's tag is the provide tag or the receive tag. -/
theorem DirectedChannel.tag_of_requirements (channel : DirectedChannel F Message) (mult : F)
    (msg : Vector F channel.toRaw.arity) (data : ProverData F) :
    channel.toRaw.Requirements mult msg data →
      msg.toArray.back? = some Direction.provide.tag ∨
        msg.toArray.back? = some Direction.receive.tag :=
  fun h => h.2.1
