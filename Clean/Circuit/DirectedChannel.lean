import Clean.Circuit.Explicit

/-!
# Directed channels

An opt-in channel construction for buses whose balance argument counts events instead of
summing signed field multiplicities. It exists because, over a field of characteristic 2,
a signed multiplicity cannot tell a provider from a receiver (`-1 = 1`), so the legacy
`Channel` contract of `Clean.Circuit.Channel` becomes meaningless there. Legacy channels are
untouched: `Channel`, `Channel.toRaw` and `emit/push/pull/pushIf/pullIf` keep their meaning.

## Tag representation

A `DirectedChannel F Message` erases to a `RawChannel` of arity `size Message + 1`. The raw
message of an interaction is `toElements msg` followed by one extra element, the
`Direction.tag`: `0` for a provider, `1` for a receiver. The multiplicity is the activation
gate and is required to be `0` or `1`; it never carries direction.

This representation survives every existing stage without changing a public record:
construction (`DirectedInteraction.toRaw`), subcircuit composition and collection (the
interaction is an ordinary `AbstractInteraction` inside `FlatOperation.interact`), evaluation
(`AbstractInteraction.eval` maps the tag together with the payload) and export (the tag is the
last element of the exported message; the export protocol is documented separately).

## Local contract

For a directed channel with guarantee `G`, evaluated at a row:

| operation | direction | may assume `G msg`? | must prove locally |
| --- | --- | --- | --- |
| `pushIf enabled msg` | provide | no | `enabled ∈ {0, 1}`, and `G msg` if `enabled ≠ 0` |
| `pullIf enabled msg` | receive | yes, if `enabled ≠ 0` | `enabled ∈ {0, 1}` |
| `emit .receive enabled msg` | receive | no | `enabled ∈ {0, 1}` |
| `emit .provide enabled msg` | provide | no | as `pushIf` |

`assumeGuarantees` keeps its legacy meaning of "permission to use the guarantee locally";
direction is stored independently, which is what lets a receiver decline the guarantee
(`emit .receive`) while still counting on the receiving side of the bus.
-/

variable {F : Type} [FiniteField F]
variable {Message : TypeMap} [ProvableType Message]

/-- The semantic direction of a bus event. -/
inductive Direction where
  | provide
  | receive
  deriving DecidableEq, Repr

namespace Direction
@[circuit_norm] lemma provide_ne_receive : provide ≠ receive := Direction.noConfusion
@[circuit_norm] lemma receive_ne_provide : receive ≠ provide := Direction.noConfusion

/-- Field encoding of a direction, stored as the last message element of a directed raw interaction. -/
def tag : Direction → F
  | provide => 0
  | receive => 1

@[circuit_norm] lemma tag_provide : (provide.tag : F) = 0 := rfl
@[circuit_norm] lemma tag_receive : (receive.tag : F) = 1 := rfl

@[circuit_norm]
lemma tag_eq_zero_iff {d : Direction} : (d.tag : F) = 0 ↔ d = .provide := by
  cases d <;> simp [tag]

@[circuit_norm]
lemma tag_eq_one_iff {d : Direction} : (d.tag : F) = 1 ↔ d = .receive := by
  cases d <;> simp [tag]

@[circuit_norm]
lemma tag_inj_iff {d d' : Direction} : (d.tag : F) = d'.tag ↔ d = d' := by
  cases d <;> cases d' <;> simp [tag]
end Direction

/-- A typed channel whose interactions carry an explicit direction. -/
structure DirectedChannel (F : Type) (Message : TypeMap) [ProvableType Message] where
  name : String
  /-- The guarantee an active provider establishes, and an active receiver may assume locally. -/
  Guarantees (message : Message F) (data : ProverData F) : Prop

namespace DirectedChannel
/--
Erase a `DirectedChannel` to a `RawChannel`. The raw message is the payload followed by the
direction tag. An active receiver is granted the guarantee; an active provider owes it;
every interaction owes a boolean gate.
-/
@[implicit_reducible]
def toRaw (channel : DirectedChannel F Message) : RawChannel F where
  name := channel.name
  arity := size Message + 1
  Guarantees mult message data :=
    message.toArray.back? = some Direction.receive.tag → mult ≠ 0 →
      channel.Guarantees (fromElements message.pop) data
  Requirements mult message data :=
    (mult = 0 ∨ mult = 1) ∧
    (message.toArray.back? = some Direction.provide.tag → mult ≠ 0 →
      channel.Guarantees (fromElements message.pop) data)

instance : CoeOut (DirectedChannel F Message) (RawChannel F) where
  coe := toRaw

@[circuit_norm]
lemma toRaw_name (channel : DirectedChannel F Message) : channel.toRaw.name = channel.name := rfl
@[circuit_norm]
lemma toRaw_arity (channel : DirectedChannel F Message) : channel.toRaw.arity = size Message + 1 := rfl
end DirectedChannel

/-- A typed interaction with a directed channel: a direction, an activation gate, a message,
and permission to assume the channel guarantee locally. -/
structure DirectedInteraction (channel : DirectedChannel F Message) where
  direction : Direction
  /-- The activation gate. It doubles as the raw multiplicity and must evaluate to `0` or `1`. -/
  enabled : Expression F
  msg : Message (Expression F)
  assumeGuarantees : Bool

namespace DirectedChannel
variable {channel : DirectedChannel F Message}

/-- An interaction in an explicit direction that does not assume the guarantee. -/
def emitted (channel : DirectedChannel F Message) (direction : Direction) (enabled : Expression F)
    (msg : Message (Expression F)) : DirectedInteraction channel :=
  { direction, enabled, msg, assumeGuarantees := false }

/-- An unconditional provider. -/
def pushed (channel : DirectedChannel F Message) (msg : Message (Expression F)) :
    DirectedInteraction channel :=
  { direction := .provide, enabled := 1, msg, assumeGuarantees := false }

/-- A provider gated by `enabled`. -/
def pushedIf (channel : DirectedChannel F Message) (enabled : Expression F)
    (msg : Message (Expression F)) : DirectedInteraction channel :=
  { direction := .provide, enabled, msg, assumeGuarantees := false }

/-- An unconditional receiver that assumes the guarantee. -/
def pulled (channel : DirectedChannel F Message) (msg : Message (Expression F)) :
    DirectedInteraction channel :=
  { direction := .receive, enabled := 1, msg, assumeGuarantees := true }

/-- A receiver gated by `enabled` that assumes the guarantee when active. -/
def pulledIf (channel : DirectedChannel F Message) (enabled : Expression F)
    (msg : Message (Expression F)) : DirectedInteraction channel :=
  { direction := .receive, enabled, msg, assumeGuarantees := true }

section
variable (direction : Direction) (enabled : Expression F) (msg : Message (Expression F))

omit [FiniteField F] in
@[circuit_norm] lemma emitted_direction : (channel.emitted direction enabled msg).direction = direction := rfl
omit [FiniteField F] in
@[circuit_norm] lemma emitted_enabled : (channel.emitted direction enabled msg).enabled = enabled := rfl
omit [FiniteField F] in
@[circuit_norm] lemma emitted_msg : (channel.emitted direction enabled msg).msg = msg := rfl
omit [FiniteField F] in
@[circuit_norm] lemma emitted_assumeGuarantees :
  (channel.emitted direction enabled msg).assumeGuarantees = false := rfl

omit [FiniteField F] in
@[circuit_norm] lemma pushedIf_direction : (channel.pushedIf enabled msg).direction = .provide := rfl
omit [FiniteField F] in
@[circuit_norm] lemma pushedIf_enabled : (channel.pushedIf enabled msg).enabled = enabled := rfl
omit [FiniteField F] in
@[circuit_norm] lemma pushedIf_msg : (channel.pushedIf enabled msg).msg = msg := rfl
omit [FiniteField F] in
@[circuit_norm] lemma pushedIf_assumeGuarantees : (channel.pushedIf enabled msg).assumeGuarantees = false := rfl

omit [FiniteField F] in
@[circuit_norm] lemma pulledIf_direction : (channel.pulledIf enabled msg).direction = .receive := rfl
omit [FiniteField F] in
@[circuit_norm] lemma pulledIf_enabled : (channel.pulledIf enabled msg).enabled = enabled := rfl
omit [FiniteField F] in
@[circuit_norm] lemma pulledIf_msg : (channel.pulledIf enabled msg).msg = msg := rfl
omit [FiniteField F] in
@[circuit_norm] lemma pulledIf_assumeGuarantees : (channel.pulledIf enabled msg).assumeGuarantees = true := rfl

omit [FiniteField F] in
/-- A provider that assumes nothing is just a provider. -/
@[circuit_norm] lemma emitted_provide_eq_pushedIf :
  channel.emitted .provide enabled msg = channel.pushedIf enabled msg := rfl

@[circuit_norm] lemma pushed_direction : (channel.pushed msg).direction = .provide := rfl
@[circuit_norm] lemma pushed_enabled : (channel.pushed msg).enabled = 1 := rfl
@[circuit_norm] lemma pushed_msg : (channel.pushed msg).msg = msg := rfl
@[circuit_norm] lemma pushed_assumeGuarantees : (channel.pushed msg).assumeGuarantees = false := rfl

@[circuit_norm] lemma pulled_direction : (channel.pulled msg).direction = .receive := rfl
@[circuit_norm] lemma pulled_enabled : (channel.pulled msg).enabled = 1 := rfl
@[circuit_norm] lemma pulled_msg : (channel.pulled msg).msg = msg := rfl
@[circuit_norm] lemma pulled_assumeGuarantees : (channel.pulled msg).assumeGuarantees = true := rfl

@[circuit_norm] lemma pushedIf_one_eq_pushed : channel.pushedIf 1 msg = channel.pushed msg := rfl
@[circuit_norm] lemma pulledIf_one_eq_pulled : channel.pulledIf 1 msg = channel.pulled msg := rfl
end
end DirectedChannel

namespace DirectedInteraction
variable {channel : DirectedChannel F Message}

/-- Erase to an `AbstractInteraction`: the raw message is the payload followed by the direction tag. -/
@[implicit_reducible]
def toRaw (i : DirectedInteraction channel) : AbstractInteraction F :=
  ⟨ channel.toRaw, i.enabled, (toElements i.msg).push (.const i.direction.tag), i.assumeGuarantees ⟩

@[circuit_norm] lemma toRaw_channel (i : DirectedInteraction channel) :
  i.toRaw.channel = channel.toRaw := rfl
@[circuit_norm] lemma toRaw_mult (i : DirectedInteraction channel) :
  i.toRaw.mult = i.enabled := rfl
@[circuit_norm] lemma toRaw_msg (i : DirectedInteraction channel) :
  i.toRaw.msg = (toElements i.msg).push (.const i.direction.tag) := rfl
@[circuit_norm] lemma toRaw_assumeGuarantees (i : DirectedInteraction channel) :
  i.toRaw.assumeGuarantees = i.assumeGuarantees := rfl

/-- What a row may assume: the guarantee, if it asked for it, is a receiver, and is active. -/
@[circuit_norm]
def Guarantees (i : DirectedInteraction channel) (env : Environment F) : Prop :=
  i.assumeGuarantees → i.direction = .receive → Expression.eval env i.enabled ≠ 0 →
    channel.Guarantees (eval env i.msg) env.data

/-- What a row must prove: a boolean gate, and the guarantee if it is an active provider. -/
@[circuit_norm]
def Requirements (i : DirectedInteraction channel) (env : Environment F) : Prop :=
  (Expression.eval env i.enabled = 0 ∨ Expression.eval env i.enabled = 1) ∧
  (i.direction = .provide → Expression.eval env i.enabled ≠ 0 →
    channel.Guarantees (eval env i.msg) env.data)

@[circuit_norm]
lemma toRaw_guarantees (env : Environment F) (i : DirectedInteraction channel) :
    i.toRaw.Guarantees env ↔ i.Guarantees env := by
  simp [AbstractInteraction.Guarantees, Guarantees, toRaw, DirectedChannel.toRaw,
    Vector.map_push, Vector.toArray_push, Array.back?_push, Vector.pop_push,
    ProvableType.fromElements_eval_toElements, Expression.eval, Direction.tag_inj_iff]

@[circuit_norm]
lemma toRaw_requirements (env : Environment F) (i : DirectedInteraction channel) :
    i.toRaw.Requirements env ↔ i.Requirements env := by
  simp [AbstractInteraction.Requirements, Requirements, toRaw, DirectedChannel.toRaw,
    Vector.map_push, Vector.toArray_push, Array.back?_push, Vector.pop_push,
    ProvableType.fromElements_eval_toElements, Expression.eval, Direction.tag_inj_iff]
end DirectedInteraction

/- ## Circuit operations -/

namespace DirectedChannel
/-- Interact in an explicit direction without assuming the guarantee. -/
@[circuit_norm]
def emit (channel : DirectedChannel F Message) (direction : Direction) (enabled : Expression F)
    (msg : Message (Expression F)) : Circuit F Unit := fun _ =>
  ((), [.interact (channel.emitted direction enabled msg).toRaw])

/-- Provide a message. The row must establish the channel guarantee for it. -/
@[circuit_norm]
def push (channel : DirectedChannel F Message) (msg : Message (Expression F)) : Circuit F Unit := fun _ =>
  ((), [.interact (channel.pushed msg).toRaw])

/-- Provide a message when `enabled = 1`. -/
@[circuit_norm]
def pushIf (channel : DirectedChannel F Message) (enabled : Expression F)
    (msg : Message (Expression F)) : Circuit F Unit := fun _ =>
  ((), [.interact (channel.pushedIf enabled msg).toRaw])

/-- Receive a message, assuming the channel guarantee for it. -/
@[circuit_norm]
def pull (channel : DirectedChannel F Message) (msg : Message (Expression F)) : Circuit F Unit := fun _ =>
  ((), [.interact (channel.pulled msg).toRaw])

/-- Receive a message when `enabled = 1`, assuming the channel guarantee when active. -/
@[circuit_norm]
def pullIf (channel : DirectedChannel F Message) (enabled : Expression F)
    (msg : Message (Expression F)) : Circuit F Unit := fun _ =>
  ((), [.interact (channel.pulledIf enabled msg).toRaw])
end DirectedChannel

attribute [explicit_circuit_no_unfold] DirectedChannel.emit DirectedChannel.push
  DirectedChannel.pushIf DirectedChannel.pull DirectedChannel.pullIf

section
variable {channel : DirectedChannel F Message}

instance {direction : Direction} {enabled : Expression F} :
    ExplicitCircuits (F:=F) (channel.emit direction enabled) where
  output _ _ := ()
  localLength _ _ := 0
  operations msg _ := [.interact (channel.emitted direction enabled msg).toRaw]
  channelsWithGuarantees _ _ := []

instance : ExplicitCircuits (F:=F) channel.push where
  output _ _ := ()
  localLength _ _ := 0
  operations msg _ := [.interact (channel.pushed msg).toRaw]
  channelsWithGuarantees _ _ := []

instance {enabled : Expression F} : ExplicitCircuits (F:=F) (channel.pushIf enabled) where
  output _ _ := ()
  localLength _ _ := 0
  operations msg _ := [.interact (channel.pushedIf enabled msg).toRaw]
  channelsWithGuarantees _ _ := []

instance : ExplicitCircuits (F:=F) channel.pull where
  output _ _ := ()
  localLength _ _ := 0
  operations msg _ := [.interact (channel.pulled msg).toRaw]
  channelsWithGuarantees _ _ := [channel.toRaw]

instance {enabled : Expression F} : ExplicitCircuits (F:=F) (channel.pullIf enabled) where
  output _ _ := ()
  localLength _ _ := 0
  operations msg _ := [.interact (channel.pulledIf enabled msg).toRaw]
  channelsWithGuarantees _ _ := [channel.toRaw]
end

/- ## Evaluated interactions -/

namespace DirectedChannel
variable {channel : DirectedChannel F Message}

/-- The evaluated form of any directed interaction. -/
@[circuit_norm]
def emittedValue (channel : DirectedChannel F Message) (direction : Direction) (enabled : F)
    (msg : Message F) (assumeGuarantees : Bool) : Interaction F where
  channel := channel.toRaw
  mult := enabled
  msg := ((toElements msg).push direction.tag).toArray
  same_size := by simp [toRaw]
  assumeGuarantees := assumeGuarantees

lemma emittedValue_msgVector (direction : Direction) (enabled : F) (msg : Message F)
    (assumeGuarantees : Bool) :
    (channel.emittedValue direction enabled msg assumeGuarantees).msgVector =
      (toElements msg).push direction.tag := rfl

/-- Evaluation of a typed directed interaction. -/
lemma eval_toRaw {i : DirectedInteraction channel} {env : Environment F} :
    i.toRaw.eval env =
      channel.emittedValue i.direction (Expression.eval env i.enabled) (eval env i.msg)
        i.assumeGuarantees := by
  simp only [circuit_norm, AbstractInteraction.eval, Interaction.mk.injEq, and_true, true_and]
  rw [ProvableType.toElements_eval, Vector.map_push]
  rfl
end DirectedChannel
