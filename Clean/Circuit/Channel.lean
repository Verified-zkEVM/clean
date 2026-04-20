import Clean.Circuit.Expression
import Clean.Circuit.Provable
import Clean.Circuit.SimpGadget
import Mathlib.Data.Finsupp.Defs

variable {F : Type} [Field F] {α : Type} {n : ℕ}
variable {Message : TypeMap} [ProvableType Message]

structure Channel (F : Type) (Message : TypeMap) [ProvableType Message] where
  name : String

  /-- the guarantees you get from adding an interaction to the channel, to be used locally in your soundness proof -/
  Guarantees (mult : F) (message : Message F) (data : ProverData F) : Prop

  /-- additional proof obligation from adding an interaction, to be _provided_ locally in your soundness proof.
    intuition: the `Guarantees` for multiplicity `-m` should follow from the `Requirements` for multiplicity `m`,
    so that pulling from the channel gives you a guarantee that is satisfied on the other side by the requirement for pushing
    the same element.
   -/
  Requirements (mult : F) (message : Message F) (data : ProverData F) : Prop

/-- `Channel` with type argument removed, to be used in the core framework. -/
structure RawChannel (F : Type) where
  name : String
  arity : ℕ
  Guarantees (mult : F) (message : Vector F arity) (data : ProverData F) : Prop
  Requirements (mult : F) (message : Vector F arity) (data : ProverData F) : Prop

structure AbstractInteraction (F : Type) where
  channel : RawChannel F
  mult : Expression F
  msg : Vector (Expression F) channel.arity
  assumeGuarantees : Bool

instance [Repr F] : Repr (AbstractInteraction F) where
  reprPrec i _ :=
    "(Interaction channel=" ++ i.channel.name ++
    ", mult=" ++ repr i.mult ++ ", msg=" ++ repr i.msg ++ ")"

def Channel.interactionFromRaw (interaction : F × Vector F (size Message)) :
    F × Message F := (interaction.1, fromElements interaction.2)

/-- Convert a `Channel` to a `RawChannel` by removing the type argument -/
def Channel.toRaw (channel : Channel F Message) : RawChannel F where
  name := channel.name
  arity := size Message
  Guarantees mult message data :=
    channel.Guarantees mult (fromElements message) data
  Requirements mult message data :=
    channel.Requirements mult (fromElements message) data

instance : CoeOut (Channel F Message) (RawChannel F) where
  coe := Channel.toRaw

omit [Field F] in
@[circuit_norm]
lemma Channel.toRaw_name (channel : Channel F Message) :
    channel.toRaw.name = channel.name := rfl
omit [Field F] in
@[circuit_norm]
lemma Channel.toRaw_arity (channel : Channel F Message) :
    channel.toRaw.arity = size Message := rfl

omit [Field F] in
-- TODO the HEq between functions is ugly, let's see how provable that is
@[circuit_norm]
lemma Channel.toRaw_ext_iff {Message2 : TypeMap} [ProvableType Message2] (channel1 : Channel F Message) (channel2 : Channel F Message2) :
    channel1.toRaw = channel2.toRaw ↔
    channel1.name = channel2.name ∧
    size Message = size Message2 ∧
    ((fun mult message data ↦ channel1.Guarantees mult (fromElements message) data) ≍ fun mult message data ↦
        channel2.Guarantees mult (fromElements message) data) ∧
    (fun mult message data ↦ channel1.Requirements mult (fromElements message) data) ≍ fun mult message data ↦
        channel2.Requirements mult (fromElements message) data := by
  simp only [Channel.toRaw, RawChannel.mk.injEq]

structure InteractionWithChannel (channel : Channel F Message) where
  mult : Expression F
  msg : Message (Expression F)
  assumeGuarantees : Bool

variable {channel : Channel F Message}

def InteractionWithChannel.toRaw (i : InteractionWithChannel channel) : AbstractInteraction F :=
  ⟨ channel.toRaw, i.mult, toElements i.msg, i.assumeGuarantees ⟩

/-- Normal form for a channel interaction. -/
def emitted (mult : Expression F) (msg : Message (Expression F)) : InteractionWithChannel channel :=
  { mult, msg, assumeGuarantees := false }

/-- Convenience alias for interaction with multiplicity `-1`. -/
@[circuit_norm]
def pulled {channel : Channel F Message} (msg : Message (Expression F)) : InteractionWithChannel channel :=
  { mult := -1, msg, assumeGuarantees := true }

/-- Convenience alias for interaction with multiplicity `1`. -/
@[circuit_norm]
def pushed {channel : Channel F Message} (msg : Message (Expression F)) : InteractionWithChannel channel :=
  { mult := 1, msg, assumeGuarantees := false }

@[circuit_norm] def Channel.emitted (channel : Channel F Message) mult msg :=
  _root_.emitted (channel := channel) mult msg
@[circuit_norm] def Channel.pulled (channel : Channel F Message) msg :=
  _root_.pulled (channel := channel) msg
@[circuit_norm] def Channel.pushed (channel : Channel F Message) msg :=
  _root_.pushed (channel := channel) msg

structure ExposedChannel (F : Type) [Field F] where
  channel : RawChannel F
  interactions : List (AbstractInteraction F)

@[circuit_norm]
def expose {Message : TypeMap} [ProvableType Message] (channel : Channel F Message)
    (interactions : List (InteractionWithChannel channel)) : List (ExposedChannel F) :=
  [{ channel, interactions := interactions.map (·.toRaw) }]

omit [Field F] in @[circuit_norm]
lemma InteractionWithChannel.toRaw_channel (i : InteractionWithChannel channel) :
  i.toRaw.channel = channel.toRaw := rfl

omit [Field F] in @[circuit_norm]
lemma InteractionWithChannel.toRaw_mult (i : InteractionWithChannel channel) :
  i.toRaw.mult = i.mult := rfl

omit [Field F] in @[circuit_norm]
lemma InteractionWithChannel.toRaw_msg (i : InteractionWithChannel channel) :
    i.toRaw.msg = toElements i.msg := rfl

omit [Field F] in @[circuit_norm]
lemma InteractionWithChannel.toRaw_assumeGuarantees (i : InteractionWithChannel channel) :
    i.toRaw.assumeGuarantees = i.assumeGuarantees := rfl

@[circuit_norm]
lemma Channel.interactionFromRaw_eq (env : Environment F)
  (mult : F) (msg : Message (Expression F)) :
    Channel.interactionFromRaw (mult, (toElements msg).map env) = (mult, eval env msg) := by
  rfl

variable {Message' : TypeMap} [ProvableType Message']

@[circuit_norm]
def InteractionWithChannel.Guarantees (i : InteractionWithChannel channel) (env : Environment F) : Prop :=
  i.assumeGuarantees → channel.Guarantees (env i.mult) (eval env i.msg) env.data

def AbstractInteraction.Guarantees (i : AbstractInteraction F) (env : Environment F) : Prop :=
  i.assumeGuarantees → i.channel.Guarantees (env i.mult) (i.msg.map env) env.data

@[circuit_norm]
lemma AbstractInteraction.guarantees_def (env : Environment F) (int : InteractionWithChannel channel) :
    int.toRaw.Guarantees env ↔ int.Guarantees env := by rfl

@[circuit_norm]
def InteractionWithChannel.Requirements (i : InteractionWithChannel channel) (env : Environment F) : Prop :=
  channel.Requirements (env i.mult) (eval env i.msg) env.data

def AbstractInteraction.Requirements (i : AbstractInteraction F) (env : Environment F) : Prop :=
  i.channel.Requirements (env i.mult) (i.msg.map env) env.data

@[circuit_norm]
lemma AbstractInteraction.requirements_def (env : Environment F) (int : InteractionWithChannel channel) :
    int.toRaw.Requirements env ↔ int.Requirements env := by rfl
