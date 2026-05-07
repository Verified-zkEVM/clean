import Clean.Circuit.Expression
import Clean.Circuit.Provable
import Clean.Circuit.SimpGadget
import Mathlib.Data.Finsupp.Defs

variable {F : Type} [Field F] {α : Type} {n : ℕ}
variable {Message : TypeMap} [ProvableType Message]

structure Channel (F : Type) (Message : TypeMap) [ProvableType Message] where
  name : String
  /-- the guarantees you get from adding an interaction to the channel, to be used locally in your soundness proof -/
  Guarantees (message : Message F) (data : ProverData F) : Prop

/-- `Channel` with type argument removed, to be used in the core framework. -/
structure RawChannel (F : Type) where
  name : String
  arity : ℕ
  /-- the guarantees you get from adding an interaction to the channel, to be used locally in your soundness proof -/
  Guarantees (mult : F) (message : Vector F arity) (data : ProverData F) : Prop
  /--
  proof obligation from adding an interaction, to be _provided_ locally in your soundness proof.
  intuition: the `Guarantees` for multiplicity `-m` should follow from the `Requirements` for multiplicity `m`,
  so that pulling from the channel gives you a guarantee that is satisfied on the other side by the requirement for pushing
  the same element.
  -/
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

/--
Convert a `Channel` to a `RawChannel` by removing the type argument,
and adapting to the more general guarantees/requirements split.
-/
def Channel.toRaw (channel : Channel F Message) : RawChannel F where
  name := channel.name
  arity := size Message
  Guarantees mult message data :=
    mult = -1 → channel.Guarantees (fromElements message) data
  Requirements mult message data :=
    mult ≠ -1 →
    channel.Guarantees (fromElements message) data

instance : CoeOut (Channel F Message) (RawChannel F) where
  coe := Channel.toRaw

@[circuit_norm]
lemma Channel.toRaw_name (channel : Channel F Message) :
    channel.toRaw.name = channel.name := rfl
@[circuit_norm]
lemma Channel.toRaw_arity (channel : Channel F Message) :
    channel.toRaw.arity = size Message := rfl

/--
Expose equality of raw channels coming from typed channels in a form that `simp` can use.
In practice this mostly lets `circuit_norm` discharge channel comparisons by reducing them
to name mismatches, while equal concrete channels close by reflexivity.
-/
@[circuit_norm]
lemma Channel.toRaw_ext_iff {Message2 : TypeMap} [ProvableType Message2]
  (channel1 : Channel F Message) (channel2 : Channel F Message2) :
    channel1.toRaw = channel2.toRaw ↔
    channel1.name = channel2.name ∧
    size Message = size Message2 ∧
    ((fun mult message data ↦ mult = (-1 : F) → channel1.Guarantees (fromElements message) data) ≍
      fun mult message data ↦ mult = (-1 : F) → channel2.Guarantees (fromElements message) data) ∧
    (fun mult message data ↦ mult ≠ (-1 : F) → channel1.Guarantees (fromElements message) data) ≍
      fun mult message data ↦ mult ≠ (-1 : F) → channel2.Guarantees (fromElements message) data := by
  simp only [Channel.toRaw, RawChannel.mk.injEq]

structure ChannelInteraction (channel : Channel F Message) where
  mult : Expression F
  msg : Message (Expression F)
  assumeGuarantees : Bool

variable {channel : Channel F Message}

def ChannelInteraction.toRaw (i : ChannelInteraction channel) : AbstractInteraction F :=
  ⟨ channel.toRaw, i.mult, toElements i.msg, i.assumeGuarantees ⟩

/-- Normal form for a channel interaction. -/
def emitted (mult : Expression F) (msg : Message (Expression F)) : ChannelInteraction channel :=
  { mult, msg, assumeGuarantees := false }

/-- Convenience alias for interaction with multiplicity `-1`. -/
@[circuit_norm]
def pulled {channel : Channel F Message} (msg : Message (Expression F)) : ChannelInteraction channel :=
  { mult := -1, msg, assumeGuarantees := true }

/-- Convenience alias for interaction with multiplicity `1`. -/
@[circuit_norm]
def pushed {channel : Channel F Message} (msg : Message (Expression F)) : ChannelInteraction channel :=
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
    (interactions : List (ChannelInteraction channel)) : List (ExposedChannel F) :=
  [{ channel, interactions := interactions.map (·.toRaw) }]

@[circuit_norm]
lemma ChannelInteraction.toRaw_channel (i : ChannelInteraction channel) :
  i.toRaw.channel = channel.toRaw := rfl

@[circuit_norm]
lemma ChannelInteraction.toRaw_mult (i : ChannelInteraction channel) :
  i.toRaw.mult = i.mult := rfl

@[circuit_norm]
lemma ChannelInteraction.toRaw_msg (i : ChannelInteraction channel) :
    i.toRaw.msg = toElements i.msg := rfl

@[circuit_norm]
lemma ChannelInteraction.toRaw_assumeGuarantees (i : ChannelInteraction channel) :
    i.toRaw.assumeGuarantees = i.assumeGuarantees := rfl

variable {Message' : TypeMap} [ProvableType Message']

@[circuit_norm]
def ChannelInteraction.Guarantees (i : ChannelInteraction channel) (env : Environment F) : Prop :=
  i.assumeGuarantees → Expression.eval env i.mult = -1 → channel.Guarantees (eval env i.msg) env.data

def AbstractInteraction.Guarantees (i : AbstractInteraction F) (env : Environment F) : Prop :=
  i.assumeGuarantees → i.channel.Guarantees (env i.mult) (i.msg.map env) env.data

@[circuit_norm]
lemma AbstractInteraction.guarantees_def (env : Environment F) (int : ChannelInteraction channel) :
    int.toRaw.Guarantees env ↔ int.Guarantees env := by
  simp [AbstractInteraction.Guarantees, ChannelInteraction.Guarantees,
    ChannelInteraction.toRaw, Channel.toRaw, ProvableType.fromElements_eval_toElements]

@[circuit_norm]
def ChannelInteraction.Requirements (i : ChannelInteraction channel) (env : Environment F) : Prop :=
  Expression.eval env i.mult ≠ -1 → channel.Guarantees (eval env i.msg) env.data

def AbstractInteraction.Requirements (i : AbstractInteraction F) (env : Environment F) : Prop :=
  i.channel.Requirements (env i.mult) (i.msg.map env) env.data

@[circuit_norm]
lemma AbstractInteraction.requirements_def (env : Environment F) (int : ChannelInteraction channel) :
    int.toRaw.Requirements env ↔ int.Requirements env := by
  simp [AbstractInteraction.Requirements, ChannelInteraction.Requirements,
    ChannelInteraction.toRaw, Channel.toRaw, ProvableType.fromElements_eval_toElements]
