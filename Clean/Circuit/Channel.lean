import Clean.Circuit.Expression
import Clean.Circuit.Provable
import Clean.Circuit.SimpGadget
import Mathlib.Data.Finsupp.Defs

variable {F : Type} [Field F]
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

namespace Channel
/--
Convert a `Channel` to a `RawChannel` by removing the type argument,
and adapting to the more general guarantees/requirements split.
-/
def toRaw (channel : Channel F Message) : RawChannel F where
  name := channel.name
  arity := size Message
  Guarantees mult message data :=
    mult = -1 → channel.Guarantees (fromElements message) data
  Requirements mult message data :=
    mult ≠ -1 →
    channel.Guarantees (fromElements message) data

instance : CoeOut (Channel F Message) (RawChannel F) where
  coe := toRaw

@[circuit_norm]
lemma toRaw_name (channel : Channel F Message) :
    channel.toRaw.name = channel.name := rfl
@[circuit_norm]
lemma toRaw_arity (channel : Channel F Message) :
    channel.toRaw.arity = size Message := rfl

/--
Expose equality of raw channels coming from typed channels in a form that `simp` can use.
In practice this mostly lets `circuit_norm` discharge channel comparisons by reducing them
to name mismatches, while equal concrete channels close by reflexivity.
-/
@[circuit_norm]
lemma toRaw_ext_iff {Message2 : TypeMap} [ProvableType Message2]
  (channel1 : Channel F Message) (channel2 : Channel F Message2) :
    channel1.toRaw = channel2.toRaw ↔
    channel1.name = channel2.name ∧
    size Message = size Message2 ∧
    ((fun mult message data ↦ mult = (-1 : F) → channel1.Guarantees (fromElements message) data) ≍
      fun mult message data ↦ mult = (-1 : F) → channel2.Guarantees (fromElements message) data) ∧
    (fun mult message data ↦ mult ≠ (-1 : F) → channel1.Guarantees (fromElements message) data) ≍
      fun mult message data ↦ mult ≠ (-1 : F) → channel2.Guarantees (fromElements message) data := by
  simp only [toRaw, RawChannel.mk.injEq]
end Channel

structure ChannelInteraction (channel : Channel F Message) where
  mult : Expression F
  msg : Message (Expression F)
  assumeGuarantees : Bool

structure AbstractInteraction (F : Type) where
  channel : RawChannel F
  mult : Expression F
  msg : Vector (Expression F) channel.arity
  assumeGuarantees : Bool

instance [Repr F] : Repr (AbstractInteraction F) where
  reprPrec i _ :=
    "(Interaction channel=" ++ i.channel.name ++
    ", mult=" ++ repr i.mult ++ ", msg=" ++ repr i.msg ++ ")"

variable {channel : Channel F Message}

/-- Normal form for a channel interaction. -/
def emitted (mult : Expression F) (msg : Message (Expression F)) : ChannelInteraction channel :=
  { mult, msg, assumeGuarantees := false }

omit [Field F] in @[circuit_norm]
lemma emitted_def (mult : Expression F) (msg : Message (Expression F)) :
  ({ mult, msg, assumeGuarantees := false } : ChannelInteraction channel) = emitted mult msg := rfl
omit [Field F] in @[circuit_norm]
lemma emitted_mult (mult : Expression F) (msg : Message (Expression F)) :
  (emitted mult msg : ChannelInteraction channel).mult = mult := rfl
omit [Field F] in @[circuit_norm]
lemma emitted_msg (mult : Expression F) (msg : Message (Expression F)) :
  (emitted mult msg : ChannelInteraction channel).msg = msg := rfl
omit [Field F] in @[circuit_norm]
lemma emitted_assumeGuarantees (mult : Expression F) (msg : Message (Expression F)) :
  (emitted mult msg : ChannelInteraction channel).assumeGuarantees = false := rfl

/-- Convenience alias for interaction with multiplicity `-1`. -/
def pulled {channel : Channel F Message} (msg : Message (Expression F)) : ChannelInteraction channel :=
  { mult := -1, msg, assumeGuarantees := true }

@[circuit_norm] lemma pulled_def (msg : Message (Expression F)) :
  ({ mult := -1, msg, assumeGuarantees := true } : ChannelInteraction channel) = pulled msg := rfl
@[circuit_norm] lemma pulled_mult (msg : Message (Expression F)) :
  (pulled msg : ChannelInteraction channel).mult = -1 := rfl
@[circuit_norm] lemma pulled_msg (msg : Message (Expression F)) :
  (pulled msg : ChannelInteraction channel).msg = msg := rfl
@[circuit_norm] lemma pulled_assumeGuarantees (msg : Message (Expression F)) :
  (pulled msg : ChannelInteraction channel).assumeGuarantees = true := rfl

/-- Convenience alias for interaction with multiplicity `1`. -/
def pushed {channel : Channel F Message} (msg : Message (Expression F)) : ChannelInteraction channel :=
  { mult := 1, msg, assumeGuarantees := false }

@[circuit_norm] lemma pushed_def (msg : Message (Expression F)) :
  ({ mult := 1, msg, assumeGuarantees := false } : ChannelInteraction channel) = pushed msg := rfl
@[circuit_norm] lemma emitted_eq_pushed (msg : Message (Expression F)) :
  (emitted 1 msg : ChannelInteraction channel) = pushed msg := rfl
@[circuit_norm] lemma pushed_mult (msg : Message (Expression F)) :
  (pushed msg : ChannelInteraction channel).mult = 1 := rfl
@[circuit_norm] lemma pushed_msg (msg : Message (Expression F)) :
  (pushed msg : ChannelInteraction channel).msg = msg := rfl
@[circuit_norm] lemma pushed_assumeGuarantees (msg : Message (Expression F)) :
  (pushed msg : ChannelInteraction channel).assumeGuarantees = false := rfl

@[circuit_norm] def Channel.emitted (channel : Channel F Message) mult msg :=
  _root_.emitted (channel := channel) mult msg
@[circuit_norm] def Channel.pulled (channel : Channel F Message) msg :=
  _root_.pulled (channel := channel) msg
@[circuit_norm] def Channel.pushed (channel : Channel F Message) msg :=
  _root_.pushed (channel := channel) msg

namespace ChannelInteraction
def toRaw (i : ChannelInteraction channel) : AbstractInteraction F :=
  ⟨ channel.toRaw, i.mult, toElements i.msg, i.assumeGuarantees ⟩

@[circuit_norm] lemma toRaw_channel (i : ChannelInteraction channel) :
  i.toRaw.channel = channel.toRaw := rfl
@[circuit_norm] lemma toRaw_mult (i : ChannelInteraction channel) :
  i.toRaw.mult = i.mult := rfl
@[circuit_norm] lemma toRaw_msg (i : ChannelInteraction channel) :
    i.toRaw.msg = toElements i.msg := rfl
@[circuit_norm] lemma toRaw_assumeGuarantees (i : ChannelInteraction channel) :
    i.toRaw.assumeGuarantees = i.assumeGuarantees := rfl

@[circuit_norm]
def Guarantees (i : ChannelInteraction channel) (env : Environment F) : Prop :=
  i.assumeGuarantees → Expression.eval env i.mult = -1 → channel.Guarantees (eval env i.msg) env.data

@[circuit_norm]
def Requirements (i : ChannelInteraction channel) (env : Environment F) : Prop :=
  Expression.eval env i.mult ≠ -1 → channel.Guarantees (eval env i.msg) env.data
end ChannelInteraction

namespace AbstractInteraction
def Guarantees (i : AbstractInteraction F) (env : Environment F) : Prop :=
  i.assumeGuarantees → i.channel.Guarantees (env i.mult) (i.msg.map env) env.data

def Requirements (i : AbstractInteraction F) (env : Environment F) : Prop :=
  i.channel.Requirements (env i.mult) (i.msg.map env) env.data
end AbstractInteraction

namespace ChannelInteraction
@[circuit_norm]
lemma toRaw_guarantees (env : Environment F) (int : ChannelInteraction channel) :
    int.toRaw.Guarantees env ↔ int.Guarantees env := by
  simp [AbstractInteraction.Guarantees, ChannelInteraction.Guarantees,
    ChannelInteraction.toRaw, Channel.toRaw, ProvableType.fromElements_eval_toElements]

@[circuit_norm]
lemma toRaw_requirements (env : Environment F) (int : ChannelInteraction channel) :
    int.toRaw.Requirements env ↔ int.Requirements env := by
  simp [AbstractInteraction.Requirements, ChannelInteraction.Requirements,
    ChannelInteraction.toRaw, Channel.toRaw, ProvableType.fromElements_eval_toElements]
end ChannelInteraction

structure ExposedChannel (F : Type) [Field F] where
  channel : RawChannel F
  interactions : List (AbstractInteraction F)

@[circuit_norm]
def expose {Message : TypeMap} [ProvableType Message] (channel : Channel F Message)
    (interactions : List (ChannelInteraction channel)) : List (ExposedChannel F) :=
  [{ channel, interactions := interactions.map (·.toRaw) }]
