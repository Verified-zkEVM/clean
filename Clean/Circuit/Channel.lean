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
    mult ≠ 0 →
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
    (fun mult message data ↦ mult ≠ (-1 : F) → mult ≠ 0 → channel1.Guarantees (fromElements message) data) ≍
      fun mult message data ↦ mult ≠ (-1 : F) → mult ≠ 0 → channel2.Guarantees (fromElements message) data := by
  simp only [toRaw, RawChannel.mk.injEq]
end Channel

/--
Static lookup channels expose a predicate that is equivalent
to being a member of a fixed list of values.
-/
structure StaticLookupChannel (F : Type) [Field F] (Message : TypeMap) [ProvableType Message] where
  name : String
  table : List (Message F)
  Guarantees : Message F → Prop
  guarantees_iff : ∀ msg, Guarantees msg ↔ msg ∈ table

@[circuit_norm]
def Channel.fromStatic (F : Type) [Field F]
    (Message : TypeMap) [ProvableType Message]
    (slc : StaticLookupChannel F Message) : Channel F Message where
  name := slc.name
  Guarantees msg _ := slc.Guarantees msg

/--
A _channel interaction_ is a channel message along with a multiplicity.

In addition, via `assumeGuarantees`, the interaction can opt into carrying the
channel guarantees as assumptions (relevant in soundness and completeness proofs).
-/
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

/-- Conditional pull. When `gate = 1`, this is a pull; when `gate = 0`, it is disabled. -/
def pullIf {channel : Channel F Message} (gate : Expression F) (msg : Message (Expression F)) :
    ChannelInteraction channel :=
  { mult := -gate, msg, assumeGuarantees := true }

@[circuit_norm] lemma pulled_def (msg : Message (Expression F)) :
  ({ mult := -1, msg, assumeGuarantees := true } : ChannelInteraction channel) = pulled msg := rfl
@[circuit_norm] lemma pulled_mult (msg : Message (Expression F)) :
  (pulled msg : ChannelInteraction channel).mult = -1 := rfl
@[circuit_norm] lemma pulled_msg (msg : Message (Expression F)) :
  (pulled msg : ChannelInteraction channel).msg = msg := rfl
@[circuit_norm] lemma pulled_assumeGuarantees (msg : Message (Expression F)) :
  (pulled msg : ChannelInteraction channel).assumeGuarantees = true := rfl

@[circuit_norm] lemma pullIf_def (gate : Expression F) (msg : Message (Expression F)) :
  ({ mult := -gate, msg, assumeGuarantees := true } : ChannelInteraction channel) = pullIf gate msg := rfl
@[circuit_norm] lemma pulled_eq_pullIf_one (msg : Message (Expression F)) :
  (pulled msg : ChannelInteraction channel) = pullIf 1 msg := rfl
@[circuit_norm] lemma pullIf_mult (gate : Expression F) (msg : Message (Expression F)) :
  (pullIf gate msg : ChannelInteraction channel).mult = -gate := rfl
@[circuit_norm] lemma pullIf_msg (gate : Expression F) (msg : Message (Expression F)) :
  (pullIf gate msg : ChannelInteraction channel).msg = msg := rfl
@[circuit_norm] lemma pullIf_assumeGuarantees (gate : Expression F) (msg : Message (Expression F)) :
  (pullIf gate msg : ChannelInteraction channel).assumeGuarantees = true := rfl

/-- Convenience alias for interaction with multiplicity `1`. -/
def pushed {channel : Channel F Message} (msg : Message (Expression F)) : ChannelInteraction channel :=
  { mult := 1, msg, assumeGuarantees := false }

/-- Conditional push. When `gate = 1`, this is a push; when `gate = 0`, it is disabled. -/
def pushIf {channel : Channel F Message} (gate : Expression F) (msg : Message (Expression F)) :
    ChannelInteraction channel :=
  { mult := gate, msg, assumeGuarantees := false }

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

omit [Field F] in @[circuit_norm] lemma pushIf_def (gate : Expression F) (msg : Message (Expression F)) :
  ({ mult := gate, msg, assumeGuarantees := false } : ChannelInteraction channel) = pushIf gate msg := rfl
@[circuit_norm] lemma pushed_eq_pushIf_one (msg : Message (Expression F)) :
  (pushed msg : ChannelInteraction channel) = pushIf 1 msg := rfl
omit [Field F] in @[circuit_norm] lemma pushIf_mult (gate : Expression F) (msg : Message (Expression F)) :
  (pushIf gate msg : ChannelInteraction channel).mult = gate := rfl
omit [Field F] in @[circuit_norm] lemma pushIf_msg (gate : Expression F) (msg : Message (Expression F)) :
  (pushIf gate msg : ChannelInteraction channel).msg = msg := rfl
omit [Field F] in @[circuit_norm] lemma pushIf_assumeGuarantees (gate : Expression F) (msg : Message (Expression F)) :
  (pushIf gate msg : ChannelInteraction channel).assumeGuarantees = false := rfl

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
  Expression.eval env i.mult ≠ -1 → Expression.eval env i.mult ≠ 0 →
    channel.Guarantees (eval env i.msg) env.data
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

/--
Concrete interaction values are heterogeneous: after evaluation, we collect interactions for
all channels in one list. The typed `Channel F Message` wrapper still remembers message shape
when building interactions, while this raw representation carries the channel arity explicitly.
-/
structure Interaction (F : Type) where
  channel : RawChannel F
  mult : F
  msg : Array F
  same_size : msg.size = channel.arity
  assumeGuarantees : Bool

namespace Interaction
def msgVector (i : Interaction F) : Vector F i.channel.arity :=
  ⟨ i.msg, i.same_size ⟩

def Guarantees (i : Interaction F) (data : ProverData F) : Prop :=
  i.assumeGuarantees → i.channel.Guarantees i.mult i.msgVector data

def Requirements (i : Interaction F) (data : ProverData F) : Prop :=
  i.channel.Requirements i.mult i.msgVector data
end Interaction

namespace AbstractInteraction
def eval (env : Environment F) (i : AbstractInteraction F) : Interaction F where
  channel := i.channel
  mult := env i.mult
  msg := (i.msg.map env).toArray
  same_size := by simp
  assumeGuarantees := i.assumeGuarantees

@[circuit_norm]
lemma eval_channel {i : AbstractInteraction F} {env : Environment F} :
  (i.eval env).channel = i.channel := rfl

@[circuit_norm]
lemma eval_guarantees {i : AbstractInteraction F} {env : Environment F} :
    (i.eval env).Guarantees env.data ↔ i.Guarantees env := by
  simp only [Interaction.Guarantees, AbstractInteraction.eval, AbstractInteraction.Guarantees]
  rfl

@[circuit_norm]
lemma eval_requirements {i : AbstractInteraction F} {env : Environment F} :
    (i.eval env).Requirements env.data ↔ i.Requirements env := by
  simp only [Interaction.Requirements, AbstractInteraction.eval, AbstractInteraction.Requirements]
  rfl
end AbstractInteraction

namespace Channel
@[circuit_norm]
def pulledValue (channel : Channel F Message) (msg : Message F) : Interaction F where
  channel := channel.toRaw
  mult := -1
  msg := (toElements msg).toArray
  same_size := by simp [Channel.toRaw]
  assumeGuarantees := true

@[circuit_norm]
def pushedValue (channel : Channel F Message) (msg : Message F) : Interaction F where
  channel := channel.toRaw
  mult := 1
  msg := (toElements msg).toArray
  same_size := by simp [Channel.toRaw]
  assumeGuarantees := false

@[circuit_norm]
def pullIfValue (channel : Channel F Message) (gate : F) (msg : Message F) : Interaction F where
  channel := channel.toRaw
  mult := -gate
  msg := (toElements msg).toArray
  same_size := by simp [Channel.toRaw]
  assumeGuarantees := true

@[circuit_norm]
def pushIfValue (channel : Channel F Message) (gate : F) (msg : Message F) : Interaction F where
  channel := channel.toRaw
  mult := gate
  msg := (toElements msg).toArray
  same_size := by simp [Channel.toRaw]
  assumeGuarantees := false

lemma eval_pulled {channel : Channel F Message} {msg : Message (Expression F)} {env : Environment F} :
     (channel.pulled msg).toRaw.eval env = channel.pulledValue (eval env msg) := by
  simp only [circuit_norm, AbstractInteraction.eval, Interaction.mk.injEq]
  simp only [mul_one, and_true, true_and]
  congr
  rw [←ProvableType.fromElements_eq_iff, CircuitType.eval_var]
  rfl

lemma eval_pushed {channel : Channel F Message} {msg : Message (Expression F)} {env : Environment F} :
     (channel.pushed msg).toRaw.eval env = channel.pushedValue (eval env msg) := by
  simp only [circuit_norm, AbstractInteraction.eval, Interaction.mk.injEq]
  simp only [and_true, true_and]
  congr
  rw [←ProvableType.fromElements_eq_iff, CircuitType.eval_var]
  rfl

lemma eval_pullIf {channel : Channel F Message} {gate : Expression F}
    {msg : Message (Expression F)} {env : Environment F} :
     (pullIf (channel:=channel) gate msg).toRaw.eval env = channel.pullIfValue (env gate) (eval env msg) := by
  simp only [circuit_norm, AbstractInteraction.eval, Interaction.mk.injEq]
  simp only [and_true, true_and]
  constructor
  · exact (neg_eq_neg_one_mul (env gate)).symm
  · apply congrArg Vector.toArray
    rw [←ProvableType.fromElements_eq_iff, CircuitType.eval_var]
    rfl

lemma eval_pushIf {channel : Channel F Message} {gate : Expression F}
    {msg : Message (Expression F)} {env : Environment F} :
     (pushIf (channel:=channel) gate msg).toRaw.eval env = channel.pushIfValue (env gate) (eval env msg) := by
  simp only [circuit_norm, AbstractInteraction.eval, Interaction.mk.injEq]
  simp only [and_true, true_and]
  congr
  rw [←ProvableType.fromElements_eq_iff, CircuitType.eval_var]
  rfl
end Channel
