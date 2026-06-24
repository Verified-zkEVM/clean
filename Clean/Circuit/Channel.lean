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

/-- Conditional pull. When `enabled = 1`, this is a pull; when `enabled = 0`, it is disabled. -/
def pulledIf {channel : Channel F Message} (enabled : Expression F) (msg : Message (Expression F)) :
    ChannelInteraction channel :=
  { mult := -enabled, msg, assumeGuarantees := true }

@[circuit_norm] lemma pulled_def (msg : Message (Expression F)) :
  ({ mult := -1, msg, assumeGuarantees := true } : ChannelInteraction channel) = pulled msg := rfl
@[circuit_norm] lemma pulled_mult (msg : Message (Expression F)) :
  (pulled msg : ChannelInteraction channel).mult = -1 := rfl
@[circuit_norm] lemma pulled_msg (msg : Message (Expression F)) :
  (pulled msg : ChannelInteraction channel).msg = msg := rfl
@[circuit_norm] lemma pulled_assumeGuarantees (msg : Message (Expression F)) :
  (pulled msg : ChannelInteraction channel).assumeGuarantees = true := rfl

@[circuit_norm] lemma pulledIf_def (enabled : Expression F) (msg : Message (Expression F)) :
  ({ mult := -enabled, msg, assumeGuarantees := true } : ChannelInteraction channel) = pulledIf enabled msg := rfl
@[circuit_norm] lemma pulledIf_mult (enabled : Expression F) (msg : Message (Expression F)) :
  (pulledIf enabled msg : ChannelInteraction channel).mult = -enabled := rfl
@[circuit_norm] lemma pulledIf_msg (enabled : Expression F) (msg : Message (Expression F)) :
  (pulledIf enabled msg : ChannelInteraction channel).msg = msg := rfl
@[circuit_norm] lemma pulledIf_assumeGuarantees (enabled : Expression F) (msg : Message (Expression F)) :
  (pulledIf enabled msg : ChannelInteraction channel).assumeGuarantees = true := rfl
@[circuit_norm] lemma pulledIf_one_eq_pulled (msg : Message (Expression F)) :
  (pulledIf 1 msg : ChannelInteraction channel) = pulled msg := by
  simp [pulledIf, pulled]

/-- Convenience alias for interaction with multiplicity `1`. -/
def pushed {channel : Channel F Message} (msg : Message (Expression F)) : ChannelInteraction channel :=
  { mult := 1, msg, assumeGuarantees := false }

/-- Conditional push. When `enabled = 1`, this is a push; when `enabled = 0`, it is disabled. -/
def pushedIf {channel : Channel F Message} (enabled : Expression F) (msg : Message (Expression F)) :
    ChannelInteraction channel :=
  { mult := enabled, msg, assumeGuarantees := false }

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
@[circuit_norm] lemma pushedIf_one_eq_pushed (msg : Message (Expression F)) :
  (pushedIf 1 msg : ChannelInteraction channel) = pushed msg := by
  simp [pushedIf, pushed]

omit [Field F] in @[circuit_norm] lemma pushedIf_def (enabled : Expression F) (msg : Message (Expression F)) :
  ({ mult := enabled, msg, assumeGuarantees := false } : ChannelInteraction channel) = pushedIf enabled msg := rfl
omit [Field F] in @[circuit_norm] lemma emitted_eq_pushedIf (enabled : Expression F) (msg : Message (Expression F)) :
  (emitted enabled msg : ChannelInteraction channel) = pushedIf enabled msg := rfl
omit [Field F] in @[circuit_norm] lemma pushedIf_mult (enabled : Expression F) (msg : Message (Expression F)) :
  (pushedIf enabled msg : ChannelInteraction channel).mult = enabled := rfl
omit [Field F] in @[circuit_norm] lemma pushedIf_msg (enabled : Expression F) (msg : Message (Expression F)) :
  (pushedIf enabled msg : ChannelInteraction channel).msg = msg := rfl
omit [Field F] in @[circuit_norm] lemma pushedIf_assumeGuarantees (enabled : Expression F) (msg : Message (Expression F)) :
  (pushedIf enabled msg : ChannelInteraction channel).assumeGuarantees = false := rfl

@[circuit_norm] def Channel.emitted (channel : Channel F Message) mult msg :=
  _root_.emitted (channel := channel) mult msg
@[circuit_norm] def Channel.pulled (channel : Channel F Message) msg :=
  _root_.pulled (channel := channel) msg
@[circuit_norm] def Channel.pushed (channel : Channel F Message) msg :=
  _root_.pushed (channel := channel) msg
@[circuit_norm] def Channel.pulledIf (channel : Channel F Message) enabled msg :=
  _root_.pulledIf (channel := channel) enabled msg
@[circuit_norm] def Channel.pushedIf (channel : Channel F Message) enabled msg :=
  _root_.pushedIf (channel := channel) enabled msg

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

def expose {Message : TypeMap} [ProvableType Message] (channel : Channel F Message)
    (interactions : List (ChannelInteraction channel)) : List (ExposedChannel F) :=
  [{ channel, interactions := interactions.map (·.toRaw) }]

lemma channelInteraction_toRaw_inj {i j : ChannelInteraction channel} :
    i.toRaw = j.toRaw ↔ i = j := by
  constructor; swap
  · rintro rfl; rfl
  intro h
  rcases i with ⟨ mult, msg, assumeGuarantees ⟩
  rcases j with ⟨ mult', msg', assumeGuarantees' ⟩
  simp only [ChannelInteraction.toRaw, AbstractInteraction.mk.injEq,
    ChannelInteraction.mk.injEq, true_and] at h ⊢
  rcases h with ⟨ h_mult, h_msg, h_assume ⟩
  refine ⟨ h_mult, ?_, h_assume ⟩
  have h_msg_eq : toElements msg = toElements msg' := eq_of_heq h_msg
  rw [← ProvableType.fromElements_toElements msg,
    ← ProvableType.fromElements_toElements msg', h_msg_eq]

@[circuit_norm]
lemma mem_expose_pullIf_pushIf (enabled enabled' : Expression F)
    (pull pull' push push' : Message (Expression F)) :
    ⟨ channel.toRaw, [(pulledIf (channel := channel) enabled pull).toRaw,
      (pushedIf (channel := channel) enabled push).toRaw] ⟩ ∈
      expose channel [pulledIf enabled' pull', pushedIf enabled' push'] ↔
    enabled = enabled' ∧ pull = pull' ∧ push = push' := by
  simp only [expose, List.mem_singleton, List.map_cons, List.map_nil,
    ExposedChannel.mk.injEq, true_and, List.cons.injEq, and_true,
    channelInteraction_toRaw_inj, pulledIf, pushedIf]
  simp
  tauto

@[circuit_norm]
lemma mem_expose_pulled_pushed (pull pull' push push' : Message (Expression F)) :
    ⟨ channel.toRaw, [(pulled (channel := channel) pull).toRaw,
      (pushed (channel := channel) push).toRaw] ⟩ ∈
      expose channel [pulled pull', pushed push'] ↔
    pull = pull' ∧ push = push' := by
  simp only [expose, List.mem_singleton, List.map_cons, List.map_nil,
    ExposedChannel.mk.injEq, true_and, List.cons.injEq, and_true,
    channelInteraction_toRaw_inj, pulled, pushed]
  simp

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
def pulledIfValue (channel : Channel F Message) (enabled : F) (msg : Message F) : Interaction F where
  channel := channel.toRaw
  mult := -enabled
  msg := (toElements msg).toArray
  same_size := by simp [Channel.toRaw]
  assumeGuarantees := true

@[circuit_norm]
def pushedIfValue (channel : Channel F Message) (enabled : F) (msg : Message F) : Interaction F where
  channel := channel.toRaw
  mult := enabled
  msg := (toElements msg).toArray
  same_size := by simp [Channel.toRaw]
  assumeGuarantees := false

lemma pulledIfValue_requirements_of_isBool_enabled {channel : Channel F Message}
  {enabled : F} {msg : Message F} {data : ProverData F} :
    enabled = 0 ∨ enabled = 1 →
    (channel.pulledIfValue enabled msg).Requirements data := by
  simp only [Interaction.Requirements, Channel.pulledIfValue, Channel.toRaw]
  grind

lemma pushedIfValue_guarantees {channel : Channel F Message}
  {enabled : F} {msg : Message F} {data : ProverData F} :
    (channel.pushedIfValue enabled msg).Guarantees data := by
  simp [Interaction.Guarantees, Channel.pushedIfValue]

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

lemma eval_pulledIf {channel : Channel F Message} {enabled : Expression F}
    {msg : Message (Expression F)} {env : Environment F} :
     (channel.pulledIf enabled msg).toRaw.eval env = channel.pulledIfValue (eval env enabled) (eval env msg) := by
  simp only [circuit_norm, AbstractInteraction.eval, Interaction.mk.injEq]
  simp only [and_true, true_and]
  constructor
  · exact (neg_eq_neg_one_mul (env enabled)).symm
  · apply congrArg Vector.toArray
    rw [←ProvableType.fromElements_eq_iff, CircuitType.eval_var]
    rfl

lemma eval_pushedIf {channel : Channel F Message} {enabled : Expression F}
    {msg : Message (Expression F)} {env : Environment F} :
     (channel.pushedIf enabled msg).toRaw.eval env = channel.pushedIfValue (eval env enabled) (eval env msg) := by
  simp only [circuit_norm, AbstractInteraction.eval, Interaction.mk.injEq]
  simp only [and_true, true_and]
  congr
  rw [←ProvableType.fromElements_eq_iff, CircuitType.eval_var]
  rfl
end Channel
