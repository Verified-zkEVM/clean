module

public import Clean.Circuit.Expression
public import Clean.Circuit.Provable
public import Clean.Circuit.SimpGadget
public import Mathlib.Data.Finsupp.Defs

@[expose] public section

variable {F : Type} [FiniteField F]
variable {Message : TypeMap} [ProvableType Message]

/-- Whether an interaction adds messages to a channel or takes them from it. -/
inductive Direction where
  | push
  | pull
deriving Repr, DecidableEq, Inhabited

def Direction.name : Direction → String
  | .push => "push"
  | .pull => "pull"

@[simp, circuit_norm] lemma Direction.push_eq_pull_iff : Direction.push = .pull ↔ False := by
  simp
@[simp, circuit_norm] lemma Direction.pull_eq_push_iff : Direction.pull = .push ↔ False := by
  simp

/-- What an interaction of multiplicity `mult` owes, given the guarantee of its message: an active
push owes the guarantee, and a pull has multiplicity `0` or `1`. -/
def Direction.Requirements {F : Type} [Zero F] [One F] (direction : Direction) (mult : F)
    (guarantee : Prop) : Prop :=
  match direction with
  | .push => mult ≠ 0 → guarantee
  | .pull => mult = 0 ∨ mult = 1

@[simp, circuit_norm] lemma Direction.push_requirements {F : Type} [Zero F] [One F] (mult : F)
    (guarantee : Prop) : Direction.push.Requirements mult guarantee = (mult ≠ 0 → guarantee) :=
  rfl
@[simp, circuit_norm] lemma Direction.pull_requirements {F : Type} [Zero F] [One F] (mult : F)
    (guarantee : Prop) : Direction.pull.Requirements mult guarantee = (mult = 0 ∨ mult = 1) :=
  rfl

structure Channel (F : Type) (Message : TypeMap) [ProvableType Message] where
  name : String
  /-- the guarantees you get from adding an interaction to the channel, to be used locally in your soundness proof -/
  Guarantees (message : Message F) (data : ProverData F) : Prop

/-- `Channel` with type argument removed, to be used in the core framework. -/
structure RawChannel (F : Type) where
  name : String
  arity : ℕ
  /-- the guarantees you get from pulling from the channel, to be used locally in your soundness proof -/
  Guarantees (mult : F) (message : Vector F arity) (data : ProverData F) : Prop
  /--
  proof obligation from adding an interaction, to be _provided_ locally in your soundness proof.
  intuition: the `Guarantees` of a pull should follow from the `Requirements` of a push,
  so that pulling from the channel gives you a guarantee that is satisfied on the other side by the requirement for pushing
  the same element.
  -/
  Requirements (direction : Direction) (mult : F) (message : Vector F arity) (data : ProverData F) : Prop

namespace Channel
/--
Convert a `Channel` to a `RawChannel` by removing the type argument,
and adapting to the more general guarantees/requirements split.

A pull of multiplicity `1` gets the guarantee, and an active push requires it. A pull requires its
multiplicity to be `0` or `1`: under field-sum balance, a pull of other multiplicities could cancel
other pulls like a push.
-/
-- The erased channel's arity indexes raw interaction message vectors.
@[implicit_reducible]
def toRaw (channel : Channel F Message) : RawChannel F where
  name := channel.name
  arity := size Message
  Guarantees mult message data :=
    mult = 1 → channel.Guarantees (fromElements message) data
  Requirements direction mult message data :=
    direction.Requirements mult (channel.Guarantees (fromElements message) data)

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
    ((fun (mult : F) message data ↦ mult = 1 →
        channel1.Guarantees (fromElements message) data) ≍
      fun (mult : F) message data ↦ mult = 1 →
        channel2.Guarantees (fromElements message) data) ∧
    (fun (direction : Direction) (mult : F) message data ↦
        direction.Requirements mult (channel1.Guarantees (fromElements message) data)) ≍
      fun (direction : Direction) (mult : F) message data ↦
        direction.Requirements mult (channel2.Guarantees (fromElements message) data) := by
  simp only [toRaw, RawChannel.mk.injEq]
end Channel

/--
A _channel interaction_ is a channel message along with a direction and a multiplicity: the number
of times the message is pushed or pulled.
-/
structure ChannelInteraction (channel : Channel F Message) where
  direction : Direction
  mult : Expression F
  msg : Message (Expression F)

structure AbstractInteraction (F : Type) where
  channel : RawChannel F
  direction : Direction
  mult : Expression F
  msg : Vector (Expression F) channel.arity

instance [Repr F] : Repr (AbstractInteraction F) where
  reprPrec i _ :=
    "(Interaction channel=" ++ i.channel.name ++ ", direction=" ++ i.direction.name ++
    ", mult=" ++ repr i.mult ++ ", msg=" ++ repr i.msg ++ ")"

variable {channel : Channel F Message}

/-- Pull a message once. -/
def pulled {channel : Channel F Message} (msg : Message (Expression F)) : ChannelInteraction channel :=
  { direction := .pull, mult := 1, msg }

/-- Conditional pull. When `enabled = 1`, this is a pull; when `enabled = 0`, it is disabled. -/
def pulledIf {channel : Channel F Message} (enabled : Expression F) (msg : Message (Expression F)) :
    ChannelInteraction channel :=
  { direction := .pull, mult := enabled, msg }

/-- Push a message once. -/
def pushed {channel : Channel F Message} (msg : Message (Expression F)) : ChannelInteraction channel :=
  { direction := .push, mult := 1, msg }

/-- Conditional push. When `enabled = 1`, this is a push; when `enabled = 0`, it is disabled. -/
def pushedIf {channel : Channel F Message} (enabled : Expression F) (msg : Message (Expression F)) :
    ChannelInteraction channel :=
  { direction := .push, mult := enabled, msg }

/-- Push a message `mult` times. -/
def emitted {channel : Channel F Message} (mult : Expression F) (msg : Message (Expression F)) :
    ChannelInteraction channel :=
  { direction := .push, mult, msg }

omit [FiniteField F] in @[circuit_norm]
lemma emitted_def (mult : Expression F) (msg : Message (Expression F)) :
  ({ direction := .push, mult, msg } : ChannelInteraction channel) = emitted mult msg := rfl
omit [FiniteField F] in @[circuit_norm]
lemma pulledIf_def (enabled : Expression F) (msg : Message (Expression F)) :
  ({ direction := .pull, mult := enabled, msg } : ChannelInteraction channel) =
    pulledIf enabled msg := rfl
omit [FiniteField F] in @[circuit_norm]
lemma emitted_direction (mult : Expression F) (msg : Message (Expression F)) :
  (emitted mult msg : ChannelInteraction channel).direction = .push := rfl
omit [FiniteField F] in @[circuit_norm]
lemma emitted_mult (mult : Expression F) (msg : Message (Expression F)) :
  (emitted mult msg : ChannelInteraction channel).mult = mult := rfl
omit [FiniteField F] in @[circuit_norm]
lemma emitted_msg (mult : Expression F) (msg : Message (Expression F)) :
  (emitted mult msg : ChannelInteraction channel).msg = msg := rfl
@[circuit_norm]
lemma pulledIf_one_eq_pulled (msg : Message (Expression F)) :
  (pulledIf 1 msg : ChannelInteraction channel) = pulled msg := rfl
@[circuit_norm]
lemma pushedIf_one_eq_pushed (msg : Message (Expression F)) :
  (pushedIf 1 msg : ChannelInteraction channel) = pushed msg := rfl

@[circuit_norm] lemma pulled_direction (msg : Message (Expression F)) :
  (pulled msg : ChannelInteraction channel).direction = .pull := rfl
@[circuit_norm] lemma pulled_mult (msg : Message (Expression F)) :
  (pulled msg : ChannelInteraction channel).mult = 1 := rfl
@[circuit_norm] lemma pulled_msg (msg : Message (Expression F)) :
  (pulled msg : ChannelInteraction channel).msg = msg := rfl
omit [FiniteField F] in @[circuit_norm]
lemma pulledIf_direction (enabled : Expression F) (msg : Message (Expression F)) :
  (pulledIf enabled msg : ChannelInteraction channel).direction = .pull := rfl
omit [FiniteField F] in @[circuit_norm]
lemma pulledIf_mult (enabled : Expression F) (msg : Message (Expression F)) :
  (pulledIf enabled msg : ChannelInteraction channel).mult = enabled := rfl
omit [FiniteField F] in @[circuit_norm]
lemma pulledIf_msg (enabled : Expression F) (msg : Message (Expression F)) :
  (pulledIf enabled msg : ChannelInteraction channel).msg = msg := rfl
@[circuit_norm] lemma pushed_direction (msg : Message (Expression F)) :
  (pushed msg : ChannelInteraction channel).direction = .push := rfl
@[circuit_norm] lemma pushed_mult (msg : Message (Expression F)) :
  (pushed msg : ChannelInteraction channel).mult = 1 := rfl
@[circuit_norm] lemma pushed_msg (msg : Message (Expression F)) :
  (pushed msg : ChannelInteraction channel).msg = msg := rfl
omit [FiniteField F] in @[circuit_norm]
lemma pushedIf_direction (enabled : Expression F) (msg : Message (Expression F)) :
  (pushedIf enabled msg : ChannelInteraction channel).direction = .push := rfl
omit [FiniteField F] in @[circuit_norm]
lemma pushedIf_mult (enabled : Expression F) (msg : Message (Expression F)) :
  (pushedIf enabled msg : ChannelInteraction channel).mult = enabled := rfl
omit [FiniteField F] in @[circuit_norm]
lemma pushedIf_msg (enabled : Expression F) (msg : Message (Expression F)) :
  (pushedIf enabled msg : ChannelInteraction channel).msg = msg := rfl

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
-- The result type contains the raw channel produced by `Channel.toRaw`.
@[implicit_reducible]
def toRaw (i : ChannelInteraction channel) : AbstractInteraction F :=
  ⟨ channel.toRaw, i.direction, i.mult, toElements i.msg ⟩

@[circuit_norm] lemma toRaw_channel (i : ChannelInteraction channel) :
  i.toRaw.channel = channel.toRaw := rfl
@[circuit_norm] lemma toRaw_direction (i : ChannelInteraction channel) :
  i.toRaw.direction = i.direction := rfl
@[circuit_norm] lemma toRaw_mult (i : ChannelInteraction channel) :
  i.toRaw.mult = i.mult := rfl
@[circuit_norm] lemma toRaw_msg (i : ChannelInteraction channel) :
    i.toRaw.msg = toElements i.msg := rfl

@[circuit_norm]
def Guarantees (i : ChannelInteraction channel) (env : Environment F) : Prop :=
  i.direction = .pull → Expression.eval env i.mult = 1 →
    channel.Guarantees (eval env i.msg) env.data

@[circuit_norm]
def Requirements (i : ChannelInteraction channel) (env : Environment F) : Prop :=
  i.direction.Requirements (Expression.eval env i.mult) (channel.Guarantees (eval env i.msg) env.data)
end ChannelInteraction

namespace AbstractInteraction
/-- Only pulls get guarantees. -/
def Guarantees (i : AbstractInteraction F) (env : Environment F) : Prop :=
  i.direction = .pull → i.channel.Guarantees (env i.mult) (i.msg.map env) env.data

def Requirements (i : AbstractInteraction F) (env : Environment F) : Prop :=
  i.channel.Requirements i.direction (env i.mult) (i.msg.map env) env.data
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

@[circuit_norm]
lemma channelInteraction_toRaw_inj {i j : ChannelInteraction channel} :
    i.toRaw = j.toRaw ↔ i = j := by
  constructor; swap
  · rintro rfl; rfl
  intro h
  rcases i with ⟨ direction, mult, msg ⟩
  rcases j with ⟨ direction', mult', msg' ⟩
  simp only [ChannelInteraction.toRaw, AbstractInteraction.mk.injEq,
    ChannelInteraction.mk.injEq, true_and] at h ⊢
  rcases h with ⟨ h_direction, h_mult, h_msg ⟩
  refine ⟨ h_direction, h_mult, ?_ ⟩
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
  direction : Direction
  mult : F
  msg : Array F
  same_size : msg.size = channel.arity

namespace Interaction
def msgVector (i : Interaction F) : Vector F i.channel.arity :=
  ⟨ i.msg, i.same_size ⟩

/-- Only pulls get guarantees. -/
def Guarantees (i : Interaction F) (data : ProverData F) : Prop :=
  i.direction = .pull → i.channel.Guarantees i.mult i.msgVector data

def Requirements (i : Interaction F) (data : ProverData F) : Prop :=
  i.channel.Requirements i.direction i.mult i.msgVector data
end Interaction

namespace AbstractInteraction
def eval (env : Environment F) (i : AbstractInteraction F) : Interaction F where
  channel := i.channel
  direction := i.direction
  mult := env i.mult
  msg := (i.msg.map env).toArray
  same_size := by simp

@[circuit_norm]
lemma eval_channel {i : AbstractInteraction F} {env : Environment F} :
  (i.eval env).channel = i.channel := rfl

@[circuit_norm]
lemma eval_direction {i : AbstractInteraction F} {env : Environment F} :
  (i.eval env).direction = i.direction := rfl

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
  direction := .pull
  mult := 1
  msg := (toElements msg).toArray
  same_size := by simp [Channel.toRaw]

@[circuit_norm]
def pushedValue (channel : Channel F Message) (msg : Message F) : Interaction F where
  channel := channel.toRaw
  direction := .push
  mult := 1
  msg := (toElements msg).toArray
  same_size := by simp [Channel.toRaw]

@[circuit_norm]
def pulledIfValue (channel : Channel F Message) (enabled : F) (msg : Message F) : Interaction F where
  channel := channel.toRaw
  direction := .pull
  mult := enabled
  msg := (toElements msg).toArray
  same_size := by simp [Channel.toRaw]

@[circuit_norm]
def pushedIfValue (channel : Channel F Message) (enabled : F) (msg : Message F) : Interaction F where
  channel := channel.toRaw
  direction := .push
  mult := enabled
  msg := (toElements msg).toArray
  same_size := by simp [Channel.toRaw]

lemma pulledIfValue_requirements_of_isBool_enabled {channel : Channel F Message}
  {enabled : F} {msg : Message F} {data : ProverData F} :
    enabled = 0 ∨ enabled = 1 →
    (channel.pulledIfValue enabled msg).Requirements data := by
  simp only [Interaction.Requirements, Channel.pulledIfValue, Channel.toRaw,
    Direction.pull_requirements]
  exact id

lemma pushedIfValue_guarantees {channel : Channel F Message}
  {enabled : F} {msg : Message F} {data : ProverData F} :
    (channel.pushedIfValue enabled msg).Guarantees data := by
  simp [Interaction.Guarantees, Channel.pushedIfValue, Channel.toRaw]

lemma eval_pulled {channel : Channel F Message} {msg : Message (Expression F)} {env : Environment F} :
     (channel.pulled msg).toRaw.eval env = channel.pulledValue (eval env msg) := by
  simp only [circuit_norm, AbstractInteraction.eval, Interaction.mk.injEq]
  simp only [true_and]
  apply congrArg Vector.toArray
  rw [←ProvableType.fromElements_eq_iff, CircuitType.eval_var]
  rfl

lemma eval_pushed {channel : Channel F Message} {msg : Message (Expression F)} {env : Environment F} :
     (channel.pushed msg).toRaw.eval env = channel.pushedValue (eval env msg) := by
  simp only [circuit_norm, AbstractInteraction.eval, Interaction.mk.injEq]
  simp only [true_and]
  apply congrArg Vector.toArray
  rw [←ProvableType.fromElements_eq_iff, CircuitType.eval_var]
  rfl

lemma eval_pulledIf {channel : Channel F Message} {enabled : Expression F}
    {msg : Message (Expression F)} {env : Environment F} :
     (channel.pulledIf enabled msg).toRaw.eval env = channel.pulledIfValue (eval env enabled) (eval env msg) := by
  simp only [circuit_norm, AbstractInteraction.eval, Interaction.mk.injEq]
  simp only [true_and]
  apply congrArg Vector.toArray
  rw [←ProvableType.fromElements_eq_iff, CircuitType.eval_var]
  rfl

lemma eval_pushedIf {channel : Channel F Message} {enabled : Expression F}
    {msg : Message (Expression F)} {env : Environment F} :
     (channel.pushedIf enabled msg).toRaw.eval env = channel.pushedIfValue (eval env enabled) (eval env msg) := by
  simp only [circuit_norm, AbstractInteraction.eval, Interaction.mk.injEq]
  simp only [true_and]
  apply congrArg Vector.toArray
  rw [←ProvableType.fromElements_eq_iff, CircuitType.eval_var]
  rfl
lemma eval_toRaw_pulledIf (channel : Channel F Message) (enabled : Expression F)
    (msg : Message (Expression F)) (env : Environment F) :
    (_root_.pulledIf (channel := channel) enabled msg).toRaw.eval env =
      channel.pulledIfValue (Expression.eval env enabled) (eval env msg) :=
  (eval_pulledIf (channel := channel)).trans (by rw [ProvableType.eval_field])

lemma eval_toRaw_pushedIf (channel : Channel F Message) (enabled : Expression F)
    (msg : Message (Expression F)) (env : Environment F) :
    (_root_.pushedIf (channel := channel) enabled msg).toRaw.eval env =
      channel.pushedIfValue (Expression.eval env enabled) (eval env msg) :=
  (eval_pushedIf (channel := channel)).trans (by rw [ProvableType.eval_field])
end Channel
