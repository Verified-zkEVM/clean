import Clean.Circuit.Expression
import Clean.Circuit.Provable
import Clean.Circuit.SimpGadget
import Mathlib.Data.Finsupp.Defs

variable {F : Type} [Field F] {α : Type} {n : ℕ}
variable {Message : TypeMap} [ProvableType Message]

/--
A named array of field elements, used for multiset add operations.
-/
abbrev NamedArray (F : Type) := String × Array F

def Environment.rawInteractions (env : Environment F) (channelName : String) (n : ℕ) :
    List (F × Vector F n) :=
  env.interactions.filterMap fun (name, mult, elts) =>
    if h : name = channelName ∧ elts.size = n then some (mult, ⟨ elts, h.2 ⟩ ) else none

namespace NamedArray
variable [Field F]

/-- Evaluate a NamedArray of expressions to a NamedArray of field elements -/
def eval (env : Environment F) (nl : NamedArray (Expression F)) : NamedArray F :=
  (nl.1, nl.2.map (Expression.eval env))

def IsAdded (env : Environment F) (nl : NamedArray (Expression F)) (mult : Expression F) : Prop :=
  let n := nl.2.size
  let interactions := env.rawInteractions nl.1 n
  let element : Vector F n := ⟨ nl.2.map env, Array.size_map .. ⟩
  (env mult, element) ∈ interactions
end NamedArray

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

structure ChannelInteraction (F : Type) (Message : TypeMap) [ProvableType Message] where
  channel : Channel F Message
  mult : Expression F
  msg : Message (Expression F)
  assumeGuarantees : Bool

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

def AbstractInteraction.eval (env : Environment F) (i : AbstractInteraction F) :
    RawInteraction F :=
  (i.channel.name,env i.mult, (i.msg.map env).toArray)

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

def ChannelInteraction.toRaw : ChannelInteraction F Message → AbstractInteraction F
  | { channel, mult, msg, assumeGuarantees } => ⟨ channel.toRaw, mult, toElements msg, assumeGuarantees ⟩

omit [Field F] in
@[circuit_norm]
lemma ChannelInteraction.toRaw_channel (i : ChannelInteraction F Message) :
    i.toRaw.channel = i.channel.toRaw := rfl
omit [Field F] in
@[circuit_norm]
lemma ChannelInteraction.toRaw_mult (i : ChannelInteraction F Message) :
    i.toRaw.mult = i.mult := rfl
omit [Field F] in
@[circuit_norm]
lemma ChannelInteraction.toRaw_msg (i : ChannelInteraction F Message) :
    i.toRaw.msg = toElements i.msg := rfl
omit [Field F] in
@[circuit_norm]
lemma ChannelInteraction.toRaw_assumeGuarantees (i : ChannelInteraction F Message) :
    i.toRaw.assumeGuarantees = i.assumeGuarantees := rfl

def Channel.interactions (env : Environment F) (channel : Channel F Message) :
    List (F × Message F) :=
  env.rawInteractions channel.name (size Message)
  |>.map fun (mult, elts) => (mult, fromElements elts)

@[circuit_norm]
def ChannelInteraction.IsAdded (i : ChannelInteraction F Message) (env : Environment F) : Prop :=
  (env i.mult, eval env i.msg) ∈ i.channel.interactions env

def AbstractInteraction.IsAdded (i : AbstractInteraction F) (env : Environment F) : Prop :=
  let n := i.channel.arity
  (env i.mult, i.msg.map env) ∈ env.rawInteractions i.channel.name n

@[circuit_norm]
lemma AbstractInteraction.isAdded_def (env : Environment F) (int : ChannelInteraction F Message) :
    int.toRaw.IsAdded env ↔ int.IsAdded env := by
  rcases int with ⟨channel, mult, msg, assumeGuarantees ⟩
  simp only [circuit_norm, AbstractInteraction.IsAdded, ChannelInteraction.IsAdded,
    ChannelInteraction.toRaw, Channel.interactions,
    List.mem_map, Prod.mk.injEq, Prod.exists, ↓existsAndEq, true_and]
  constructor
  · intro h_mem
    exact ⟨ _, h_mem, rfl ⟩
  · intro ⟨ b, h_mem, h_eq ⟩
    replace h_eq := congrArg toElements h_eq
    simp only [ProvableType.eval, ProvableType.toElements_fromElements] at h_eq
    subst h_eq
    exact h_mem

def RawChannel.filter (channel : RawChannel F) (is : RawInteractions F) :
    List (F × Vector F channel.arity) :=
  is.filterMap fun ⟨ name, mult, elts ⟩ =>
    if h : name = channel.name ∧ elts.size = channel.arity
      then some (mult, ⟨ elts, h.2 ⟩)
      else none

def Channel.filter (channel : Channel F Message) (is : RawInteractions F) :
    List (F × Message F) :=
  channel.toRaw.filter is
  |>.map fun (mult, elts) => (mult, fromElements elts)

-- normalize to Channel.filter
-- TODO this is not picked up by simp
omit [Field F] in
@[circuit_norm]
lemma RawChannel.filter_eq (channel : Channel F Message) (is : RawInteractions F) :
  (channel.toRaw.filter is).map Channel.interactionFromRaw = channel.filter is := rfl

@[circuit_norm]
lemma Channel.filter_self (channel : Channel F Message) (env : Environment F)
  (mult : Expression F) (msg : Message (Expression F)) (assumeGuarantees : Bool) (is : RawInteractions F) :
    let interaction : ChannelInteraction F Message := { channel, mult, msg, assumeGuarantees };
    channel.toRaw.filter ((AbstractInteraction.eval env interaction.toRaw) :: is) =
      (env mult, (toElements msg).map env) :: channel.toRaw.filter is := by
    simp only [RawChannel.filter, AbstractInteraction.eval, ChannelInteraction.toRaw, Channel.toRaw,
      List.filterMap_cons, Vector.toArray_map, Array.size_map, Vector.size_toArray,
      and_self, ↓reduceDIte]
    congr 1

@[circuit_norm]
lemma Channel.interactionFromRaw_eq (env : Environment F)
  (mult : F) (msg : Message (Expression F)) :
    Channel.interactionFromRaw (mult, (toElements msg).map env) = (mult, eval env msg) := by
  rfl

variable {Message' : TypeMap} [ProvableType Message']

@[circuit_norm]
lemma Channel.filter_other (channel : Channel F Message) (channel' : Channel F Message') (env : Environment F)
  (mult : Expression F) (msg : Message' (Expression F)) (assumeGuarantees : Bool) (is : RawInteractions F) :
    let interaction : ChannelInteraction F Message' := { channel := channel', mult, msg, assumeGuarantees };
    channel.toRaw.filter (AbstractInteraction.eval env interaction.toRaw :: is) =
      if h : channel'.name = channel.name ∧ size Message' = size Message
      then ((env mult, (toElements msg).map env |>.cast h.2) :: channel.toRaw.filter is)
      else channel.toRaw.filter is := by
    sorry

@[circuit_norm]
def ChannelInteraction.Guarantees (i : ChannelInteraction F Message) (env : Environment F) : Prop :=
  i.channel.Guarantees (env i.mult) (eval env i.msg) env.data

def AbstractInteraction.Guarantees (i : AbstractInteraction F) (env : Environment F) : Prop :=
  i.channel.Guarantees (env i.mult) (i.msg.map env) env.data

@[circuit_norm]
lemma AbstractInteraction.guarantees_def (env : Environment F) (int : ChannelInteraction F Message) :
    int.toRaw.Guarantees env ↔ int.Guarantees env := by
  rfl

@[circuit_norm]
def ChannelInteraction.Requirements (i : ChannelInteraction F Message) (env : Environment F) : Prop :=
  i.channel.Requirements (env i.mult) (eval env i.msg) env.data

def AbstractInteraction.Requirements (i : AbstractInteraction F) (env : Environment F) : Prop :=
  i.channel.Requirements (env i.mult) (i.msg.map env) env.data

@[circuit_norm]
lemma AbstractInteraction.requirements_def (env : Environment F) (int : ChannelInteraction F Message) :
    int.toRaw.Requirements env ↔ int.Requirements env := by
  rfl

/--
An `InteractionDelta` represents a change to an interaction (multiset argument), as a list
of (NamedList, multiplicity) pairs. This representation is computable and supports efficient
addition via list concatenation. Two deltas are semantically equal if they have the same
total multiplicity for each key (checked via `toFinsupp` in proofs).

Note: Multiplicities are in `F` (the field) rather than `ℤ` because the `enabled` flag used
in conditional emission (e.g., `emitStateWhen enabled mult state`) is a field element.
Using `F` avoids ambiguity in converting `F → ℤ` and allows direct multiplication
`enabled * mult` without coercion issues.
-/
abbrev InteractionDelta (F : Type) := RawInteractions F

@[circuit_norm]
lemma NamedArray.isAdded_def (channel : Channel F Message) (env : Environment F)
  (msg : Message (Expression F)) (mult : Expression F) :
    NamedArray.IsAdded env (channel.name, (toElements msg).toArray) mult ↔
    (env mult, ProvableType.eval env msg) ∈ channel.interactions env := by
  -- TODO this proof is much more annoying that I expected
  -- TODO I think the Array / Vector mismatch makes it much harder
  simp only [NamedArray.IsAdded, Channel.interactions, circuit_norm]
  have h_size : (toElements msg).toArray.size = size Message := by simp
  simp only [List.mem_map]
  set v1 : Vector F _ := ⟨ Array.map (fun x ↦ Expression.eval env x) (toElements msg).toArray, _ ⟩
  set v1' : Vector F (size Message) := (toElements msg).map env
  have h_v1 : v1 = v1'.cast h_size.symm := by
    simp only [Vector.mk_eq, Vector.toArray_cast, Vector.toArray_map, v1, v1']
  have h_channels : env.rawInteractions channel.name (toElements msg).toArray.size =
      List.map (fun t => (t.1, t.2.cast h_size.symm)) (env.rawInteractions channel.name (size Message)) := by
    apply List.ext_getElem
    · simp only [List.length_map]; congr
    · simp only [List.length_map, List.getElem_map]
      intro i h_i h_i'
      rw [Prod.mk.injEq]
      constructor
      · congr!
      · rw [Vector.cast, Vector.eq_mk]
        congr!
  rw [h_v1, h_channels, List.mem_map]
  simp only [Prod.mk.injEq, Vector.cast_eq_cast, Vector.cast_rfl]
  constructor
  · intro ⟨ a, h_mem, h_eq1, h_eq2 ⟩
    use a, h_mem, h_eq1
    rw [h_eq2]
    rfl
  · intro ⟨ a, h_mem, h_eq1, h_eq2 ⟩
    use a, h_mem, h_eq1
    have h_eq2' := congrArg toElements h_eq2
    simp only [ProvableType.eval, ProvableType.toElements_fromElements] at h_eq2'
    exact h_eq2'

namespace InteractionDelta
variable {F : Type}

instance : Zero (InteractionDelta F) := ⟨[]⟩

instance : Inhabited (InteractionDelta F) := ⟨0⟩

/-- Create a singleton interaction delta with one named list and its multiplicity -/
def single (nl : RawInteraction F) : InteractionDelta F := [nl]

/-- Addition is list concatenation - semantic equality handles combining multiplicities -/
instance : Add (InteractionDelta F) := ⟨List.append⟩

/-- Negation: negate all multiplicities -/
def neg [Neg F] (d : InteractionDelta F) : InteractionDelta F :=
  d.map (fun (name, mult, msg) => (name, -mult, msg))

instance [Neg F] : Neg (InteractionDelta F) := ⟨neg⟩

variable [Field F]

/-- Get the total multiplicity for a key by summing all entries -/
def getMultiplicity [DecidableEq F] (nl : NamedArray F) (d : InteractionDelta F) : F :=
  d.foldl (fun acc (s, m, v) => if (s, v) = nl then acc + m else acc) 0

/-- Convert to Finsupp for proofs (noncomputable) -/
noncomputable def toFinsupp [DecidableEq F] (d : InteractionDelta F) : Finsupp (NamedArray F) F :=
  d.foldl (fun acc (s, m, v) => acc + Finsupp.single (s, v) m) 0

omit [Field F] in
@[circuit_norm] theorem append_eq_add (d1 d2 : InteractionDelta F) : d1 ++ d2 = d1 + d2 := rfl

omit [Field F] in
theorem add_eq_append (d1 d2 : InteractionDelta F) : d1 + d2 = d1 ++ d2 := rfl

omit [Field F] in
@[circuit_norm] theorem nil_eq_zero : [] = (0 : InteractionDelta F) := rfl

omit [Field F] in
theorem zero_eq_nil : (0 : InteractionDelta F) = [] := rfl

omit [Field F] in
theorem add_zero' (d : InteractionDelta F) : d + 0 = d := List.append_nil d

omit [Field F] in
theorem zero_add' (d : InteractionDelta F) : 0 + d = d := List.nil_append d

omit [Field F] in
theorem add_assoc' (d1 d2 d3 : InteractionDelta F) : d1 + d2 + d3 = d1 + (d2 + d3) :=
  List.append_assoc d1 d2 d3

/-- AddMonoid instance for InteractionDelta.
    Note: Addition is list concatenation, so commutativity only holds semantically
    (same result via toFinsupp), not definitionally. -/
instance instAddMonoid : AddMonoid (InteractionDelta F) where
  add := (· + ·)
  add_assoc := add_assoc'
  zero := 0
  zero_add := zero_add'
  add_zero := add_zero'
  nsmul := nsmulRec

-- Semantic equality: two deltas are equal if they have the same toFinsupp
theorem toFinsupp_add [DecidableEq F] (d1 d2 : InteractionDelta F) :
    (d1 + d2).toFinsupp = d1.toFinsupp + d2.toFinsupp := by
  simp only [toFinsupp, add_eq_append]
  have h : ∀ (init : Finsupp (NamedArray F) F) (l : InteractionDelta F),
      List.foldl (fun acc x => acc + Finsupp.single (x.1, x.2.2) x.2.1) init l =
      init + List.foldl (fun acc x => acc + Finsupp.single (x.1, x.2.2) x.2.1) 0 l := by
    intro init l
    induction l generalizing init with
    | nil => simp
    | cons hd' tl' ih' =>
      simp only [List.foldl_cons]
      rw [ih' (init + Finsupp.single _ _), ih' (0 + Finsupp.single _ _)]
      simp only [zero_add]
      rw [add_assoc]
  induction d1 with
  | nil => simp [List.foldl_nil]
  | cons hd tl ih =>
    simp only [List.cons_append, List.foldl_cons]
    rw [h (0 + Finsupp.single _ _) (tl ++ d2)]
    simp only [zero_add]
    rw [ih]
    rw [h (Finsupp.single (hd.1, hd.2.2) hd.2.1) tl]
    rw [add_assoc]

theorem toFinsupp_single [DecidableEq F] (nl : NamedArray F) (m : F) :
    (single (nl.1, m, nl.2)).toFinsupp = Finsupp.single nl m := by
  simp only [single, toFinsupp, List.foldl_cons, List.foldl_nil, zero_add]

theorem toFinsupp_zero [DecidableEq F] : toFinsupp (0 : InteractionDelta F) = 0 := by
  simp only [←nil_eq_zero, toFinsupp, List.foldl_nil]

theorem toFinsupp_zero_mult [DecidableEq F] (nl1 nl2 : NamedArray F) :
    toFinsupp ([(nl1.1, 0, nl1.2), (nl2.1, 0, nl2.2)] : InteractionDelta F) = 0 := by
  simp only [toFinsupp, List.foldl_cons, List.foldl_nil, Finsupp.single_zero, add_zero]

/-- Helper lemma: equality of InteractionDeltas implies equality of their toFinsupp. -/
theorem toFinsupp_eq_of_eq [DecidableEq F] {a b : InteractionDelta F} (h : a = b) :
    a.toFinsupp = b.toFinsupp := by rw [h]

/-- Helper lemma: if localAdds = 0, then toFinsupp of localAdds = toFinsupp 0. -/
@[circuit_norm]
theorem toFinsupp_zero_of_eq_zero [DecidableEq F] {a : InteractionDelta F} (h : a = 0) :
    a.toFinsupp = (0 : InteractionDelta F).toFinsupp := by rw [h]

/-- Relates a foldl over List.finRange to a Finset.sum at the toFinsupp level.
    This is useful for proving localAdds_eq when localAdds is defined using foldl. -/
theorem toFinsupp_foldl_finRange [DecidableEq F] {n : ℕ} (f : Fin n → InteractionDelta F) :
    ((List.finRange n).foldl (fun acc i => acc + f i) 0).toFinsupp =
    ∑ i : Fin n, (f i).toFinsupp := by
  induction n with
  | zero =>
    simp only [List.finRange_zero, List.foldl_nil, Finset.univ_eq_empty, Finset.sum_empty]
    rfl
  | succ n ih =>
    -- Use the _last variant: finRange (n+1) = map castSucc (finRange n) ++ [last n]
    rw [List.finRange_succ_last, List.foldl_append, List.foldl_map, List.foldl_cons, List.foldl_nil]
    -- Show that foldl.toFinsupp = sum for the first n elements
    have ih' : ((List.finRange n).foldl (fun acc i => acc + f (Fin.castSucc i)) 0).toFinsupp =
        ∑ i : Fin n, (f (Fin.castSucc i)).toFinsupp := by
      have := ih (f ∘ Fin.castSucc)
      simp only [Function.comp_def] at this
      exact this
    rw [toFinsupp_add, ih', Fin.sum_univ_castSucc]

@[circuit_norm]
lemma flatMap_eq_map {α β : Type} {f : α → RawInteraction β} {l : List α} :
    l.flatMap (fun x ↦ InteractionDelta.single (f x)) = l.map f := by
  simp only [InteractionDelta.single, ← List.map_eq_flatMap]

end InteractionDelta

noncomputable abbrev RawInteractions.toFinsupp [DecidableEq F] (d : RawInteractions F) : Finsupp (NamedArray F) F :=
  InteractionDelta.toFinsupp d

/-- normal form for channel interactions -/
def Channel.emitted (chan : Channel F Message) (mult : F) (msg : Message F) :=
  InteractionDelta.single (chan.name, mult, (toElements msg).toArray)

/-- convenient way to specify channel interaction with multiplicity -1 -/
def Channel.pulled (chan : Channel F Message) (msg : Message F) :=
  InteractionDelta.single (chan.name, -1, (toElements msg).toArray)

/-- convenient way to specify channel interaction with multiplicity 1 -/
def Channel.pushed (chan : Channel F Message) (msg : Message F) :=
  InteractionDelta.single (chan.name, 1, (toElements msg).toArray)

@[circuit_norm]
lemma Channel.pulled_def (chan : Channel F Message) (msg : Message F) :
    chan.pulled msg = chan.emitted (-1) msg  := rfl

@[circuit_norm]
lemma Channel.pushed_def (chan : Channel F Message) (msg : Message F) :
    chan.pushed msg = chan.emitted 1 msg := rfl

@[circuit_norm]
lemma InteractionDelta.single_eq_channel_emitted (channel : Channel F Message) (mult : Expression F)
    (msg : Message (Expression F)) (assumeGuarantees : Bool) (env : Environment F) :
    let interaction : ChannelInteraction F Message := { channel, mult, msg, assumeGuarantees }
    .single (interaction.toRaw.eval env) = channel.emitted (mult.eval env) (eval env msg) := by
  simp only [Channel.emitted, AbstractInteraction.eval, InteractionDelta.single, ChannelInteraction.toRaw, eval,
    ProvableType.toElements_fromElements]
  rfl

omit [Field F] in
lemma Channel.filter_self_single (channel : Channel F Message)
  (mult : F) (msg : Message F) :
    channel.toRaw.filter (channel.emitted mult msg) = [(mult, toElements msg)] := by
  simp [Channel.emitted, InteractionDelta.single, Channel.toRaw, RawChannel.filter]

omit [Field F] in
lemma Channel.filter_self_add (channel : Channel F Message)
  (mult : F) (msg : Message F) (is : RawInteractions F) :
    channel.toRaw.filter (channel.emitted mult msg + is) = (mult, toElements msg) :: channel.toRaw.filter is := by
  simp [Channel.emitted, InteractionDelta.single, InteractionDelta.add_eq_append, Channel.toRaw, RawChannel.filter]

omit [Field F] in
@[circuit_norm]
lemma RawChannel.filter_zero (channel : Channel F Message) :
  (channel.toRaw.filter 0).map Channel.interactionFromRaw = [] := rfl

omit [Field F] in
@[circuit_norm]
lemma Channel.filter_zero (channel : Channel F Message) :
  channel.filter 0 = [] := rfl

-- abstract theory of channel consistency

namespace Channel

-- we assume some initial channel interactions (for modelling lookup tables)
variable (initial : List (F × Message F))
-- we have some global property about the initial interactions and all interactions of a channel
variable (GlobalProp : List (F × Message F) → List (F × Message F) → ProverData F → Prop)
-- also, there are some abstract "local" properties, "constraints" and "spec", that may depend on local interactions
variable (LocalConstraints LocalSpec : List (F × Message F) → ProverData F → Prop)

-- requirements / guarantees are meant to be called on a current interaction.
-- this naturally defines what it means for them to be satisfied on a given list of interactions.

def RequirementsSatisfied (channel : Channel F Message) (data : ProverData F) (ins : List (F × Message F)) : Prop :=
  ins.Forall fun (mult, msg) => channel.Requirements mult msg data

def GuaranteesSatisfied (channel : Channel F Message) (data : ProverData F) (ins : List (F × Message F)) : Prop :=
  ins.Forall fun (mult, msg) => channel.Guarantees mult msg data

/--
A channel is consistent (parametrized by the global property) if
- the requirements are satisfied on all the initial interactions
- all requirements taken together for a given channel interactions length imply all guarantees
 -/
def Consistent (channel : Channel F Message) (data : ProverData F) : Prop :=
  ∀ (ins : List (F × Message F)),
  GlobalProp initial (initial ++ ins) data →
    channel.RequirementsSatisfied data initial ∧
    (channel.RequirementsSatisfied data (initial ++ ins) → channel.GuaranteesSatisfied data (initial ++ ins))

/-- Let's assume that a circuit locally proves the following soundness theorem: -/
def LocalSoundness (channel : Channel F Message) (data : ProverData F) (localInteractions : List (F × Message F)) : Prop :=
    LocalConstraints localInteractions data →
    channel.GuaranteesSatisfied data localInteractions →
    LocalSpec localInteractions data ∧ channel.RequirementsSatisfied data localInteractions

/--
  Main result:
  Consistency + local soundness imply that the local soundness theorem holds in a
  stronger sense of not relying on the guarantees; and also, the guarantees actually hold.

  TODO: this doesn't work, we're missing several things, such as:
  - requirements/guarantees are monotone in the initial interactions
  - global prop is preserved when adding local interactions
  but I think the structure hints at a working argument, I'm going to revisit the abstract version
  after making it work in a concrete example.
  -/
def globalSoundness (channel : Channel F Message) (data : ProverData F) (ins : List (F × Message F)) :
  channel.Consistent initial GlobalProp data →
  channel.LocalSoundness LocalConstraints LocalSpec data ins →
  GlobalProp initial (initial ++ ins) data →
    -- guarantees actually hold
    channel.GuaranteesSatisfied data (initial ++ ins) ∧
    -- stronger local soundness
    (LocalConstraints ins data → LocalSpec ins data) := by
  intros h_consistent h_localSoundness h_globalProp
  simp only [Consistent, LocalSoundness] at h_consistent h_localSoundness
  specialize h_consistent ins h_globalProp
  -- it suffices to show that requirements hold
  suffices h_requirements : channel.RequirementsSatisfied data (initial ++ ins) by
    obtain ⟨ _, h_implies ⟩ := h_consistent
    have h_guarantees := h_implies h_requirements
    use h_guarantees
    intro h_localConstraints
    have : channel.GuaranteesSatisfied data ins := by simp_all [GuaranteesSatisfied]
    exact (h_localSoundness h_localConstraints this).1
  -- cyclic reasoning
  sorry

end Channel
