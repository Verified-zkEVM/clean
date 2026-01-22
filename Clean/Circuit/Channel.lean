import Clean.Circuit.Expression
import Clean.Circuit.Provable
import Clean.Circuit.SimpGadget
import Mathlib.Data.Finsupp.Defs

variable {F : Type} [Field F] {α : Type} {n : ℕ}
variable {Message : TypeMap} [ProvableType Message]

/--
A named list of field elements, used for multiset add operations.
-/
structure NamedList (F : Type) where
  name : String
  values : List F
deriving DecidableEq, Repr

def Environment.rawInteractions (env : Environment F) (channelName : String) (n : ℕ) :
    List (F × Vector F n) :=
  env.channelInteractions.filterMap fun (name, mult, elts) =>
    if name = channelName then some (mult, .ofArray n elts) else none

namespace NamedList
variable [Field F]

/-- Evaluate a NamedList of expressions to a NamedList of field elements -/
def eval (env : Environment F) (nl : NamedList (Expression F)) : NamedList F :=
  { name := nl.name, values := nl.values.map (Expression.eval env) }

def IsAdded (env : Environment F) (nl : NamedList (Expression F)) (mult : Expression F) : Prop :=
  let n := nl.values.length
  let interactions := env.rawInteractions nl.name n
  let element : Vector F n := ⟨ .mk (nl.values.map env), List.length_map .. ⟩
  (env mult, element) ∈ interactions
end NamedList

structure Channel (F : Type) (Message : TypeMap) [ProvableType Message] where
  name : String

  /-- the guarantees you get from adding an interaction to the channel, to be used locally in your soundness proof -/
  Guarantees (mult : F) (message : Message F)
    (interactions : List (F × Message F)) (data : ProverData F) : Prop

  /-- additional proof obligation from adding an interaction, to be _provided_ locally in your soundness proof.
    intuition: the `Guarantees` for multiplicity `-m` should follow from the `Requirements` for multiplicity `m`,
    so that pulling from the channel gives you a guarantee that is satisfied on the other side by the requirement for pushing
    the same element.
   -/
  Requirements (mult : F) (message : Message F)
    (interactions : List (F × Message F)) (data : ProverData F) : Prop

structure ChannelInteraction (F : Type) (Message : TypeMap) [ProvableType Message] where
  channel : Channel F Message
  mult : Expression F
  msg : Message (Expression F)

/-- `Channel` with type argument removed, to be used in the core framework. -/
structure RawChannel (F : Type) where
  name : String
  arity : ℕ
  Guarantees (mult : F) (message : Vector F arity) (interactions : List (F × Vector F arity))
    (data : ProverData F) : Prop
  Requirements (mult : F) (message : Vector F arity) (interactions : List (F × Vector F arity))
    (data : ProverData F) : Prop

structure RawInteraction (F : Type) where
  channel : RawChannel F
  mult : Expression F
  msg : Vector (Expression F) channel.arity

instance [Repr F] : Repr (RawInteraction F) where
  reprPrec i _ :=
    "(RawInteraction channel=" ++ i.channel.name ++
    ", mult=" ++ repr i.mult ++ ", msg=" ++ repr i.msg ++ ")"

def Channel.interactionToRaw (interaction : F × Message F) :
    F × Vector F (size Message) := (interaction.1, toElements interaction.2)

def Channel.interactionFromRaw (interaction : F × Vector F (size Message)) :
    F × Message F := (interaction.1, fromElements interaction.2)

/-- Convert a `Channel` to a `RawChannel` by removing the type argument -/
def Channel.toRaw (channel : Channel F Message) : RawChannel F where
  name := channel.name
  arity := size Message
  Guarantees mult message is data :=
    channel.Guarantees mult (fromElements message) (is.map interactionFromRaw) data
  Requirements mult message is data :=
    channel.Requirements mult (fromElements message) (is.map interactionFromRaw) data

def ChannelInteraction.toRaw : ChannelInteraction F Message → RawInteraction F
  | { channel, mult, msg } => ⟨ channel.toRaw, mult, toElements msg ⟩

def Channel.interactions (env : Environment F) (channel : Channel F Message) :
    List (F × Message F) :=
  env.rawInteractions channel.name (size Message)
  |>.map fun (mult, elts) => (mult, fromElements elts)

@[circuit_norm]
def ChannelInteraction.IsAdded (i : ChannelInteraction F Message) (env : Environment F) : Prop :=
  (env i.mult, eval env i.msg) ∈ i.channel.interactions env

def RawInteraction.IsAdded (i : RawInteraction F) (env : Environment F) : Prop :=
  let n := i.channel.arity
  (env i.mult, i.msg.map env) ∈ env.rawInteractions i.channel.name n

@[circuit_norm]
lemma RawInteraction.isAdded_def (env : Environment F) (int : ChannelInteraction F Message) :
    int.toRaw.IsAdded env ↔ int.IsAdded env := by
  rcases int with ⟨channel, mult, msg⟩
  simp only [circuit_norm, RawInteraction.IsAdded, ChannelInteraction.IsAdded,
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

@[circuit_norm]
def ChannelInteraction.Guarantees (i : ChannelInteraction F Message) (env : Environment F) : Prop :=
  i.channel.Guarantees (env i.mult) (eval env i.msg) (i.channel.interactions env) env.data

def RawInteraction.Guarantees (i : RawInteraction F) (env : Environment F) : Prop :=
  i.channel.Guarantees (env i.mult) (i.msg.map env) (env.rawInteractions i.channel.name i.channel.arity) env.data

@[circuit_norm]
lemma RawInteraction.guarantees_def (env : Environment F) (int : ChannelInteraction F Message) :
  int.toRaw.Guarantees env ↔ int.Guarantees env := by rfl

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
abbrev InteractionDelta (F : Type) := List (NamedList F × F)

@[circuit_norm]
lemma NamedList.isAdded_def (channel : Channel F Message) (env : Environment F)
  (msg : Message (Expression F)) (mult : Expression F) :
    NamedList.IsAdded env { name := channel.name, values := (toElements msg).toList } mult ↔
    (env mult, ProvableType.eval env msg) ∈ channel.interactions env := by
  -- TODO this proof is much more annoying that I expected
  -- TODO I think the List / Vector mismatch makes it much harder, remove that!
  simp only [NamedList.IsAdded, Channel.interactions, circuit_norm]
  have h_size : (toElements msg).toArray.size = size Message := by simp
  have h_size' : (toElements msg).toList.length = size Message := by simp
  simp only [List.mem_map]
  set v1 : Vector F _ := ⟨ .mk <| List.map (fun x ↦ Expression.eval env x) (toElements msg).toList, _ ⟩
  set v1' : Vector F (size Message) := (toElements msg).map env
  have h_v1 : v1 = v1'.cast h_size.symm := by
    simp only [Vector.mk_eq, Vector.toArray_cast, Vector.toArray_map, v1, v1']
    rw [←Array.toList_map]
    rfl
  have h_channels : env.rawInteractions channel.name (toElements msg).toList.length =
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
def single (nl : NamedList F) (mult : F) : InteractionDelta F :=
  [(nl, mult)]

/-- Addition is list concatenation - semantic equality handles combining multiplicities -/
instance : Add (InteractionDelta F) := ⟨List.append⟩

/-- Negation: negate all multiplicities -/
def neg [Neg F] (d : InteractionDelta F) : InteractionDelta F :=
  d.map (fun (nl, m) => (nl, -m))

instance [Neg F] : Neg (InteractionDelta F) := ⟨neg⟩

variable [Field F]

/-- Get the total multiplicity for a key by summing all entries -/
def getMultiplicity [DecidableEq F] (nl : NamedList F) (d : InteractionDelta F) : F :=
  d.foldl (fun acc (k, v) => if k = nl then acc + v else acc) 0

/-- Convert to Finsupp for proofs (noncomputable) -/
noncomputable def toFinsupp [DecidableEq F] (d : InteractionDelta F) : Finsupp (NamedList F) F :=
  d.foldl (fun acc (nl, m) => acc + Finsupp.single nl m) 0

omit [Field F] in
@[circuit_norm] theorem add_eq_append (d1 d2 : InteractionDelta F) : d1 + d2 = d1 ++ d2 := rfl

omit [Field F] in
@[circuit_norm] theorem zero_eq_nil : (0 : InteractionDelta F) = [] := rfl

omit [Field F] in
@[circuit_norm] theorem add_zero' (d : InteractionDelta F) : d + 0 = d := List.append_nil d

omit [Field F] in
@[circuit_norm] theorem zero_add' (d : InteractionDelta F) : 0 + d = d := List.nil_append d

omit [Field F] in
theorem add_assoc' (d1 d2 d3 : InteractionDelta F) : (d1 + d2) + d3 = d1 + (d2 + d3) :=
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

@[circuit_norm]
theorem single_zero (nl : NamedList F) : single nl 0 = [(nl, 0)] := rfl

-- Semantic equality: two deltas are equal if they have the same toFinsupp
theorem toFinsupp_add [DecidableEq F] (d1 d2 : InteractionDelta F) :
    (d1 + d2).toFinsupp = d1.toFinsupp + d2.toFinsupp := by
  simp only [toFinsupp, add_eq_append]
  have h : ∀ (init : Finsupp (NamedList F) F) (l : List (NamedList F × F)),
      List.foldl (fun acc x => acc + Finsupp.single x.1 x.2) init l =
      init + List.foldl (fun acc x => acc + Finsupp.single x.1 x.2) 0 l := by
    intro init l
    induction l generalizing init with
    | nil => simp
    | cons hd' tl' ih' =>
      simp only [List.foldl_cons]
      rw [ih' (init + Finsupp.single hd'.1 hd'.2), ih' (0 + Finsupp.single hd'.1 hd'.2)]
      simp only [zero_add]
      rw [add_assoc]
  induction d1 with
  | nil => simp [List.foldl_nil]
  | cons hd tl ih =>
    simp only [List.cons_append, List.foldl_cons]
    rw [h (0 + Finsupp.single hd.1 hd.2) (tl ++ d2)]
    simp only [zero_add]
    rw [ih]
    rw [h (Finsupp.single hd.1 hd.2) tl]
    rw [add_assoc]

theorem toFinsupp_single [DecidableEq F] (nl : NamedList F) (m : F) :
    (single nl m).toFinsupp = Finsupp.single nl m := by
  simp only [single, toFinsupp, List.foldl_cons, List.foldl_nil, zero_add]

theorem toFinsupp_zero [DecidableEq F] : toFinsupp (0 : InteractionDelta F) = 0 := by
  simp only [zero_eq_nil, toFinsupp, List.foldl_nil]

theorem toFinsupp_zero_mult [DecidableEq F] (nl1 nl2 : NamedList F) :
    toFinsupp ([(nl1, 0), (nl2, 0)] : InteractionDelta F) = 0 := by
  simp only [toFinsupp, List.foldl_cons, List.foldl_nil, Finsupp.single_zero, add_zero]

/-- Helper lemma: equality of InteractionDeltas implies equality of their toFinsupp. -/
theorem toFinsupp_eq_of_eq [DecidableEq F] {a b : InteractionDelta F} (h : a = b) :
    a.toFinsupp = b.toFinsupp := by rw [h]

/-- Helper lemma: if collectAdds = 0, then toFinsupp of collectAdds = toFinsupp 0. -/
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

end InteractionDelta

-- abstract theory of channel consistency

namespace Channel

-- we assume some initial channel interactions (for modelling lookup tables)
variable (initial : List (F × Message F))
-- we have some global property about the initial interactions and all interactions of a channel
variable (GlobalProp : List (F × Message F) → List (F × Message F) → ProverData F → Prop)
-- also, there are some abstract "local" properties, "constraints" and "spec", that may depend on local interactions
variable (LocalConstraints LocalSpec : List (F × Message F) → ProverData F → Prop)

-- requirements / guarantees are meant to be called on a current interaction
-- plus all previous interactions. this naturally defines what it means for them to be satisfied
-- on a given list of interactions.

def RequirementsSatisfied (channel : Channel F Message) (data : ProverData F) (initial : List (F × Message F)) :
    List (F × Message F) → Prop
  | [] => True
  | (mult, msg) :: interactions =>
    channel.Requirements mult msg initial data ∧
    channel.RequirementsSatisfied data initial interactions

def GuaranteesSatisfied (channel : Channel F Message) (data : ProverData F) (initial : List (F × Message F)) :
    List (F × Message F) → Prop
  | [] => True
  | (mult, msg) :: interactions =>
    channel.Guarantees mult msg initial data ∧
    channel.GuaranteesSatisfied data initial interactions

/--
A channel is consistent (parametrized by the global property) if
- the requirements are satisfied on all the initial interactions
- all requirements taken together for a given channel interactions length imply all guarantees
 -/
def Consistent (channel : Channel F Message) (data : ProverData F) : Prop :=
  ∀ (localInteractions globalInteractions : List (F × Message F)),
  GlobalProp initial (initial ++ globalInteractions ++ localInteractions) data →
    channel.RequirementsSatisfied data initial localInteractions ∧
    (channel.RequirementsSatisfied data (initial ++ globalInteractions) localInteractions →
    channel.GuaranteesSatisfied data (initial ++ globalInteractions) localInteractions)

/-- Let's assume that a circuit locally proves the following soundness theorem: -/
def LocalSoundness (channel : Channel F Message) (data : ProverData F) (localInteractions : List (F × Message F)) : Prop :=
  ∀ (globalInteractions : List (F × Message F)),
    LocalConstraints localInteractions data →
    channel.GuaranteesSatisfied data globalInteractions localInteractions →
    LocalSpec localInteractions data ∧ channel.RequirementsSatisfied data (globalInteractions ++ localInteractions) localInteractions

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
def globalSoundness (channel : Channel F Message) (data : ProverData F) (localInteractions : List (F × Message F)) :
  channel.Consistent initial GlobalProp data →
  channel.LocalSoundness LocalConstraints LocalSpec data localInteractions →
  ∀ (globalInteractions : List (F × Message F)),
    GlobalProp initial (initial ++ globalInteractions ++ localInteractions) data →
    -- guarantees actually hold
    channel.GuaranteesSatisfied data (initial ++ globalInteractions) localInteractions ∧
    -- stronger local soundness
    (LocalConstraints localInteractions data → LocalSpec localInteractions data) := by
  intros h_consistent h_localSoundness globalInteractions h_globalProp
  simp only [Consistent, LocalSoundness] at h_consistent h_localSoundness
  specialize h_consistent localInteractions globalInteractions h_globalProp
  specialize h_localSoundness (initial ++ globalInteractions)
  -- it suffices to show that requirements hold
  suffices h_requirements : channel.RequirementsSatisfied data (initial ++ globalInteractions) localInteractions by
    obtain ⟨ _, h_implies ⟩ := h_consistent
    have h_guarantees := h_implies h_requirements
    use h_guarantees
    intro h_localConstraints
    exact (h_localSoundness h_localConstraints h_guarantees).1
  -- let's do induction on the globalInteractions to show the requirements
  induction globalInteractions with
  | nil => simp_all only [List.append_nil]
  | cons hd tl ih =>

    sorry

end Channel
