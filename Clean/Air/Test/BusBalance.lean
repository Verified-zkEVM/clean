import Clean.Air.BalanceModel
import Clean.Circuit.Json
import Mathlib.Tactic.NormNum.Prime

/-!
# Bus balance acceptance tests

Evidence for the acceptance items of the bus-balance roadmap that are within reach of the
kernel and the balance models (A1–A6, A11, A13–A15, A17–A18), the legacy compatibility
fixtures, and the Layer 0 prototype: one typed message, a provider, a receive with an
assumption, a receive without an assumption, a gated event, and one ensemble whose statement
takes an explicit balance model. The Consistency section shows what a balance model does on
the channel encoding it reads, and what it does on the other one.

Two kinds of fixture are kept apart. An `example` whose type is `Prop` only checks that the
new API elaborates with explicit parameters; it proves nothing about satisfiability. Every
semantic claim in this file (what the legacy relation admits over `F 2`, what the local
contract rejects, what a model accepts, what a nested circuit collects) is a proved statement
or a `#guard`.
-/

namespace BusBalanceTests
open Air.Flat

instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-! ## Legacy compatibility fixtures (A11, A13) -/
section Legacy
variable {p : ℕ} [Fact p.Prime]

/-- A legacy channel with a nontrivial guarantee. -/
def LegacyChannel : Channel (F p) field where
  name := "legacy"
  Guarantees x _ := x = 7

/-- A legacy channel whose guarantee can never be established. -/
def NeverChannel : Channel (F p) field where
  name := "never"
  Guarantees _ _ := False

/-- A11: legacy `emit (-1)` neither assumes nor owes the guarantee, even a `False` one. -/
example (env : Environment (F p)) (msg : Expression (F p)) :
    ((NeverChannel (p := p)).emitted (-1) msg).Guarantees env ∧
    ((NeverChannel (p := p)).emitted (-1) msg).Requirements env := by
  simp [circuit_norm]

/-- A13: the two-premise requirement proof shape used downstream still typechecks. -/
example (env : Environment (F p)) (m msg : Expression (F p))
    (h : (LegacyChannel (p := p)).Guarantees (eval env msg) env.data) :
    ((LegacyChannel (p := p)).emitted m msg).Requirements env :=
  fun _ _ => h

/-- A13: `exists_push_of_pull` keeps its name and statement. -/
example {F : Type} [FiniteField F] [DecidableEq F] (interactions : List (Interaction F))
    (balance : BalancedInteractions interactions) :
    ∀ a ∈ interactions, a.mult = -1 →
      ∃ b ∈ interactions, b.msg = a.msg ∧ b.mult ≠ 0 ∧ b.mult ≠ -1 :=
  exists_push_of_pull interactions balance

/-- A13: `one_ne_neg_one` keeps its name and statement. -/
example {F : Type} [FiniteField F] [Fact (ringChar F ≠ 2)] : (1 : F) ≠ -1 := one_ne_neg_one

/-- A13, amended 2026-09-18: the legacy VM theorem keeps its name and binders, minus the
characteristic assumption, which was provably redundant (in characteristic `2` the no-wrap
guard forces an empty cycle). Callers that had the instance in scope still elaborate; this
example has none in scope. -/
example {F : Type} [FiniteField F] [DecidableEq F]
    (channel : RawChannel F) [channel.Normal]
    (pulls pushes : List (Interaction F))
    (balance : BalancedInteractions (pulls ++ pushes)) (data : ProverData F)
    (n : ℕ) (len_pulls : pulls.length = n) (len_pushes : pushes.length = n)
    (pulls_channel : ∀ a ∈ pulls, a.channel = channel)
    (pushes_channel : ∀ b ∈ pushes, b.channel = channel)
    (pulls_mult : ∀ a ∈ pulls, a.mult = -1) (pushes_mult : ∀ b ∈ pushes, b.mult = 1) :
    (∀ (i : ℕ) (hi : i < n), pulls[i].Guarantees data → pushes[i].Requirements data) →
    ∀ (i : ℕ) (hi: i < n), pushes[i].Requirements data → pulls[i].Guarantees data :=
  guarantees_of_requirements_of_requirements_of_guarantees channel pulls pushes balance data n
    len_pulls len_pushes pulls_channel pushes_channel pulls_mult pushes_mult

-- A13: the JSON of a legacy interaction is unchanged: channel, multiplicity, message, no tag.
#guard (Lean.toJson ((LegacyChannel (p := 5)).pushed 3).toRaw).compress ==
  "{\"channel\":\"legacy\",\"message\":[{\"type\":\"const\",\"value\":3}]," ++
  "\"multiplicity\":{\"type\":\"const\",\"value\":1}}"

/-- What the legacy relation excludes over `F 2`: more than one interaction on a channel,
since its no-wrap guard is `length < ringChar F = 2`. A matching provide/receive pair is
already too many. It says nothing about a channel without interactions; see
`legacyProto_satisfiable`. -/
theorem legacy_length_le_one_over_F2 (l : List (Interaction (F 2))) :
    BalancedInteractions l → l.length ≤ 1 :=
  length_le_one_of_balancedInteractions_of_ringChar_eq_two (ZMod.ringChar_zmod_n 2)
end Legacy

/-! ## The directed tag representation (A1) -/
section Directed
variable {K : Type} [FiniteField K] [DecidableEq K]

/-- A directed channel whose guarantee is that the message equals `1`. -/
def OneChannel (F : Type) [FiniteField F] : DirectedChannel F field where
  name := "one"
  Guarantees x _ := x = 1

/-- A directed channel whose guarantee can never be established. -/
def NeverDirected (F : Type) [FiniteField F] : DirectedChannel F field where
  name := "never-directed"
  Guarantees _ _ := False

/-- A1: the sign carries no direction over `F 2`; the tag does, over every field. -/
example : (-1 : F 2) = 1 := by decide
example : (Direction.provide.tag : F 2) ≠ Direction.receive.tag := by decide
example : (Direction.provide.tag : K) ≠ Direction.receive.tag := by simp [circuit_norm]

/-- A raw interaction on a directed channel whose last element is neither tag fails the local
contract whatever its gate, so it cannot occur in a sound row. The typed constructors always
emit a well-formed tag (`DirectedInteraction.toRaw_requirements`). -/
example (mult : F 5) (data : ProverData (F 5)) :
    ¬ (NeverDirected (F 5)).toRaw.Requirements mult #v[0, 2] data := by
  have h : (2 : F 5) ≠ 0 ∧ (2 : F 5) ≠ 1 := by decide
  simp [NeverDirected, DirectedChannel.toRaw, Direction.tag, h.1, h.2]

/-- A legacy channel with a two-element payload on the same wire name as `OneChannel`. -/
def LegacyTwo : Channel (F 5) (fields 2) where
  name := "one"
  Guarantees _ _ := True

-- Serialization shape only: the raw JSON of a directed interaction is the legacy
-- channel/message/multiplicity object with the tag as one more message element. It does not
-- identify the directed interpretation: a legacy interaction with a two-element payload
-- serializes to the same bytes. The opt-in directed export protocol is roadmap Layer 5 work and
-- does not exist yet.
#guard (Lean.toJson ((OneChannel (F 5)).pushed 3).toRaw).compress ==
  "{\"channel\":\"one\",\"message\":[{\"type\":\"const\",\"value\":3}," ++
  "{\"type\":\"const\",\"value\":0}],\"multiplicity\":{\"type\":\"const\",\"value\":1}}"
#guard (Lean.toJson ((OneChannel (F 5)).pushed 0).toRaw).compress ==
  (Lean.toJson (LegacyTwo.pushed #v[0, 0]).toRaw).compress
end Directed

/-! ## Necessity of the kernel hypotheses (A2–A6) -/
section Necessity

/-- A throwaway legacy raw channel with trivial guarantees and requirements. -/
def anyChannel (F : Type) [FiniteField F] : RawChannel F :=
  ⟨"any", 1, fun _ _ _ => True, fun _ _ _ => True⟩

def pull1 : Interaction (F 2) := ⟨anyChannel (F 2), -1, #[0], rfl, true⟩
def push1 : Interaction (F 2) := ⟨anyChannel (F 2), 1, #[0], rfl, false⟩

/-- A2: field-sum balance without the no-wrap guard admits two unsupported unit receives
over `F 2`. -/
theorem logUp_guard_necessary :
    (∀ msg, balanceOf [pull1, pull1] msg = 0) ∧
    ¬ PullsSupported Interaction.legacyEvent [pull1, pull1] := by
  refine ⟨?_, ?_⟩
  · intro msg
    by_cases h : msg = #[0]
    · subst h
      decide
    · have h' : (#[0] : Array (F 2)) ≠ msg := fun e => h e.symm
      simp [balanceOf, pull1, h']
  · intro h
    obtain ⟨j, hj, hdir, -, -⟩ := h pull1 (by simp) (by decide) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at hj
    subst hj
    exact absurd hdir (by decide)

/-- Today's guard excludes every pair over `F 2`, matched or not: an instance of
`legacy_length_le_one_over_F2`. -/
theorem logUp_guard_excludes_pairs : ¬ BalancedInteractions [pull1, push1] :=
  fun h => absurd (legacy_length_le_one_over_F2 _ h) (by simp)

def push5 : Interaction (F 5) := ⟨anyChannel (F 5), 1, #[0], rfl, false⟩
def push2 : Interaction (F 5) := ⟨anyChannel (F 5), 2, #[0], rfl, false⟩
def pull5 : Interaction (F 5) := ⟨anyChannel (F 5), -1, #[0], rfl, true⟩
def pullW2 : Interaction (F 5) := ⟨anyChannel (F 5), -2, #[0], rfl, true⟩

/-- A4: on the legacy path, a signed receive of weight `2` is not a receive at all. Over `F 5`
the multiplicity `-2` is neither `1` nor `-1`, it balances a weight-2 provider, and the sign
reading makes it a provider (which owes the requirement). Non-unit receive weights are
therefore not representable as receives; the directed path rejects them locally instead. -/
theorem legacy_reads_weight_two_receive_as_provider :
    ((-2 : F 5) ≠ 1 ∧ (-2 : F 5) ≠ -1) ∧ BalancedInteractions [push2, pullW2] ∧
    pullW2.legacyEvent.direction = .provide := by
  refine ⟨by decide, ⟨?_, ?_⟩, by decide⟩
  · left
    rw [ZMod.ringChar_zmod_n]
    decide
  · intro msg
    by_cases h : msg = #[0]
    · subst h
      decide
    · have h' : (#[0] : Array (F 5)) ≠ msg := fun e => h e.symm
      simp [balanceOf, push2, pullW2, h']

/-- A5: a signed receive of weight `2` against two unit providers over `F 5` is
LogUp-balanced, yet all three read as providers and nothing reads as a receive. Count balance
needs unit events on the receive side. -/
theorem logUp_unit_receives_necessary :
    BalancedInteractions [push5, push5, pullW2] ∧
    ¬ CountBalanced Interaction.legacyEvent [push5, push5, pullW2] := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · left
    rw [ZMod.ringChar_zmod_n]
    decide
  · intro msg
    by_cases h : msg = #[0]
    · subst h
      decide
    · have h' : (#[0] : Array (F 5)) ≠ msg := fun e => h e.symm
      simp [balanceOf, push5, pullW2, h']
  · intro h
    have := h #[0]
    revert this
    decide

/-- A6: a weight-2 provider and two unit receives over `F 5` are LogUp-balanced, yet the
active counts are `1` and `2`. Count balance needs unit events on the provider side. -/
theorem logUp_unit_events_necessary :
    BalancedInteractions [push2, pull5, pull5] ∧
    ¬ CountBalanced Interaction.legacyEvent [push2, pull5, pull5] := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · left
    rw [ZMod.ringChar_zmod_n]
    decide
  · intro msg
    by_cases h : msg = #[0]
    · subst h
      decide
    · have h' : (#[0] : Array (F 5)) ≠ msg := fun e => h e.symm
      simp [balanceOf, push2, pull5, h']
  · intro h
    have := h #[0]
    revert this
    decide

def provide1 : Interaction (F 2) := (OneChannel (F 2)).emittedValue .provide 1 1 false
def receive1 : Interaction (F 2) := (OneChannel (F 2)).emittedValue .receive 1 1 true

/-- A3: the multiset model rejects two providers of a message with no receive. -/
theorem multiset_rejects_two_providers :
    ¬ (BalanceModel.multiset (F 2)).Balanced [provide1, provide1] := by
  rw [BalanceModel.multiset_balanced_iff]
  simp [activePayloads, provide1, circuit_norm]

/-- A9 in miniature: the multiset model accepts a matched pair over `F 2` ... -/
theorem multiset_accepts_matched_pair :
    (BalanceModel.multiset (F 2)).Balanced [provide1, receive1] := by
  rw [BalanceModel.multiset_balanced_iff]
  simp [activePayloads, provide1, receive1, circuit_norm]

/-- ... which the legacy guard rejects, so `F 2` cannot silently fall back to LogUp (A14):
another instance of `legacy_length_le_one_over_F2`. -/
theorem logUp_rejects_matched_pair : ¬ BalancedInteractions [provide1, receive1] :=
  fun h => absurd (legacy_length_le_one_over_F2 _ h) (by simp)
end Necessity

/-! ## Consistency under a model, and what happens under the wrong one (A15, A17) -/
section Consistency
variable {K : Type} [FiniteField K] [DecidableEq K]
variable {Message : TypeMap} [ProvableType Message]

/-- A directed channel over `F 2` with an arbitrary guarantee. -/
def PChannel (P : F 2 → Prop) : DirectedChannel (F 2) field where
  name := "p"
  Guarantees x _ := P x

def pProvide (P : F 2 → Prop) : Interaction (F 2) := (PChannel P).emittedValue .provide 1 1 false
def pReceive (P : F 2 → Prop) : Interaction (F 2) := (PChannel P).emittedValue .receive 1 1 true

/-- A15 in miniature, over `F 2`. The guarantee of the receive is not free: it is `P 1` ... -/
theorem pReceive_guarantees_iff (P : F 2 → Prop) (data : ProverData (F 2)) :
    (pReceive P).Guarantees data ↔ P 1 := by
  simp [pReceive, PChannel, Interaction.Guarantees, Interaction.msgVector,
    DirectedChannel.emittedValue, DirectedChannel.toRaw, Direction.tag, fromElements, field,
    ProvableType.fromElements, toElements, ProvableType.toElements]
  rfl

/-- ... the multiset relation accepts the matched pair whatever `P` is ... -/
theorem multiset_accepts_pPair (P : F 2 → Prop) :
    (BalanceModel.multiset (F 2)).Balanced [pProvide P, pReceive P] := by
  rw [BalanceModel.multiset_balanced_iff]
  simp [activePayloads, pProvide, pReceive, circuit_norm]

/-- ... so the consistency of the channel under the multiset model, found by instance search,
turns the requirements of the pair into the guarantee of the receive ... -/
theorem pReceive_guarantees_of_requirements (P : F 2 → Prop) (data : ProverData (F 2))
    (reqs : ∀ i ∈ [pProvide P, pReceive P],
      i.channel = (PChannel P).toRaw ∧ i.Requirements data) :
    (pReceive P).Guarantees data :=
  RawChannel.ConsistentWith.consistent (model := .multiset (F 2)) _ data
    (multiset_accepts_pPair P) reqs _ (by simp)

/-- ... and those requirements hold exactly when the provider establishes `P 1`. -/
theorem pPair_requirements_iff (P : F 2 → Prop) (data : ProverData (F 2)) :
    (∀ i ∈ [pProvide P, pReceive P], i.channel = (PChannel P).toRaw ∧ i.Requirements data) ↔
      P 1 := by
  simp [pProvide, pReceive, PChannel, Interaction.Requirements, Interaction.msgVector,
    DirectedChannel.emittedValue, DirectedChannel.toRaw, Direction.tag, fromElements, field,
    ProvableType.fromElements, toElements, ProvableType.toElements]

/-- Correct pairings are found by instance search: directed channels under the multiset
model over any field, in particular `F 2`, and legacy channels under LogUp. -/
example (channel : DirectedChannel K Message) : channel.toRaw.ConsistentWith (.multiset K) :=
  inferInstance
example : (OneChannel (F 2)).toRaw.ConsistentWith (.multiset (F 2)) := inferInstance
example : (LegacyChannel (p := 5)).toRaw.ConsistentWith (.logUp (F 5)) := inferInstance

/-- Two pulls on the legacy channel whose guarantee is `x = 7`, of the messages `0` and `3`.
A legacy pull owes nothing. -/
def legacyPull0 : Interaction (F 5) := ⟨(LegacyChannel (p := 5)).toRaw, -1, #[0], rfl, true⟩
def legacyPull3 : Interaction (F 5) := ⟨(LegacyChannel (p := 5)).toRaw, -1, #[3], rfl, true⟩

/-- The multiset model on a legacy channel reads the wrong encoding: it strips the only
payload element as if it were a tag, so the pull of `0` reads as a provide and the pull of
`3` as a receive, both of the empty payload, and the relation accepts two messages that never
matched and that nobody provided. -/
theorem multiset_accepts_two_legacy_pulls :
    (BalanceModel.multiset (F 5)).Balanced [legacyPull0, legacyPull3] := by
  rw [BalanceModel.multiset_balanced_iff]
  decide

/-- So a legacy channel is not consistent under the multiset model: the two pulls are balanced
and meet their (empty) requirements, yet the pull of `3` would be granted `3 = 7`. No instance
can exist for this pairing, and `FormalEnsembleWith.consistent` cannot be supplied for it. -/
theorem legacy_not_consistentWith_multiset :
    ¬ (LegacyChannel (p := 5)).toRaw.ConsistentWith (.multiset (F 5)) := by
  intro h
  have grt := h.consistent [legacyPull0, legacyPull3] (fun _ _ => #[])
    multiset_accepts_two_legacy_pulls
    (by
      intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl <;>
        exact ⟨rfl, by simp [Interaction.Requirements, legacyPull0, legacyPull3, Channel.toRaw]⟩)
    legacyPull3 (by simp)
  revert grt
  simp [Interaction.Guarantees, Interaction.msgVector, legacyPull3, Channel.toRaw, LegacyChannel,
    fromElements, field, ProvableType.fromElements]
  decide

def provide5 : Interaction (F 5) := (OneChannel (F 5)).emittedValue .provide 1 1 false
def receive5 : Interaction (F 5) := (OneChannel (F 5)).emittedValue .receive 1 1 true

/-- The opposite mismatch: LogUp on a directed channel. A matched provide and receive both
have multiplicity `1` and differ in their tag, so no sum cancels. Over `F 5` the no-wrap guard
holds for the pair, and the relation still rejects it. -/
theorem logUp_rejects_directed_pair :
    ¬ (BalanceModel.logUp (F 5)).Balanced [provide5, receive5] := by
  rw [BalanceModel.logUp_balanced_iff]
  intro ⟨_, h⟩
  have := h provide5.msg
  revert this
  decide
end Consistency

/-! ## The directed reading on malformed tags and on activity (A17) -/
section Reading
variable {K : Type} [FiniteField K] [DecidableEq K]

/-- A raw interaction on a directed channel whose last element is neither tag, with an active
gate and permission to assume. Only a raw construction can produce it; the typed constructors
always emit a well-formed tag. -/
def malformed : Interaction (F 5) := ⟨(NeverDirected (F 5)).toRaw, 1, #[0, 2], rfl, true⟩

/-- A17, malformed tags: the directed reading is total and reads a malformed tag as an active
receive, never as a provider, so it can support nothing. That receive assumes nothing: its
guarantee holds for every prover data although the channel's guarantee is `False`. And the
Layer 0 contract rejects it, so it cannot occur in a sound row. -/
theorem malformed_reads_as_receive_assuming_nothing (data : ProverData (F 5)) :
    malformed.directedEvent.direction = .receive ∧ malformed.directedEvent.active = true ∧
    malformed.Guarantees data ∧ ¬ malformed.Requirements data := by
  have h : (2 : F 5) ≠ 0 ∧ (2 : F 5) ≠ 1 := by decide
  refine ⟨by decide, by decide, ?_, ?_⟩
  · simp [malformed, Interaction.Guarantees, Interaction.msgVector, DirectedChannel.toRaw,
      Direction.tag, h.2]
  · simp [malformed, Interaction.Requirements, Interaction.msgVector, DirectedChannel.toRaw,
      Direction.tag, h.1, h.2]

/-- A17, activity: a disabled interaction is not an active event in the directed reading,
whatever its direction, payload and permission, over any field. -/
example (direction : Direction) (msg : K) (permission : Bool) :
    ((OneChannel K).emittedValue direction 0 msg permission).directedEvent.active = false := by
  simp [circuit_norm]

def disabledProvide : Interaction (F 2) := (OneChannel (F 2)).emittedValue .provide 0 1 false
def disabledReceive : Interaction (F 2) := (OneChannel (F 2)).emittedValue .receive 0 1 true

/-- So disabled interactions contribute no active payload in either direction ... -/
theorem disabled_contribute_no_active_payload :
    activePayloads Interaction.directedEvent [disabledProvide, disabledReceive] .provide = [] ∧
    activePayloads Interaction.directedEvent [disabledProvide, disabledReceive] .receive = [] := by
  simp [activePayloads, disabledProvide, disabledReceive, circuit_norm]

/-- ... a disabled provider supports nothing: next to it, the active receive `receive1` is
unsupported and the multiset model rejects the pair ... -/
theorem disabled_provider_supports_nothing :
    ¬ PullsSupported Interaction.directedEvent [disabledProvide, receive1] ∧
    ¬ (BalanceModel.multiset (F 2)).Balanced [disabledProvide, receive1] := by
  refine ⟨?_, ?_⟩
  · simp [PullsSupported, disabledProvide, receive1, circuit_norm]
  · rw [BalanceModel.multiset_balanced_iff]
    simp [activePayloads, disabledProvide, receive1, circuit_norm]

/-- ... and a disabled receive needs no support: alone, it is supported and balanced, as an
empty bus is. -/
theorem disabled_receive_needs_no_support :
    PullsSupported Interaction.directedEvent [disabledReceive] ∧
    (BalanceModel.multiset (F 2)).Balanced [disabledReceive] := by
  refine ⟨?_, ?_⟩
  · simp [PullsSupported, disabledReceive, circuit_norm]
  · rw [BalanceModel.multiset_balanced_iff]
    simp [activePayloads, disabledReceive, circuit_norm]
end Reading

/-! ## Explicit models (A14) -/
section Models

/-- A14, typechecking test: the model-aware statement is stated over any field with an
explicit model; there is no default instance to fall back to. The `Prop` is not proved. -/
example {F : Type} [FiniteField F] [DecidableEq F] {PublicIO : TypeMap} [ProvableType PublicIO]
    (model : BalanceModel F) (ens : Ensemble F PublicIO) (publicInput : PublicIO F) : Prop :=
  ens.StatementWith model publicInput

/-- A14, typechecking test: the multiset model is one such explicit model, over any field. -/
example {F : Type} [FiniteField F] [DecidableEq F] {PublicIO : TypeMap} [ProvableType PublicIO]
    (ens : Ensemble F PublicIO) (publicInput : PublicIO F) : Prop :=
  ens.StatementWith (.multiset F) publicInput

/-- `BalanceModel` is an abstract count/support interface: a model that reads every
interaction as an inactive event satisfies every field. Nothing in the structure relates
`view` to the raw channel contract. -/
def blindModel (F : Type) [FiniteField F] [DecidableEq F] : BalanceModel F where
  Verified _ := True
  SideCondition _ := True
  view _ := { payload := #[], direction := .provide, active := false }
  UnitEvent _ := True
  verified_of_perm _ _ := trivial
  sideCondition_of_perm _ _ := trivial
  pullsSupported := by intro l _ _; simp [PullsSupported]
  countBalanced := by intro l _ _ _; simp [CountBalanced, activeCount]

/-- So the interface alone does not reject a lone active receive that no provider supports,
although its raw guarantee (`message = 1`, for payload `0`) is false. Ruling this out is the
job of the correspondence law of the reading a model uses: for the directed reading,
`DirectedChannel.directedEvent_emittedValue` ties the view to the evaluated interactions of
the channel and `DirectedChannel.guarantees_of_requirements_of_pullsSupported` transports the
requirement of the supporting provider to the guarantee of the receive. That law lives
outside the structure. -/
example : (blindModel (F 2)).Balanced [(OneChannel (F 2)).emittedValue .receive 1 0 true] :=
  ⟨trivial, trivial⟩

example (data : ProverData (F 2)) :
    ¬ ((OneChannel (F 2)).emittedValue .receive 1 0 true).Guarantees data := by
  simp [OneChannel, Interaction.Guarantees, Interaction.msgVector, DirectedChannel.emittedValue,
    DirectedChannel.toRaw, Direction.tag, fromElements, field, ProvableType.fromElements,
    toElements, ProvableType.toElements]
  decide
end Models

/-! ## The Layer 0 prototype -/
section Prototype

structure ProtoInput (F : Type) where
  enabled : F
  x : F
deriving ProvableStruct

/-- One typed message on a directed channel: a receive with an assumption, a provider that
owes what the receive assumed, a gated receive without an assumption, and a gated provider. -/
def proto (F : Type) [FiniteField F] : GeneralFormalCircuit F ProtoInput unit where
  main input := do
    assertZero (input.enabled * (input.enabled - 1))
    (OneChannel F).pull input.x
    (OneChannel F).push input.x
    (OneChannel F).emit .receive input.enabled input.x
    (OneChannel F).pushIf input.enabled 1
  Spec input _ _ := input.x = 1
  ProverAssumptions input _ _ := (input.enabled = 0 ∨ input.enabled = 1) ∧ input.x = 1
  channelsWithRequirements := [(OneChannel F).toRaw]
  soundness := by
    circuit_proof_start [OneChannel]
    -- `h_holds` carries the boolean constraint and the guarantee assumed by the receive
    obtain ⟨h_bool, h_pull⟩ := h_holds
    rw [mul_eq_zero, sub_eq_zero] at h_bool
    simp_all
  completeness := by
    circuit_proof_start [OneChannel]
    obtain ⟨h_enabled, hx⟩ := h_assumptions
    refine ⟨?_, fun _ => hx⟩
    rcases h_enabled with h | h <;> simp [h]

example {F : Type} [FiniteField F] (input : Var ProtoInput F) :
    ExplicitCircuit ((proto F).main input) := by
  infer_explicit_circuit

/-- The prototype called as a subcircuit of another circuit. -/
def nestedProto (F : Type) [FiniteField F] (input : Var ProtoInput F) : Circuit F Unit :=
  proto F input

/-- The tag survives subcircuit composition, flattening and evaluation: the interactions
collected from the nested prototype are its four directed events, payload and tag intact and
in circuit order. -/
example {F : Type} [FiniteField F] (env : Environment F) (input : Var ProtoInput F) :
    ((nestedProto F input).operations 0).interactionValues env =
      [ (OneChannel F).emittedValue .receive 1 (env input.x) true,
        (OneChannel F).emittedValue .provide 1 (env input.x) false,
        (OneChannel F).emittedValue .receive (env input.enabled) (env input.x) false,
        (OneChannel F).emittedValue .provide (env input.enabled) 1 false ] := by
  simp [circuit_norm, nestedProto, proto, Operations.interactions,
    GeneralFormalCircuit.toSubcircuit_interactions, DirectedChannel.eval_toRaw]

/-- The prototype ensemble: one table on one directed channel, no verifier. -/
def protoEnsemble (F : Type) [FiniteField F] : Ensemble F unit where
  tables := [⟨ proto F ⟩]
  channels := [(OneChannel F).toRaw]

/-- The `consistent` field of `FormalEnsembleWith` for the prototype ensemble under the
multiset model, over any field: one case per channel, each closed by instance search. -/
example {F : Type} [FiniteField F] [DecidableEq F] :
    ∀ channel ∈ (protoEnsemble F).channels, channel.ConsistentWith (.multiset F) := by
  simp only [protoEnsemble, List.mem_singleton, forall_eq]
  infer_instance

/-- A14, typechecking tests: the model-aware statement of the prototype ensemble elaborates
over any field with an explicit model, in particular the multiset model, and over `F 2`. None
of these `Prop`s is proved here; the directed statement with a nonempty witness is A9
(roadmap Layer 4). -/
example {F : Type} [FiniteField F] [DecidableEq F] (model : BalanceModel F) : Prop :=
  (protoEnsemble F).StatementWith model ()
example {F : Type} [FiniteField F] [DecidableEq F] : Prop :=
  (protoEnsemble F).StatementWith (.multiset F) ()
example (model : BalanceModel (F 2)) : Prop := (protoEnsemble (F 2)).StatementWith model ()
example : Prop := (protoEnsemble (F 2)).StatementWith (.multiset (F 2)) ()

/-- The empty prototype table over `F 2`: no rows, hence no interactions. -/
def emptyProtoTable : Table (F 2) where
  component := ⟨ proto (F 2) ⟩
  width := 2
  table := []
  data := fun _ _ => #[]
  uniform_width := by simp

/-- The empty witness of the prototype ensemble over `F 2`. -/
def emptyProtoWitness : EnsembleWitness (protoEnsemble (F 2)) where
  tables := [emptyProtoTable]
  data := fun _ _ => #[]
  publicInput := ()
  same_length := rfl
  same_circuits := by
    intro i hi
    obtain rfl : i = 0 := by change i < 1 at hi; omega
    rfl
  same_data := by
    intro table ht
    simp only [List.mem_singleton] at ht
    subst ht
    rfl

/-- The legacy statement of the prototype ensemble is satisfiable over `F 2`: the empty trace
has no interactions, so every channel is balanced. The legacy limitation is
`legacy_length_le_one_over_F2`, not unsatisfiability of the statement. -/
theorem legacyProto_satisfiable : (protoEnsemble (F 2)).Statement () := by
  refine ⟨emptyProtoWitness, rfl, ?_, ?_⟩
  · rw [EnsembleWitness.Constraints, EnsembleWitness.forall_mem_allTables_iff]
    exact ⟨EnsembleWitness.verifierTable_constraints_of_verifier_empty rfl,
      by simp [emptyProtoWitness, emptyProtoTable, Table.Constraints]⟩
  · intro channel _
    have h : emptyProtoWitness.allTablesWitness.interactionsWith channel = [] := by
      rw [EnsembleWitness.interactionsWith_allTablesWitness,
        EnsembleWitness.interactionsWith_of_verifier_empty rfl]
      simp [emptyProtoWitness, emptyProtoTable, Table.interactionsWith]
    change BalancedInteractions (emptyProtoWitness.allTablesWitness.interactionsWith channel)
    rw [h]
    simp [BalancedInteractions, balanceOf, ZMod.ringChar_zmod_n]

/-- And it is satisfied only by empty prototype tables: every row puts four interactions on
the channel, where `legacy_length_le_one_over_F2` allows at most one. This is the precise form
of the legacy limitation for this ensemble. -/
theorem legacyProto_only_empty (witness : EnsembleWitness (protoEnsemble (F 2)))
    (balanced : witness.BalancedChannels) : ∀ table ∈ witness.tables, table.table = [] := by
  obtain ⟨t, ht⟩ := List.length_eq_one_iff.mp witness.same_length.symm
  have h_component : t.component = ⟨ proto (F 2) ⟩ := by
    have h := witness.same_circuits 0 (by simp [protoEnsemble])
    simp only [protoEnsemble, ht, List.getElem_cons_zero] at h
    exact h.symm
  have h_row (row : Array (F 2)) :
      (t.component.operations.interactionValuesWith (OneChannel (F 2)).toRaw
        (t.environment row)).length = 4 := by
    rw [Operations.interactionValuesWith_eq_map, Component.interactionsWith_eq, h_component]
    simp [circuit_norm, proto]
  have h_len := legacy_length_le_one_over_F2 _
    (balanced (OneChannel (F 2)).toRaw (by simp [protoEnsemble]))
  rw [EnsembleWitness.interactionsWith_allTablesWitness,
    EnsembleWitness.interactionsWith_of_verifier_empty rfl, ht] at h_len
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, Table.interactionsWith,
    List.length_flatMap, h_row, List.map_const', List.sum_replicate, smul_eq_mul] at h_len
  intro table h_table
  rw [ht, List.mem_singleton] at h_table
  subst h_table
  exact List.eq_nil_of_length_eq_zero (by omega)
end Prototype

end BusBalanceTests
