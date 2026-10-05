module

public import Clean.Air.BalanceModel
meta import Clean.Air.BalanceModel
meta import Clean.Circuit.Json
import Mathlib.Tactic.NormNum.Prime

/-!
# Bus balance tests

Tests for the event kernel of `Clean.Air.Balance`, the balance models and the directed channel
contract: legacy channels and their JSON, the directed tag and local contract, counterexamples
showing that the kernel hypotheses are needed, matching and mismatched model/channel pairings,
the directed reading of malformed tags, and a small directed circuit and ensemble. An `example`
whose type is `Prop` only checks elaboration; every semantic claim is a theorem or a `#guard`.
-/

@[expose] public section

namespace BusBalanceTests
open Air.Flat

instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-! ## Legacy channels -/
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

/-- Legacy `emit (-1)` neither assumes nor owes the guarantee, even a `False` one. -/
example (env : Environment (F p)) (msg : Expression (F p)) :
    ((NeverChannel (p := p)).emitted (-1) msg).Guarantees env ∧
    ((NeverChannel (p := p)).emitted (-1) msg).Requirements env := by
  simp [circuit_norm]

/-- A legacy requirement is proved from the guarantee under two premises. -/
example (env : Environment (F p)) (m msg : Expression (F p))
    (h : (LegacyChannel (p := p)).Guarantees (eval env msg) env.data) :
    ((LegacyChannel (p := p)).emitted m msg).Requirements env :=
  fun _ _ => h

/-- The statement of `exists_push_of_pull`. -/
example {F : Type} [FiniteField F] [DecidableEq F] (interactions : List (Interaction F))
    (balance : BalancedInteractions interactions) :
    ∀ a ∈ interactions, a.mult = -1 →
      ∃ b ∈ interactions, b.msg = a.msg ∧ b.mult ≠ 0 ∧ b.mult ≠ -1 :=
  exists_push_of_pull interactions balance

/-- The statement of `one_ne_neg_one`. -/
example {F : Type} [FiniteField F] [Fact (ringChar F ≠ 2)] : (1 : F) ≠ -1 := one_ne_neg_one

/-- The legacy VM theorem needs no characteristic assumption. -/
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

-- The JSON of a legacy interaction: channel, multiplicity and message, with no tag.
#guard (Lean.toJson ((LegacyChannel (p := 5)).pushed 3).toRaw).compress ==
  "{\"channel\":\"legacy\",\"message\":[{\"type\":\"const\",\"value\":3}]," ++
  "\"multiplicity\":{\"type\":\"const\",\"value\":1}}"

/-- Over `F 2`, the no-wrap guard of `BalancedInteractions` allows at most one interaction on a
channel, so even a matching provide/receive pair is rejected. -/
theorem legacy_length_le_one_over_F2 (l : List (Interaction (F 2))) :
    BalancedInteractions l → l.length ≤ 1 :=
  length_le_one_of_balancedInteractions_of_ringChar_eq_two (ZMod.ringChar_zmod_n 2)
end Legacy

/-! ## Directed tags and local contract -/
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

/-- The sign carries no direction over `F 2`; the tag does, over every field. -/
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

-- A directed interaction serializes as a legacy interaction with the tag as one more message
-- element, so it has the same JSON as a legacy interaction with a two-element payload. The
-- interpretation is recorded separately by the bus export protocol (`Clean/Air/BusProtocol.lean`).
#guard (Lean.toJson ((OneChannel (F 5)).pushed 3).toRaw).compress ==
  "{\"channel\":\"one\",\"message\":[{\"type\":\"const\",\"value\":3}," ++
  "{\"type\":\"const\",\"value\":0}],\"multiplicity\":{\"type\":\"const\",\"value\":1}}"
#guard (Lean.toJson ((OneChannel (F 5)).pushed 0).toRaw).compress ==
  (Lean.toJson (LegacyTwo.pushed #v[0, 0]).toRaw).compress

/-- An active provider owes the guarantee, and every provider owes a boolean gate. -/
example (env : Environment K) (enabled x : Expression K) :
    ((OneChannel K).pushedIf enabled x).Requirements env ↔
      (Expression.eval env enabled = 0 ∨ Expression.eval env enabled = 1) ∧
      (Expression.eval env enabled ≠ 0 → (OneChannel K).Guarantees (eval env x) env.data) := by
  simp [circuit_norm]

/-- An active receiver may assume the guarantee and owes only the gate. -/
example (env : Environment K) (enabled x : Expression K) :
    (((OneChannel K).pulledIf enabled x).Guarantees env ↔
      (Expression.eval env enabled ≠ 0 → (OneChannel K).Guarantees (eval env x) env.data)) ∧
    (((OneChannel K).pulledIf enabled x).Requirements env ↔
      (Expression.eval env enabled = 0 ∨ Expression.eval env enabled = 1)) := by
  simp [circuit_norm]

/-- A receiver that declines the guarantee is granted nothing and owes only the gate, even on a
channel whose guarantee is `False`. -/
example (env : Environment K) (enabled x : Expression K) :
    ((NeverDirected K).emitted .receive enabled x).Guarantees env ∧
    (((NeverDirected K).emitted .receive enabled x).Requirements env ↔
      (Expression.eval env enabled = 0 ∨ Expression.eval env enabled = 1)) := by
  simp [circuit_norm, NeverDirected]

/-- A disabled event is granted nothing and owes nothing. -/
example (env : Environment K) (i : DirectedInteraction (NeverDirected K))
    (h : Expression.eval env i.enabled = 0) : i.Guarantees env ∧ i.Requirements env :=
  ⟨DirectedChannel.guarantees_of_enabled_eq_zero i h,
    DirectedChannel.requirements_of_enabled_eq_zero i h⟩

/-- On a directed channel, a receive of weight `2` violates the local contract, so no balance
argument sees a non-unit event. -/
example (data : ProverData (F 5)) :
    ¬ ((OneChannel (F 5)).emittedValue .receive 2 1 true).Requirements data := by
  rw [DirectedChannel.emittedValue_requirements_iff]
  rintro ⟨h, -⟩
  revert h
  decide
end Directed

/-! ## Necessity of the kernel hypotheses -/
section Necessity

def noData (F : Type) : ProverData F := fun _ _ => #[]

/-- A throwaway legacy raw channel with trivial guarantees and requirements. -/
def anyChannel (F : Type) [FiniteField F] : RawChannel F :=
  ⟨"any", 1, fun _ _ _ => True, fun _ _ _ => True⟩

def pull1 : Interaction (F 2) := ⟨anyChannel (F 2), -1, #[0], rfl, true⟩
def push1 : Interaction (F 2) := ⟨anyChannel (F 2), 1, #[0], rfl, false⟩

/-- Field-sum balance without the no-wrap guard admits two unsupported unit receives over
`F 2`. -/
theorem logUp_guard_necessary :
    (∀ msg, balanceOf [pull1, pull1] msg = 0) ∧
    ¬ PullsSupported Interaction.legacyEvent [pull1, pull1] := by
  refine ⟨?_, ?_⟩
  · intro msg
    by_cases h : msg = #[0]
    · subst h
      simp [balanceOf, pull1]; decide
    · have h' : (#[0] : Array (F 2)) ≠ msg := fun e => h e.symm
      simp [balanceOf, pull1, h']
  · intro h
    obtain ⟨j, hj, hdir, -, -⟩ := h pull1 (by simp) (by decide) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at hj
    subst hj
    exact absurd hdir (by decide)

/-- The no-wrap guard excludes every pair over `F 2`, matched or not. -/
theorem logUp_guard_excludes_pairs : ¬ BalancedInteractions [pull1, push1] :=
  fun h => absurd (legacy_length_le_one_over_F2 _ h) (by simp)

def push5 : Interaction (F 5) := ⟨anyChannel (F 5), 1, #[0], rfl, false⟩
def push2 : Interaction (F 5) := ⟨anyChannel (F 5), 2, #[0], rfl, false⟩
def pull5 : Interaction (F 5) := ⟨anyChannel (F 5), -1, #[0], rfl, true⟩
def pullW2 : Interaction (F 5) := ⟨anyChannel (F 5), -2, #[0], rfl, true⟩

/-- On a legacy channel, a receive of weight `2` is read as a provider: over `F 5`, `-2` is
neither `1` nor `-1`, and it balances a weight-2 provider. -/
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
      simp [balanceOf, push2, pullW2]
    · have h' : (#[0] : Array (F 5)) ≠ msg := fun e => h e.symm
      simp [balanceOf, push2, pullW2, h']

/-- A receive of weight `2` against two unit providers over `F 5` is LogUp-balanced, yet all
three read as providers. Count balance needs unit events on the receive side. -/
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
      simp [balanceOf, push5, pullW2]; decide
    · have h' : (#[0] : Array (F 5)) ≠ msg := fun e => h e.symm
      simp [balanceOf, push5, pullW2, h']
  · intro h
    have := h #[0]
    revert this
    simp [activeCount, Interaction.legacyEvent, push5, pullW2, List.countP_cons]; decide

/-- A weight-2 provider and two unit receives over `F 5` are LogUp-balanced, yet the active
counts are `1` and `2`. Count balance needs unit events on the provider side. -/
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
      simp [balanceOf, push2, pull5]; decide
    · have h' : (#[0] : Array (F 5)) ≠ msg := fun e => h e.symm
      simp [balanceOf, push2, pull5, h']
  · intro h
    have := h #[0]
    revert this
    simp [activeCount, Interaction.legacyEvent, push2, pull5, List.countP_cons]; decide

def provide1 : Interaction (F 2) := (OneChannel (F 2)).emittedValue .provide 1 1 false
def receive1 : Interaction (F 2) := (OneChannel (F 2)).emittedValue .receive 1 1 true

/-- The multiset model rejects two providers of a message with no receive. -/
theorem multiset_rejects_two_providers :
    ¬ (BalanceModel.multiset (F 2)).Balanced [provide1, provide1] := by
  rw [BalanceModel.multiset_balanced_iff]
  simp [activePayloads, provide1, circuit_norm]

/-- The multiset model accepts a matched pair over `F 2` ... -/
theorem multiset_accepts_matched_pair :
    (BalanceModel.multiset (F 2)).Balanced [provide1, receive1] := by
  rw [BalanceModel.multiset_balanced_iff]
  simp [activePayloads, provide1, receive1, circuit_norm]

/-- ... which the legacy relation rejects. -/
theorem logUp_rejects_matched_pair : ¬ BalancedInteractions [provide1, receive1] :=
  fun h => absurd (legacy_length_le_one_over_F2 _ h) (by simp)

def neverReceive : Interaction (F 2) := (NeverDirected (F 2)).emittedValue .receive 1 0 true
def receiveTaggedPush : Interaction (F 2) :=
  (NeverDirected (F 2)).emittedValue .receive 1 0 false
def disabledPush : Interaction (F 2) := (NeverDirected (F 2)).emittedValue .provide 0 0 false

/-- The provider role is necessary for the bridge from a push's requirement to a pull's
guarantee: an active receive-tagged interaction with the same payload satisfies its requirement
trivially, yet the receiver's guarantee is `False`. -/
theorem bridge_provider_role_necessary :
    receiveTaggedPush.directedEvent.active = true ∧
    receiveTaggedPush.directedEvent.payload = neverReceive.directedEvent.payload ∧
    receiveTaggedPush.Requirements (noData (F 2)) ∧
    ¬ neverReceive.Guarantees (noData (F 2)) := by
  simp only [receiveTaggedPush, neverReceive, DirectedChannel.directedEvent_emittedValue,
    DirectedChannel.emittedValue_requirements_iff, DirectedChannel.emittedValue_guarantees_iff]
  simp [NeverDirected]

/-- Activity is necessary for the bridge: a disabled provider owes nothing. -/
theorem bridge_activity_necessary :
    disabledPush.directedEvent.direction = .provide ∧
    disabledPush.directedEvent.payload = neverReceive.directedEvent.payload ∧
    disabledPush.Requirements (noData (F 2)) ∧
    ¬ neverReceive.Guarantees (noData (F 2)) := by
  simp only [disabledPush, neverReceive, DirectedChannel.directedEvent_emittedValue,
    DirectedChannel.emittedValue_requirements_iff, DirectedChannel.emittedValue_guarantees_iff]
  simp [NeverDirected]
end Necessity

/-! ## Consistency under matching and mismatched models -/
section Consistency
variable {K : Type} [FiniteField K] [DecidableEq K]
variable {Message : TypeMap} [ProvableType Message]

/-- A directed channel over `F 2` with an arbitrary guarantee. -/
def PChannel (P : F 2 → Prop) : DirectedChannel (F 2) field where
  name := "p"
  Guarantees x _ := P x

def pProvide (P : F 2 → Prop) : Interaction (F 2) := (PChannel P).emittedValue .provide 1 1 false
def pReceive (P : F 2 → Prop) : Interaction (F 2) := (PChannel P).emittedValue .receive 1 1 true

/-- Over `F 2`, the guarantee of the receive is `P 1` ... -/
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

/-- ... so the pair's requirements give the receive's guarantee, through the channel's
consistency under the multiset model, found by instance search ... -/
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

/-- The transport needs pull support: a lone active receive on the channel whose guarantee is
`False` meets every requirement (boolean gate, well-formed tag, not a provider), and its
guarantee is refutable. -/
theorem transport_needs_support (data : ProverData (F 2)) :
    (∀ i ∈ [pReceive (fun _ => False)],
      i.channel = (PChannel (fun _ => False)).toRaw ∧ i.Requirements data) ∧
    ¬ (pReceive (fun _ => False)).Guarantees data := by
  refine ⟨?_, ?_⟩
  · intro i hi
    simp only [List.mem_singleton] at hi
    subst hi
    exact ⟨rfl, by
      simp [pReceive, PChannel, Interaction.Requirements, Interaction.msgVector,
        DirectedChannel.emittedValue, DirectedChannel.toRaw, Direction.tag]⟩
  · rw [pReceive_guarantees_iff]
    exact id

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
and meet their (empty) requirements, yet the pull of `3` would be granted `3 = 7`. -/
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
  simp [balanceOf, provide5, receive5, DirectedChannel.emittedValue, circuit_norm,
    Array.push_eq_push]

/-- That mismatch makes the obligation vacuous rather than false: under LogUp every directed
gate is `0` or `1` and nothing cancels, so a balanced list on a directed channel has no active
interaction. `BalanceModel.Reads` is what excludes this pairing. -/
theorem directed_consistentWith_logUp (channel : DirectedChannel K Message) :
    channel.toRaw.ConsistentWith (.logUp K) := by
  constructor
  intro interactions data balanced reqs a a_mem
  rw [BalanceModel.logUp_balanced_iff] at balanced
  obtain ⟨guard, bal⟩ := balanced
  -- every active interaction on the channel has gate `1`
  have unit : ∀ i ∈ interactions, i.msg = a.msg → i.mult ≠ 0 → i.mult = 1 := by
    intro i hi _ hne
    have h := (reqs i hi).2
    rw [Interaction.requirements_iff_of_channel_eq (reqs i hi).1] at h
    rcases h.1 with h0 | h1
    · exact absurd h0 hne
    · exact h1
  -- so the field sum for `a.msg` is the number of active interactions carrying it, and the
  -- no-wrap guard turns "zero in the field" into "zero"
  have hbal := bal a.msg
  rw [balanceOf_eq_of_mult_or_zero unit, one_mul] at hbal
  have hcount : interactions.countP (fun i => i.msg = a.msg && i.mult ≠ 0) = 0 :=
    (natCast_eq_iff_of_le_of_lt_ringChar List.countP_le_length (Nat.zero_le _) guard).mp
      (by rw [Nat.cast_zero]; exact hbal)
  -- hence `a` is not active, and its guarantee holds vacuously
  rw [Interaction.guarantees_iff_of_channel_eq (reqs a a_mem).1]
  intro _ _ a_active
  exfalso
  rw [List.countP_eq_zero] at hcount
  exact hcount a a_mem (by simp [a_active])

/-- In particular for the directed channel whose guarantee is `False`. -/
example : (NeverDirected (F 5)).toRaw.ConsistentWith (.logUp (F 5)) :=
  directed_consistentWith_logUp _

-- Instance search finds neither mismatched pairing. `#check_failure` succeeds exactly when
-- elaboration fails; its report is dropped.
#guard_msgs (drop info) in
#check_failure (inferInstance : (LegacyChannel (p := 5)).toRaw.ConsistentWith (.multiset (F 5)))
#guard_msgs (drop info) in
#check_failure (inferInstance : (OneChannel (F 5)).toRaw.ConsistentWith (.logUp (F 5)))

/-- Each model reads exactly one channel kind, over any field ... -/
example : (BalanceModel.logUp K).Reads (Channel K) := inferInstance
example : (BalanceModel.multiset K).Reads (DirectedChannel K) := inferInstance

-- ... and a channel of the other kind is a type error.
#guard_msgs (drop info) in
#check_failure (inferInstance : (BalanceModel.logUp (F 2)).Reads (DirectedChannel (F 2)))
#guard_msgs (drop info) in
#check_failure (inferInstance : (BalanceModel.multiset (F 5)).Reads (Channel (F 5)))

/-- The erasure through `Reads` is the channel's own `toRaw`, as `circuit_norm` sees it. -/
example (channel : DirectedChannel K Message) :
    BalanceModel.Reads.toRaw (model := .multiset K) channel = channel.toRaw := by
  simp only [circuit_norm]
end Consistency

/-! ## The directed reading on malformed tags and activity -/
section Reading
variable {K : Type} [FiniteField K] [DecidableEq K]

/-- A raw interaction on a directed channel whose last element is neither tag, with an active
gate and permission to assume. Only a raw construction can produce it; the typed constructors
always emit a well-formed tag. -/
def malformed : Interaction (F 5) := ⟨(NeverDirected (F 5)).toRaw, 1, #[0, 2], rfl, true⟩

/-- The directed reading reads a malformed tag as an active receive, never as a provider, and
its guarantee holds although the channel's guarantee is `False`; the local contract rejects
it. -/
theorem malformed_reads_as_receive_assuming_nothing (data : ProverData (F 5)) :
    malformed.directedEvent.direction = .receive ∧ malformed.directedEvent.active = true ∧
    malformed.Guarantees data ∧ ¬ malformed.Requirements data := by
  have h : (2 : F 5) ≠ 0 ∧ (2 : F 5) ≠ 1 := by decide
  refine ⟨by decide, by decide, ?_, ?_⟩
  · simp [malformed, Interaction.Guarantees, Interaction.msgVector, DirectedChannel.toRaw,
      Direction.tag, h.2]
  · simp [malformed, Interaction.Requirements, Interaction.msgVector, DirectedChannel.toRaw,
      Direction.tag, h.1, h.2]

/-- A disabled interaction is not an active event in the directed reading, whatever its
direction, payload and permission. -/
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

/-! ## Explicit models -/
section Models

/-- The model-aware statement takes an explicit model, over any field. -/
example {F : Type} [FiniteField F] [DecidableEq F] {PublicIO : TypeMap} [ProvableType PublicIO]
    (model : BalanceModel F) (ens : Ensemble F PublicIO) (publicInput : PublicIO F) : Prop :=
  ens.StatementWith model publicInput

/-- The multiset model, over any field. -/
example {F : Type} [FiniteField F] [DecidableEq F] {PublicIO : TypeMap} [ProvableType PublicIO]
    (ens : Ensemble F PublicIO) (publicInput : PublicIO F) : Prop :=
  ens.StatementWith (.multiset F) publicInput

/-- A model that reads every interaction as an inactive event satisfies every field of
`BalanceModel`: the structure does not relate `view` to the channel contract. -/
def blindModel (F : Type) [FiniteField F] [DecidableEq F] : BalanceModel F where
  Verified _ := True
  SideCondition _ := True
  view _ := { payload := #[], direction := .provide, active := false }
  UnitEvent _ := True
  verified_of_perm _ _ := trivial
  sideCondition_of_perm _ _ := trivial
  pullsSupported := by intro l _ _; simp [PullsSupported]
  countBalanced := by intro l _ _ _; simp [CountBalanced, activeCount]

/-- So the structure alone does not reject a lone active receive that no provider supports,
although its guarantee (`message = 1`, for payload `0`) is false. -/
example : (blindModel (F 2)).Balanced [(OneChannel (F 2)).emittedValue .receive 1 0 true] :=
  ⟨trivial, trivial⟩

example (data : ProverData (F 2)) :
    ¬ ((OneChannel (F 2)).emittedValue .receive 1 0 true).Guarantees data := by
  simp [OneChannel, Interaction.Guarantees, Interaction.msgVector, DirectedChannel.emittedValue,
    DirectedChannel.toRaw, Direction.tag, fromElements, field, ProvableType.fromElements,
    toElements, ProvableType.toElements]
  decide
end Models

/-! ## A directed circuit and ensemble -/
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

/-- `proto` called as a subcircuit of another circuit. -/
def nestedProto (F : Type) [FiniteField F] (input : Var ProtoInput F) : Circuit F Unit :=
  proto F input

/-- The tag survives subcircuit composition, flattening and evaluation: the interactions
collected from `nestedProto` are its four directed events, with payload and tag, in order. -/
example {F : Type} [FiniteField F] (env : Environment F) (input : Var ProtoInput F) :
    ((nestedProto F input).operations 0).interactionValues env =
      [ (OneChannel F).emittedValue .receive 1 (env input.x) true,
        (OneChannel F).emittedValue .provide 1 (env input.x) false,
        (OneChannel F).emittedValue .receive (env input.enabled) (env input.x) false,
        (OneChannel F).emittedValue .provide (env input.enabled) 1 false ] := by
  simp [circuit_norm, nestedProto, proto, Operations.interactions,
    GeneralFormalCircuit.toSubcircuit_interactions, DirectedChannel.eval_toRaw]

/-- One table of `proto` on one directed channel, and no verifier. -/
def protoEnsemble (F : Type) [FiniteField F] : Ensemble F unit where
  tables := [⟨ proto F ⟩]
  channels := [(OneChannel F).toRaw]

/-- The `consistent` field of `FormalEnsembleWith` for `protoEnsemble` under the multiset
model: one case per channel, each closed by instance search. -/
example {F : Type} [FiniteField F] [DecidableEq F] :
    ∀ channel ∈ (protoEnsemble F).channels, channel.ConsistentWith (.multiset F) := by
  simp only [protoEnsemble, List.mem_singleton, forall_eq]
  infer_instance

/-- The model-aware statement of `protoEnsemble` elaborates with an explicit model, over any
field and over `F 2`. -/
example {F : Type} [FiniteField F] [DecidableEq F] (model : BalanceModel F) : Prop :=
  (protoEnsemble F).StatementWith model ()
example {F : Type} [FiniteField F] [DecidableEq F] : Prop :=
  (protoEnsemble F).StatementWith (.multiset F) ()
example (model : BalanceModel (F 2)) : Prop := (protoEnsemble (F 2)).StatementWith model ()
example : Prop := (protoEnsemble (F 2)).StatementWith (.multiset (F 2)) ()

/-- The empty table of `proto` over `F 2`: no rows, hence no interactions. -/
def emptyProtoTable : Table (F 2) where
  component := ⟨ proto (F 2) ⟩
  width := 2
  table := []
  data := fun _ _ => #[]
  uniform_width := by simp

/-- The empty witness of `protoEnsemble` over `F 2`. -/
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

/-- The legacy statement of `protoEnsemble` is satisfiable over `F 2`, by the empty trace ... -/
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

/-- ... and only by empty tables: every row puts four interactions on the channel, where
`legacy_length_le_one_over_F2` allows at most one. -/
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
