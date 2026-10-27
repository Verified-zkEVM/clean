module

public import Clean.Circuit
public import Clean.Gadgets.Boolean

@[expose] public section

variable {F : Type} [FiniteField F]
variable {Message : TypeMap} [ProvableType Message]

/-
## Channel balance

This module treats channel interactions as multisets of pushed and pulled messages and asks what
properties can be deduced from the condition of _balance_: that every pulled message is matched
by a pushed one.

What balance means depends on the proof system. `BalancedInteractions` collects the facts that the
soundness theory uses, and a `Balance` is a check that a verifier performs on the interactions
with a channel, together with the proof that the check implies these facts.
-/

namespace Interaction
/-- A pull of one copy of a message: the interactions that typed channels give their guarantee. -/
def Pull (i : Interaction F) : Prop := i.direction = .pull ∧ i.mult = 1

/--
An interaction that pushes its message: an active push, or a pull of multiplicity other than `0` or
`1`, which acts as a push under field-sum balance.
-/
def Push (i : Interaction F) : Prop := i.mult ≠ 0 ∧ (i.direction = .pull → i.mult ≠ 1)

lemma not_push_iff {i : Interaction F} : ¬i.Push ↔ i.mult = 0 ∨ i.Pull := by
  simp only [Push, Pull, not_and, Classical.not_imp]
  tauto
end Interaction

/-- The number of active interactions in a direction that carry a message. -/
def activeCount (interactions : List (Interaction F)) (direction : Direction) (msg : Array F) : ℕ :=
  interactions.countP fun i => i.direction = direction ∧ i.msg = msg ∧ i.mult ≠ 0

/-- The messages of the active interactions in a direction. -/
def activeMessages (interactions : List (Interaction F)) (direction : Direction) :
    List (Array F) :=
  (interactions.filter fun i => i.direction = direction ∧ i.mult ≠ 0).map (·.msg)

lemma count_activeMessages (interactions : List (Interaction F)) (direction : Direction)
    (msg : Array F) :
    (activeMessages interactions direction).count msg = activeCount interactions direction msg := by
  simp only [activeMessages, activeCount, List.count_eq_countP, List.countP_map,
    List.countP_filter]
  apply List.countP_congr
  intro i _
  simp only [Function.comp_apply, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq]
  tauto

/--
The facts about balanced interactions that soundness proofs use:
- a pull of one copy of a message is matched by a push of it, and
- if all interactions carrying a message have multiplicity `0` or `1`, it is pushed and pulled
  equally often.
-/
structure BalancedInteractions (interactions : List (Interaction F)) : Prop where
  exists_push_of_pull : ∀ a ∈ interactions, a.Pull →
    ∃ b ∈ interactions, b.msg = a.msg ∧ b.Push
  activeCount_push_eq_activeCount_pull_of_isBool : ∀ msg : Array F,
    (∀ i ∈ interactions, i.msg = msg → IsBool i.mult) →
    activeCount interactions .push msg = activeCount interactions .pull msg

/-- Balance is invariant under permutation of the interaction list. -/
lemma BalancedInteractions.of_perm {as bs : List (Interaction F)} :
    BalancedInteractions as → List.Perm as bs → BalancedInteractions bs := by
  rintro ⟨ push_of_pull, counts ⟩ perm
  constructor
  · intro a a_mem a_pull
    obtain ⟨ b, b_mem, b_msg, b_push ⟩ := push_of_pull a (perm.mem_iff.mpr a_mem) a_pull
    exact ⟨ b, perm.mem_iff.mp b_mem, b_msg, b_push ⟩
  · intro msg isBool
    simp only [activeCount, ← perm.countP_eq]
    exact counts msg fun i hi => isBool i (perm.mem_iff.mp hi)

lemma BalancedInteractions.nil : BalancedInteractions ([] : List (Interaction F)) :=
  ⟨ by simp, by simp [activeCount] ⟩

/--
A balance check: the condition that a verifier checks on the interactions with each channel, and its
proof that the condition implies `BalancedInteractions`.
-/
structure Balance (F : Type) [FiniteField F] where
  Balanced : List (Interaction F) → Prop
  balancedInteractions_of_balanced : ∀ interactions,
    Balanced interactions → BalancedInteractions interactions

/-
## LogUp: field-sum balance
-/

/-- The multiplicity of an interaction with sign: pushes count positively, pulls negatively. -/
def Interaction.signedMult (i : Interaction F) : F :=
  match i.direction with
  | .push => i.mult
  | .pull => -i.mult

/-- Balance of one message: the sum of signed multiplicities of the interactions carrying it. -/
def balanceOf (interactions : List (Interaction F)) (msg : Array F) : F :=
  interactions.filter (·.msg = msg) |>.map (·.signedMult) |>.sum

lemma balanceOf_cons {i : Interaction F} {is : List (Interaction F)} {msg : Array F} :
    balanceOf (i :: is) msg = (if i.msg = msg then i.signedMult else 0) + balanceOf is msg := by
  by_cases h : i.msg = msg <;> simp [balanceOf, h]

/--
If all interactions carrying a message have multiplicity `0` or `1`, its balance is the number of
active pushes minus the number of active pulls.
-/
lemma balanceOf_eq_sub_of_isBool {interactions : List (Interaction F)} {msg : Array F}
    (isBool : ∀ i ∈ interactions, i.msg = msg → IsBool i.mult) :
    balanceOf interactions msg =
      activeCount interactions .push msg - activeCount interactions .pull msg := by
  induction interactions with
  | nil => simp [balanceOf, activeCount]
  | cons i is ih =>
    rw [balanceOf_cons, ih (fun j hj => isBool j (List.mem_cons_of_mem i hj))]
    simp only [activeCount, List.countP_cons]
    by_cases h_msg : i.msg = msg
    · rcases isBool i List.mem_cons_self h_msg with h_mult | h_mult <;>
        cases h_direction : i.direction <;>
        simp [h_msg, h_mult, h_direction, Interaction.signedMult] <;> ring
    · simp [h_msg]

/--
LogUp balance: for every message, the signed multiplicities sum to zero, and there are fewer
interactions than the characteristic, so that counts can't wrap around.
-/
def LogUpBalanced (interactions : List (Interaction F)) : Prop :=
  interactions.length < ringChar F ∧ ∀ msg, balanceOf interactions msg = 0

/-- If all interactions carrying a message have multiplicity `0` or `1`, it is pushed and pulled
equally often. -/
theorem LogUpBalanced.activeCount_push_eq_activeCount_pull_of_isBool
    {interactions : List (Interaction F)} (balanced : LogUpBalanced interactions) (msg : Array F)
    (isBool : ∀ i ∈ interactions, i.msg = msg → IsBool i.mult) :
    activeCount interactions .push msg = activeCount interactions .pull msg := by
  obtain ⟨ length_lt, sums ⟩ := balanced
  have activeCount_lt (direction : Direction) :
      activeCount interactions direction msg < ringChar F :=
    lt_of_le_of_lt (List.countP_le_length) length_lt
  have sum := sums msg
  rw [balanceOf_eq_sub_of_isBool isBool, sub_eq_zero,
    Lean.Grind.IsCharP.natCast_eq_iff_of_lt _ (activeCount_lt _) (activeCount_lt _)] at sum
  exact sum

/-- Every pull of one copy of a message is matched by a push of it. -/
theorem LogUpBalanced.exists_push_of_pull {interactions : List (Interaction F)}
    (balanced : LogUpBalanced interactions) :
    ∀ a ∈ interactions, a.Pull → ∃ b ∈ interactions, b.msg = a.msg ∧ b.Push := by
  intro a a_mem a_pull
  -- assuming no such push exists, all interactions with the message are pulls of one copy or
  -- inactive, so balance says that there are none
  by_contra! no_push
  have isBool : ∀ i ∈ interactions, i.msg = a.msg → IsBool i.mult := by
    intro i i_mem i_msg
    rcases Interaction.not_push_iff.mp (no_push i i_mem i_msg) with h | h
    · exact .inl h
    · exact .inr h.2
  have no_active_push : activeCount interactions .push a.msg = 0 := by
    simp only [activeCount, List.countP_eq_zero, decide_eq_true_eq, not_and]
    intro i i_mem i_push i_msg i_mult
    rcases Interaction.not_push_iff.mp (no_push i i_mem i_msg) with h | h
    · exact i_mult h
    · simp [h.1] at i_push
  have pull_pos : 0 < activeCount interactions .pull a.msg := by
    apply List.countP_pos_iff.mpr
    exact ⟨ a, a_mem, by simp [a_pull.1, a_pull.2] ⟩
  have := balanced.activeCount_push_eq_activeCount_pull_of_isBool a.msg isBool
  omega

/-- LogUp: field sums with the interaction-count bound. -/
def Balance.logUp : Balance F where
  Balanced := LogUpBalanced
  balancedInteractions_of_balanced _ balanced :=
    ⟨ balanced.exists_push_of_pull, balanced.activeCount_push_eq_activeCount_pull_of_isBool ⟩

/-
## Multiset balance with `0`/`1` activations
-/

/--
Multiset balance: every multiplicity is `0` or `1`, and the messages of the active pushes are a
permutation of the messages of the active pulls. There are fewer interactions than field elements.
-/
def Balance.multiset : Balance F where
  Balanced interactions :=
    interactions.length < FiniteField.size F ∧ (∀ i ∈ interactions, IsBool i.mult) ∧
      (activeMessages interactions .push).Perm (activeMessages interactions .pull)
  balancedInteractions_of_balanced interactions h_check := by
    have counts (msg : Array F) :
        activeCount interactions .push msg = activeCount interactions .pull msg := by
      rw [← count_activeMessages, ← count_activeMessages]
      exact h_check.2.2.count_eq msg
    refine ⟨ ?_, fun msg _ => counts msg ⟩
    intro a a_mem a_pull
    have pull_pos : 0 < activeCount interactions .pull a.msg := by
      apply List.countP_pos_iff.mpr
      exact ⟨ a, a_mem, by simp [a_pull.1, a_pull.2] ⟩
    rw [← counts] at pull_pos
    obtain ⟨ b, b_mem, h_b ⟩ := List.countP_pos_iff.mp pull_pos
    simp only [decide_eq_true_eq] at h_b
    exact ⟨ b, b_mem, h_b.2.1, h_b.2.2, by simp [h_b.1] ⟩

/--
A balance check that bounds the number of interactions by the size of the field. Offline memory
checking relies on it to bound the number of reads of one address.
-/
class Balance.LengthLtSize (balance : Balance F) : Prop where
  length_lt_size : ∀ interactions,
    balance.Balanced interactions → interactions.length < FiniteField.size F

instance : (Balance.multiset (F := F)).LengthLtSize where
  length_lt_size _ balanced := balanced.1

instance {p : ℕ} [Fact p.Prime] : (Balance.logUp (F := _root_.F p)).LengthLtSize where
  length_lt_size _ balanced := by
    have : FiniteField.size (_root_.F p) = p := rfl
    simpa [Balance.logUp, ZMod.ringChar_zmod_n, this] using balanced.1

/- ## Conditions on channels that strengthen the implications of interaction balance. -/

namespace RawChannel
/--
We call a channel "consistent" if balancedness + requirements on all interacions
imply guarantees on all interactions.

This can be proved for individual channels without reference to any constraints,
essentially just means that reqs and grts are reasonably related.

For `Channel` it holds by definition, see `Normal` below.
-/
class Consistent (channel : RawChannel F) : Prop where
  consistent : ∀ (interactions : List (Interaction F)) (data : ProverData F),
    BalancedInteractions interactions →
    (∀ i ∈ interactions, i.channel = channel ∧ i.Requirements data) →
    (∀ i ∈ interactions, i.Guarantees data)

/--
A "normal" channel is one where
- the requirements of an interaction that provides a message imply the guarantees of a unit pull
  of the same message
- only unit pulls cause guarantees to be added
-/
class Normal (channel : RawChannel F) : Prop where
  guarantees_of_requirements : ∀ (a b : Interaction F) (data : ProverData F),
    a.channel = channel → b.channel = channel → a.msg = b.msg →
    a.Pull → b.Push → b.Requirements data → a.Guarantees data
  guarantees_of_not_pull : ∀ (a : Interaction F) (data : ProverData F),
    a.channel = channel → ¬a.Pull → a.Guarantees data

/-- Typed `Channel`s are normal by definition! -/
instance (channel : Channel F Message) : Normal channel.toRaw where
  guarantees_of_requirements := by
    rintro ⟨ _, a_direction, a_mult, a_msg, a_size ⟩ ⟨ _, b_direction, b_mult, b_msg, b_size ⟩
      data rfl rfl (rfl : a_msg = b_msg) a_pull ⟨ b_ne_zero, b_ne_one ⟩ b_reqs
    simp only [Interaction.Guarantees, Interaction.Requirements, Interaction.msgVector,
      Channel.toRaw] at b_reqs ⊢
    cases b_direction
    · exact fun _ _ => b_reqs b_ne_zero
    · exact absurd (b_reqs.resolve_left b_ne_zero) (b_ne_one rfl)
  guarantees_of_not_pull := by
    rintro ⟨ _, direction, mult, msg, size ⟩ data rfl not_pull
    simp only [Interaction.Pull, not_and] at not_pull
    simp only [Interaction.Guarantees, Channel.toRaw]
    exact fun h_direction h_mult => absurd h_mult (not_pull h_direction)

/-- Normal channels are consistent: every pull of one copy is matched by a push, whose requirements
give the guarantee. -/
theorem consistent_of_normal (channel : RawChannel F) [channel.Normal] :
    channel.Consistent := by
  constructor
  intro interactions data balance reqs a a_mem
  by_cases a_pull : a.Pull
  case neg => exact Normal.guarantees_of_not_pull a data (reqs a a_mem).1 a_pull
  obtain ⟨ b, b_mem, b_msg, b_push ⟩ := balance.exists_push_of_pull a a_mem a_pull
  exact Normal.guarantees_of_requirements a b data (reqs a a_mem).1 (reqs b b_mem).1 b_msg.symm
    a_pull b_push (reqs b b_mem).2

instance (channel : RawChannel F) [channel.Normal] : channel.Consistent :=
  consistent_of_normal channel
end RawChannel

/-
## Theory of "VM channels"

This section establishes a subtle soundness property for (normal) channels that
only ever emit multiplicity 1 or 0.

See `Vm.lean` for a detailed motivation and application of the main theorem,
`guarantees_of_requirements_of_requirements_of_guarantees`.
-/

-- Missing stlib lemma needed below
lemma List.countP_eraseIdx {α : Type} {l : List α} {p : α → Bool} {i : ℕ} (hi : i < l.length) :
    (l.eraseIdx i).countP p = l.countP p - (if p l[i] then 1 else 0) := by
  suffices (l.eraseIdx i).countP p + (if p l[i] then 1 else 0) = l.countP p by omega
  induction l generalizing i with
  | nil => nomatch hi
  | cons a l ih =>
    cases i with
    | zero => simp [countP_cons]
    | succ i =>
      simp only [eraseIdx_cons_succ, countP_cons, getElem_cons_succ]
      rw [← ih (Nat.lt_of_succ_lt_succ hi)]
      ring_nf

/--
Assume you have a list of channel interactions that is made up of pairs (pull_i, push_i) of one
copy of a message each, where for each i, `Guarantees pull_i → Requirements push_i`.
We want to think of (pull_i → push_i) as the state transition of a VM circuit.

Furthermore, assume every message is pulled as often as it is pushed, and the channel is normal.

Then, for any i, the **converse** is true: `Requirements push_i → Guarantees pull_i`.

The intuition is that when the requirements for a push hold unconditionally, we
can "follow implications around the cycle" to show that _all_ the guarantees/requirements must hold
(within that cycle, which contains both the push and its corresponding pull).

By narrowing the conclusion to only the guarantees of the push, the formulation cleverly
avoids talking about cycles at all, and achieves a comparatively simple proof by induction.
-/
theorem guarantees_of_requirements_of_requirements_of_guarantees
    (channel : RawChannel F) [channel.Normal]
    (pulls pushes : List (Interaction F))
    (count_eq : ∀ msg, pulls.countP (·.msg = msg) = pushes.countP (·.msg = msg))
    (data : ProverData F)
  -- same length
  (n : ℕ) (len_pulls : pulls.length = n) (len_pushes : pushes.length = n)
  -- all interactions are on the input channel
  (pulls_channel : ∀ a ∈ pulls, a.channel = channel) (pushes_channel : ∀ b ∈ pushes, b.channel = channel)
  -- every pull takes one copy of its message, and every push adds one copy
  (pulls_unit : ∀ a ∈ pulls, a.Pull)
  (pushes_unit : ∀ b ∈ pushes, b.direction = .push ∧ b.mult = 1) :
    (∀ (i : ℕ) (hi : i < n), pulls[i].Guarantees data → pushes[i].Requirements data) →
    ∀ (i : ℕ) (hi: i < n), pushes[i].Requirements data → pulls[i].Guarantees data := by
  intro constraints
  induction n generalizing pulls pushes with
  | zero => intro i hi; nomatch hi
  | succ n ih =>
    -- every pulled message is pushed
    have exists_push_of_pull : ∀ pull ∈ pulls, ∃ push ∈ pushes, push.msg = pull.msg := by
      intro pull pull_mem
      have : 0 < pushes.countP (·.msg = pull.msg) := by
        rw [← count_eq]
        exact List.countP_pos_iff.mpr ⟨ pull, pull_mem, by simp ⟩
      obtain ⟨ push, push_mem, h_msg ⟩ := List.countP_pos_iff.mp this
      exact ⟨ push, push_mem, by simpa using h_msg ⟩
    -- we identify the "previous" transition (pulls[j], pushes[j]) in the chain, where pushes[j] = pulls[i]
    intro i hi push_i_req
    have ⟨ push', push'_mem, push_j_msg ⟩ := exists_push_of_pull pulls[i] (List.getElem_mem ..)
    have ⟨ j, hj, hpush' ⟩ := List.getElem_of_mem push'_mem
    subst hpush'
    rw [len_pushes] at hj
    -- thanks to the channel being normal, it suffices to show the requirements of pushes[j]
    have push_j_imp_pull_i : pushes[j].Requirements data → pulls[i].Guarantees data := by
      have push_j_unit := pushes_unit pushes[j] (List.getElem_mem ..)
      apply RawChannel.Normal.guarantees_of_requirements pulls[i] pushes[j] data
        (pulls_channel _ (List.getElem_mem ..)) (pushes_channel _ (List.getElem_mem ..))
        push_j_msg.symm (pulls_unit _ (List.getElem_mem ..))
      simp [Interaction.Push, push_j_unit.1, push_j_unit.2]
    -- if i = j, we're done
    by_cases h_ij : j = i
    · subst h_ij; exact push_j_imp_pull_i push_i_req
    -- if i ≠ j, we can reduce our goal to a smaller list: the one where
    -- (pulls[j], pushes[j]) and (pulls[i], pushes[i]) are replaced with the single pair (pulls[j], pushes[i]).
    have pulls_j_imp_push_i : pulls[j].Guarantees data → pushes[i].Requirements data := fun j_grt =>
      j_grt |> constraints j hj |> push_j_imp_pull_i |> constraints i hi
    -- we remove (pulls[i], pushes[i]) and change pushes[j] to pushes[i]
    let j' := if j < i then j else j - 1
    let pulls' := pulls.eraseIdx i
    let pushes' := pushes.eraseIdx i |>.set j' pushes[i]
    have hj' : j' < n := by simp only [j']; split_ifs <;> omega
    have pulls'_len : pulls'.length = n := by simp [pulls', List.length_eraseIdx, len_pulls, hi]
    have pushes'_len : pushes'.length = n := by simp [pushes', List.length_eraseIdx, len_pushes, hi]
    have pulls'_getElem : pulls'[j'] = pulls[j] := by
      simp only [pulls', j', List.getElem_eraseIdx]
      split_ifs
      · simp
      · omega
      · simp [show j - 1 + 1 = j by omega]
    have pushes'_getElem : pushes'[j'] = pushes[i] := by simp [pushes', j']
    suffices push_i_imp_pull_j : pushes'[j'].Requirements data → pulls'[j'].Guarantees data by
      simp only [pulls'_getElem, pushes'_getElem] at push_i_imp_pull_j
      exact push_i_req |> push_i_imp_pull_j |> constraints j hj |> push_j_imp_pull_i
    -- we need to re-check all assumptions about pulls', pushes' for the induction hypothesis
    -- most of these are straightforward
    have pulls'_unit : ∀ a ∈ pulls', a.Pull := by
      simp only [pulls', List.forall_mem_iff_getElem, List.getElem_eraseIdx]
      intros; split_ifs <;> simp [*]
    have pushes'_unit : ∀ b ∈ pushes', b.direction = .push ∧ b.mult = 1 := by
      simp only [pushes', List.forall_mem_iff_getElem, List.getElem_eraseIdx, List.getElem_set]
      intros; split_ifs <;> simp [*]
    apply ih pulls' pushes' ?count_eq' pulls'_len pushes'_len ?pulls'_channel ?pushes'_channel
      pulls'_unit pushes'_unit ?constraints' j' hj'
    <;> clear ih
    case pulls'_channel | pushes'_channel =>
      simp only [pulls', pushes', List.forall_mem_iff_getElem, List.getElem_set, List.getElem_eraseIdx]
      intros; split_ifs <;> simp [*]
    case constraints' : ∀ i' (hi' : i' < n), pulls'[i'].Guarantees data → pushes'[i'].Requirements data := by
      intro i' hi'
      by_cases h_ij' : j' = i'
      · simp only [←h_ij', pulls'_getElem, pushes'_getElem]
        exact pulls_j_imp_push_i
      simp only [pulls', pushes', h_ij', List.getElem_eraseIdx, ne_eq, not_false_eq_true, List.getElem_set_ne]
      split_ifs <;> exact constraints _ (by linarith)
    -- it only remains to prove that counts still agree on pulls' and pushes'.
    -- at a high level, this is obvious because we removed two opposing elements with the same message
    -- (pushes[j] and pulls[i]), so counts for any message are unaffected.
    intro msg'
    have pushes_eq : pushes' = (pushes.set j pushes[i]).eraseIdx i := by
      simp [pushes', List.eraseIdx_set, j']
      split_ifs <;> (simp_all; try omega)
    simp only [pulls', pushes_eq]
    rw [List.countP_eraseIdx (by linarith)]
    rw [List.countP_eraseIdx (by simp_all), List.countP_set (len_pushes ▸ hj), push_j_msg]
    simp [h_ij, count_eq msg']

def activeInteractions (interactions : List (Interaction F)) : List (Interaction F) :=
  interactions.filter (fun i => i.mult ≠ 0)
lemma activeInteractions_length_eq {pulls pushes : List (Interaction F)}
    (h_len : pulls.length = pushes.length)
    (h_pair : ∀ i (hpi : i < pulls.length) (hqi : i < pushes.length),
      pulls[i].mult = 0 ↔ pushes[i].mult = 0) :
    (activeInteractions pulls).length = (activeInteractions pushes).length := by
  simp only [activeInteractions]
  induction pulls generalizing pushes with
  | nil =>
    cases pushes <;> simp at h_len ⊢
  | cons pull pulls ih =>
    cases pushes with
    | nil => simp at h_len
    | cons push pushes =>
      simp only [List.length_cons, Nat.succ.injEq] at h_len
      have h_pair_tail : ∀ i (hpi : i < pulls.length) (hqi : i < pushes.length),
          pulls[i].mult = 0 ↔ pushes[i].mult = 0 := by
        intro i hpi hqi
        exact h_pair (i + 1) (by simpa) (by simpa)
      specialize ih h_len h_pair_tail
      simp only [ne_eq, decide_not] at ih
      have h_pair_head : pull.mult = 0 ↔ push.mult = 0 := h_pair 0 (by simp) (by simp)
      by_cases h_pull : pull.mult = 0
      <;> simp [←h_pair_head, h_pull, ih]

lemma activePair_mem_zip {pulls pushes : List (Interaction F)}
    (h_len : pulls.length = pushes.length)
    (h_pair : ∀ i (hpi : i < pulls.length) (hqi : i < pushes.length),
      pulls[i].mult = 0 ↔ pushes[i].mult = 0)
    (i : ℕ) (hi : i < (activeInteractions pulls).length) :
    ((activeInteractions pulls)[i],
      (activeInteractions pushes)[i]'(activeInteractions_length_eq h_len h_pair ▸ hi))
      ∈ pulls.zip pushes := by
  induction pulls generalizing pushes i with
  | nil => simp [activeInteractions] at hi
  | cons pull pulls ih =>
    cases pushes with
    | nil => simp at h_len
    | cons push pushes =>
      simp only [List.length_cons, Nat.succ.injEq] at h_len
      have h_pair_tail : ∀ i (hpi : i < pulls.length) (hqi : i < pushes.length),
          pulls[i].mult = 0 ↔ pushes[i].mult = 0 := by
        intro i hpi hqi
        exact h_pair (i + 1) (by simpa) (by simpa)
      by_cases h_zero : pull.mult = 0
      · have h_push_zero : push.mult = 0 := (h_pair 0 (by simp) (by simp)).mp h_zero
        simp [activeInteractions, h_zero, h_push_zero] at hi ⊢
        have hi' : i < (activeInteractions pulls).length := by
          simpa [activeInteractions] using hi
        exact Or.inr (by
          simpa [activeInteractions] using ih h_len h_pair_tail i hi')
      · cases i with
        | zero =>
          have h_push_ne_zero : push.mult ≠ 0 := by
            intro h_push_zero
            exact h_zero ((h_pair 0 (by simp) (by simp)).mpr h_push_zero)
          simp [activeInteractions, h_zero, h_push_ne_zero]
        | succ i =>
          have h_push_ne_zero : push.mult ≠ 0 := by
            intro h_push_zero
            exact h_zero ((h_pair 0 (by simp) (by simp)).mpr h_push_zero)
          simp [activeInteractions, h_zero, h_push_ne_zero] at hi ⊢
          have hi' : i < (activeInteractions pulls).length := by
            simpa [activeInteractions] using hi
          exact Or.inr (by
            simpa [activeInteractions] using ih h_len h_pair_tail i hi')

lemma activeCount_append (as bs : List (Interaction F)) (direction : Direction) (msg : Array F) :
    activeCount (as ++ bs) direction msg = activeCount as direction msg + activeCount bs direction msg :=
  List.countP_append ..

lemma activeCount_eq_countP_activeInteractions {interactions : List (Interaction F)}
    {direction : Direction} (h_direction : ∀ i ∈ interactions, i.direction = direction)
    (msg : Array F) :
    activeCount interactions direction msg =
      (activeInteractions interactions).countP (·.msg = msg) := by
  simp only [activeCount, activeInteractions, List.countP_filter]
  apply List.countP_congr
  intro i hi
  simp [h_direction i hi]

lemma activeCount_eq_zero_of_direction_ne {interactions : List (Interaction F)}
    {direction : Direction} (h_direction : ∀ i ∈ interactions, i.direction ≠ direction)
    (msg : Array F) : activeCount interactions direction msg = 0 := by
  simp only [activeCount, List.countP_eq_zero, decide_eq_true_eq, not_and]
  exact fun i hi h => absurd h (h_direction i hi)

/--
Zero-padded variant of `guarantees_of_requirements_of_requirements_of_guarantees`.

The input lists may contain padded pull/push pairs with multiplicity `0`. The active
subsequence, where all multiplicities are `1`, satisfies the original VM theorem.
`0` multiplicities can be discarded as they don't affect balance.
-/
theorem guarantees_of_requirements_of_requirements_of_guarantees_of_mult_zero_iff
    (channel : RawChannel F) [channel.Normal]
    (pulls pushes : List (Interaction F))
    (balance : BalancedInteractions (pulls ++ pushes)) (data : ProverData F)
  -- same length before filtering
  (len_pulls_pushes : pulls.length = pushes.length)
  -- all interactions are on the input channel
  (pulls_channel : ∀ a ∈ pulls, a.channel = channel) (pushes_channel : ∀ b ∈ pushes, b.channel = channel)
  -- pulls and pushes are either active, with multiplicity `1`, or disabled
  (pulls_direction : ∀ a ∈ pulls, a.direction = .pull ∧ IsBool a.mult)
  (pushes_direction : ∀ b ∈ pushes, b.direction = .push ∧ IsBool b.mult)
  -- a pair is disabled on one side iff it is disabled on the other
  (pair_zero : ∀ i (hi_p : i < pulls.length) (hi_q : i < pushes.length),
    pulls[i].mult = 0 ↔ pushes[i].mult = 0) :
    (∀ (i : ℕ) (hi : i < (activeInteractions pulls).length),
      (activeInteractions pulls)[i].Guarantees data →
        ((activeInteractions pushes)[i]'(activeInteractions_length_eq len_pulls_pushes pair_zero ▸ hi)).Requirements data) →
    ∀ (i : ℕ) (hi : i < (activeInteractions pulls).length),
      ((activeInteractions pushes)[i]'(activeInteractions_length_eq len_pulls_pushes pair_zero ▸ hi)).Requirements data →
        (activeInteractions pulls)[i].Guarantees data := by
  intro constraints
  let active_pulls := activeInteractions pulls
  let active_pushes := activeInteractions pushes
  have count_eq : ∀ msg, active_pulls.countP (·.msg = msg) = active_pushes.countP (·.msg = msg) := by
    intro msg
    have pulls_ne_push : ∀ a ∈ pulls, a.direction ≠ .push := by
      intro a ha; simp [(pulls_direction a ha).1]
    have pushes_ne_pull : ∀ b ∈ pushes, b.direction ≠ .pull := by
      intro b hb; simp [(pushes_direction b hb).1]
    have counts := balance.activeCount_push_eq_activeCount_pull_of_isBool msg (by
      intro i hi _
      rcases List.mem_append.mp hi with hi | hi
      · exact (pulls_direction i hi).2
      · exact (pushes_direction i hi).2)
    simp only [activeCount_append] at counts
    show (activeInteractions pulls).countP _ = (activeInteractions pushes).countP _
    rw [activeCount_eq_zero_of_direction_ne pulls_ne_push,
      activeCount_eq_zero_of_direction_ne pushes_ne_pull,
      activeCount_eq_countP_activeInteractions (fun a ha => (pulls_direction a ha).1),
      activeCount_eq_countP_activeInteractions (fun b hb => (pushes_direction b hb).1)] at counts
    omega
  have active_pulls_channel : ∀ a ∈ active_pulls, a.channel = channel := by
    intro a ha
    simp only [active_pulls, activeInteractions, List.mem_filter] at ha
    exact pulls_channel a ha.1
  have active_pushes_channel : ∀ b ∈ active_pushes, b.channel = channel := by
    intro b hb
    simp only [active_pushes, activeInteractions, List.mem_filter] at hb
    exact pushes_channel b hb.1
  have active_pulls_unit : ∀ a ∈ active_pulls, a.Pull := by
    intro a ha
    simp only [active_pulls, activeInteractions, List.mem_filter, decide_eq_true_eq] at ha
    obtain ⟨ h_direction, h_mult ⟩ := pulls_direction a ha.1
    exact ⟨ h_direction, h_mult.resolve_left ha.2 ⟩
  have active_pushes_unit : ∀ b ∈ active_pushes, b.direction = .push ∧ b.mult = 1 := by
    intro b hb
    simp only [active_pushes, activeInteractions, List.mem_filter, decide_eq_true_eq] at hb
    obtain ⟨ h_direction, h_mult ⟩ := pushes_direction b hb.1
    exact ⟨ h_direction, h_mult.resolve_left hb.2 ⟩
  have active_len : active_pulls.length = active_pushes.length := by
    simpa [active_pulls, active_pushes] using
      activeInteractions_length_eq len_pulls_pushes pair_zero
  have theorem_active := guarantees_of_requirements_of_requirements_of_guarantees
    channel active_pulls active_pushes count_eq data active_pulls.length rfl active_len.symm
    active_pulls_channel active_pushes_channel active_pulls_unit active_pushes_unit
  have constraints' : ∀ (i : ℕ) (hi : i < active_pulls.length),
      active_pulls[i].Guarantees data → (active_pushes[i]'(by rw [← active_len]; exact hi)).Requirements data := by
    simpa [active_pulls, active_pushes] using constraints
  exact theorem_active constraints'
