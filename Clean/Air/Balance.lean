import Clean.Circuit

variable {F : Type} [FiniteField F] [DecidableEq F]
variable {Message : TypeMap} [ProvableType Message]

/-
## Channel balance

This module treats channel interactions as multisets and asks what properties can be
deduced from the condition of _balance_: that each element has multiplicity 0.
-/

/--
Balance of one element of an interaction list.
This is just multiplicity of the element when viewing the list as a multiset.
-/
def balanceOf (interactions : List (Interaction F)) (msg : Array F) : F :=
  interactions.filter (·.msg = msg) |>.map (·.mult) |>.sum

/--
Channel balance: for any message, the sum of multiplicities is 0.
We also require a side condition that ensures the interaction count does not overflow.
-/
def BalancedInteractions (interactions : List (Interaction F)) : Prop :=
  (interactions.length < ringChar F ∨ ringChar F = 0) ∧
  ∀ msg : Array F, balanceOf interactions msg = 0

lemma balanceOf_append {as bs : List (Interaction F)} {msg : Array F} :
    balanceOf (as ++ bs) msg = balanceOf as msg + balanceOf bs msg := by
  simp [balanceOf, List.filter_append, List.map_append, List.sum_append]

lemma balanceOf_cons {i : Interaction F} {is : List (Interaction F)} {msg : Array F} :
    balanceOf (i :: is) msg = (if i.msg = msg then i.mult else 0) + balanceOf is msg := by
  by_cases h : i.msg = msg <;> simp [balanceOf, h]

lemma balanceOf_perm {as bs : List (Interaction F)} {msg : Array F} :
    List.Perm as bs → balanceOf as msg = balanceOf bs msg := by
  intro perm
  apply List.Perm.sum_eq
  exact perm.filter (·.msg = msg) |>.map (·.mult)

/-- Balance is invariant under permutation of the interaction list. -/
lemma balancedInteractions_of_perm {as bs : List (Interaction F)} :
   BalancedInteractions as → List.Perm as bs → BalancedInteractions bs := by
  rintro ⟨ lt_ringChar, balance ⟩ perm
  constructor
  · simp_all [perm.length_eq]
  intro msg
  rw [← balanceOf_perm perm, balance]

lemma count_lt_ringChar_of_balancedInteractions {ins : List (Interaction F)} {msg : Array F} :
    BalancedInteractions ins → ins.countP (·.msg = msg) < ringChar F ∨ ringChar F = 0 := by
  intro ⟨ lt_ringChar, _ ⟩
  grw [List.countP_le_length]
  exact lt_ringChar

lemma List.countP_and_left_le {α : Type} (l : List α) (p q : α → Bool) :
    l.countP (fun x => p x && q x) ≤ l.countP p := by
  induction l with
  | nil => simp
  | cons a l ih =>
    by_cases hp : p a
    · by_cases hq : q a
      · simp [hp, hq, ih]
      · simp [hp, hq, ih.trans (Nat.le_add_right _ _)]
    · simp [hp, ih]

/--
Useful mechanical lemma: if all multiplicities for a given message are the same,
the balance sum can be written as multiplicity times message count.
-/
lemma balanceOf_eq_of_const_mult {interactions : List (Interaction F)} {msg : Array F} {mult : F} :
    (∀ i ∈ interactions, i.msg = msg → i.mult = mult) →
    balanceOf interactions msg = mult * ↑(interactions.countP (·.msg = msg)) := by
  intro constant_mult
  set count : ℕ := interactions.countP (·.msg = msg)
  suffices (interactions.filter (·.msg = msg)).map (·.mult) = List.replicate count mult by
    convert (congrArg List.sum this)
    simp [mul_comm]
  apply List.ext_getElem
  · simp [count, List.countP_eq_length_filter]
  intro i hi hi'
  simp only [List.getElem_map, List.getElem_replicate]
  rw [List.length_map] at hi
  set a := (interactions.filter (·.msg = msg))[i] with ha
  have a_mem_filter : a ∈ interactions.filter (·.msg = msg) := by simp [a]
  simp only [List.mem_filter, decide_eq_true_eq] at a_mem_filter
  apply constant_mult a <;> simp_all

/--
Special case of `balanceOf_eq_of_const_mult` for when the exact message doesn't matter.
-/
lemma balanceOf_eq_of_const_mult' {interactions : List (Interaction F)} {msg : Array F} {mult : F} :
    (∀ i ∈ interactions, i.mult = mult) →
    balanceOf interactions msg = mult * ↑(interactions.countP (·.msg = msg)) :=
  fun constant_mult => balanceOf_eq_of_const_mult (fun i hi _ => constant_mult i hi)

lemma balanceOf_eq_of_const_zero {interactions : List (Interaction F)} {msg : Array F} :
    (∀ i ∈ interactions, i.mult = 0) → balanceOf interactions msg = 0 := by
  intro const_zero
  rw [balanceOf_eq_of_const_mult' const_zero]
  simp

lemma balanceOf_eq_add_filter {interactions : List (Interaction F)} {msg : Array F} (p : F → Prop) [DecidablePred p] :
    balanceOf interactions msg =
      balanceOf (interactions.filter (fun i => decide (p i.mult))) msg
      + balanceOf (interactions.filter (fun i => decide (¬p i.mult))) msg := by
  simp only [balanceOf, List.filter_filter]
  conv in _ && decide (p _) => rw [Bool.and_comm]
  conv in _ && decide (¬ p _) => rw [Bool.and_comm]
  simp_rw [← List.filter_filter]
  rw [List.sum_map_filter_add_sum_map_filter_not]

lemma balanceOf_eq_filter_ne_zero {interactions : List (Interaction F)} {msg : Array F} :
    balanceOf interactions msg =
      (interactions.filter (fun i => i.msg = msg && i.mult ≠ 0) |>.map (·.mult) |>.sum) := by
  rw [balanceOf_eq_add_filter (· = 0)]
  simp only [balanceOf, List.filter_filter, decide_not, ne_eq, add_eq_right]
  simp_rw [←List.filter_filter]
  set l := interactions.filter (·.mult = 0) with hl
  show balanceOf l msg = 0
  apply balanceOf_eq_of_const_zero
  grind

/--
If every interaction for `msg` has multiplicity either nonzero `mult` or `0`, the
balance is `mult` times the count of the `mult` interactions. This is the zero-padding
variant of `balanceOf_eq_of_const_mult`.
-/
lemma balanceOf_eq_of_mult_or_zero
    {interactions : List (Interaction F)} {msg : Array F} {mult : F} :
    (∀ i ∈ interactions, i.msg = msg → i.mult ≠ 0 → i.mult = mult) →
    balanceOf interactions msg =
      mult * ↑(interactions.countP fun i => i.msg = msg && i.mult ≠ 0) := by
  intro constant_mult
  set count : ℕ := interactions.countP fun i => i.msg = msg && i.mult ≠ 0
  suffices (interactions.filter (fun i => i.msg = msg && i.mult ≠ 0)).map (·.mult) = List.replicate count mult by
    rw [balanceOf_eq_filter_ne_zero]
    convert (congrArg List.sum this)
    simp [mul_comm]
  apply List.ext_getElem
  · simp [count, List.countP_eq_length_filter]
  intro i hi hi'
  simp only [List.getElem_map, List.getElem_replicate]
  rw [List.length_map] at hi
  set a := (interactions.filter (fun i ↦ decide (i.msg = msg) && decide (i.mult ≠ 0)))[i] with ha
  have a_mem_filter : a ∈ interactions.filter (fun i ↦ decide (i.msg = msg) && decide (i.mult ≠ 0)) := by simp [a]
  simp [List.mem_filter] at a_mem_filter
  apply constant_mult a <;> simp_all

/--
If an interaction list is balanced, then for every pull there must be a corresponding "push",
where "push" means an interaction with multiplicity neither `-1` nor `0`.
-/
theorem exists_push_of_pull (interactions : List (Interaction F)) (balance : BalancedInteractions interactions) :
    ∀ a ∈ interactions, a.mult = -1 → ∃ b ∈ interactions, b.msg = a.msg ∧ b.mult ≠ 0 ∧ b.mult ≠ -1 := by
  intro a h_mem_a h_pull
  set msg := a.msg
  set count : ℕ := interactions.countP fun i => i.msg = msg && i.mult ≠ 0
  have count_lt_ringChar : count < ringChar F ∨ ringChar F = 0 := by
    simp only [count]
    grw [List.countP_le_length]
    exact balance.1
  replace balance := balance.2 msg
  -- assuming no such push exists => all interactions with the same message have multiplicity -1 or 0
  -- this leads to a contradiction with the 0 balance + no overflow
  by_contra! const_minus_one
  suffices count = 0 by
    simp only [count, msg, List.countP_eq_zero, Bool.and_eq_true, decide_eq_true_eq, not_and] at this
    apply this a h_mem_a rfl
    show a.mult ≠ 0
    rw [h_pull, ne_eq, neg_eq_zero]
    exact one_ne_zero
  rw [balanceOf_eq_of_mult_or_zero const_minus_one] at balance
  simp only [neg_mul, one_mul, neg_eq_zero] at balance
  change (count : F) = 0 at balance
  rcases count_lt_ringChar with count_lt_ringChar | ringChar_zero
  · simp_all [Lean.Grind.IsCharP.natCast_eq_zero_iff_of_lt _ count_lt_ringChar]
  · simp_all [CharP.ringChar_zero_iff_CharZero]

/- ## Conditions on channels that strengthen the implications of interaction balance. -/

namespace RawChannel
/--
We call a channel "consistent" if balancedness + requirements on all interacions
imply guarantees on all interactions.

This can be proved for individual channels without reference to any constraints,
essentially just means that reqs and grts are reasonably related.

For `Channel` it holds by definition, see `NormalChannel` below.
-/
class Consistent (channel : RawChannel F) : Prop where
  consistent : ∀ (interactions : List (Interaction F)) (data : ProverData F),
    BalancedInteractions interactions →
    (∀ i ∈ interactions, i.channel = channel ∧ i.Requirements data) →
    (∀ i ∈ interactions, i.Guarantees data)

/--
A "normal" channel is one where
- the requirements for a push interaction imply the guarantees of the corresponding pull interaction
- only pull interactions cause guarantees to be added
-/
class Normal (channel : RawChannel F) : Prop where
  grts_of_reqs : ∀ (msg : Vector F channel.arity) (mult : F) data, mult ≠ 0 → mult ≠ -1 →
    channel.Requirements mult msg data → channel.Guarantees (-1) msg data
  grts_of_ne_neg_one : ∀ (msg : Vector F channel.arity) (mult : F) data, mult ≠ -1 →
    channel.Guarantees mult msg data

/-- Typed `Channel`s are normal by definition! -/
instance (channel : Channel F Message) : Normal channel.toRaw where
  grts_of_reqs := by
    intro msg mult data mult_ne_zero mult_ne_neg_one reqs
    simp [Channel.toRaw, mult_ne_zero, mult_ne_neg_one] at reqs ⊢
    exact reqs
  grts_of_ne_neg_one := by
    intro msg mult data mult_ne_neg_one
    simp [Channel.toRaw, mult_ne_neg_one]

/-- Normal channels are consistent, thanks to `exists_push_of_pull` -/
theorem consistent_of_normal (channel : RawChannel F) [channel.Normal] :
    channel.Consistent := by
  constructor
  intro interactions data balance reqs a a_mem
  simp only [Interaction.Guarantees, Interaction.Requirements, Interaction.msgVector] at reqs ⊢
  intro _
  have a_channel_eq := reqs a a_mem |>.left
  have a_msg_size : a.msg.size = channel.arity := by rw [a.same_size, a_channel_eq]
  -- we need to prove the guarantees for a given interaction from the requirements of _all_ interactions
  suffices channel.Guarantees a.mult ⟨ a.msg, a_msg_size ⟩ data by convert this
  by_cases a_mult : a.mult = -1
  -- if the multiplitity is not -1, this is trivial by `grts_of_ne_neg_one`
  case neg => exact RawChannel.Normal.grts_of_ne_neg_one ⟨ a.msg, a_msg_size ⟩ a.mult data a_mult
  -- if the multiplicity is -1, we get the corresponding push interaction and apply `grts_of_reqs`
  rw [a_mult]
  have ⟨ b, b_mem, b_msg_eq, b_mult_ne_neg_one, b_mult_ne_zero ⟩ :=
    exists_push_of_pull interactions balance a a_mem a_mult
  apply RawChannel.Normal.grts_of_reqs ⟨ a.msg, a_msg_size ⟩ b.mult data b_mult_ne_neg_one b_mult_ne_zero
  have ⟨ b_channel_eq, b_reqs ⟩ := reqs _ b_mem
  symm at b_channel_eq
  simp only [b_msg_eq] at b_reqs
  convert b_reqs

instance (channel : RawChannel F) [channel.Normal] : channel.Consistent :=
  consistent_of_normal channel
end RawChannel

/-
## Theory of "VM channels"

This section establishes a subtle soundness property for (normal) channels that
only ever emit 1 or -1 multiplicities.

See `Vm.lean` for a detailed motivation and application of the main theorem,
`guarantees_of_requirements_of_requirements_of_guarantees`.
-/

omit [DecidableEq F] in
lemma one_ne_neg_one [Fact (ringChar F ≠ 2)] : (1 : F) ≠ -1 :=
  Ne.symm (Ring.neg_one_ne_one_of_char_ne_two ‹Fact (ringChar F ≠ 2)›.out)

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
      ring

/--
Assume you have a list of channel interactions that is made up of pairs (-1, pull_i), (1, push_i),
where for each i, `Guarantees (-1, pull_i) → Requirements (1, push_i)`.
We want to think of (pull_i → push_i) as the state transition of a VM circuit.

Furthermore, assume the list is balanced and the channel is normal.

Then, for any i, the **converse** is true: `Requirements (1, push_i) → Guarantees (-1, pull_i)`.

The intuition is that when the requirements for a push hold unconditionally, we
can "follow implications around the cycle" to show that _all_ the guarantees/requirements must hold
(within that cycle, which contains both the push and its corresponding pull).

By narrowing the conclusion to only the guarantees of the push, the formulation cleverly
avoids talking about cycles at all, and achieves a comparatively simple proof by induction.
-/
theorem guarantees_of_requirements_of_requirements_of_guarantees [Fact (ringChar F ≠ 2)]
    (channel : RawChannel F) [channel.Normal]
    (pulls pushes : List (Interaction F))
    (balance : BalancedInteractions (pulls ++ pushes)) (data : ProverData F)
  -- same length
  (n : ℕ) (len_pulls : pulls.length = n) (len_pushes : pushes.length = n)
  -- all interactions are on the input channel
  (pulls_channel : ∀ a ∈ pulls, a.channel = channel) (pushes_channel : ∀ b ∈ pushes, b.channel = channel)
  -- the multiplicities are -1 for pulls and 1 for pushes
  (pulls_mult : ∀ a ∈ pulls, a.mult = -1) (pushes_mult : ∀ b ∈ pushes, b.mult = 1) :
    (∀ (i : ℕ) (hi : i < n), pulls[i].Guarantees data → pushes[i].Requirements data) →
    ∀ (i : ℕ) (hi: i < n), pushes[i].Requirements data → pulls[i].Guarantees data := by
  intro constraints
  induction n generalizing pulls pushes with
  | zero => intro i hi; nomatch hi
  | succ n ih =>
    -- first, a little inline version of `exists_push_of_pull`
    have exists_push_of_pull : ∀ pull ∈ pulls, ∃ push ∈ pushes, push.msg = pull.msg := by
      intro pull pull_mem
      have pull_mem_append : pull ∈ pulls ++ pushes := by simp [pull_mem]
      have ⟨ push, push_mem, push_msg_eq, push_mult_ne_neg_one, _ ⟩ := exists_push_of_pull (pulls ++ pushes)
        balance pull pull_mem_append (pulls_mult pull pull_mem)
      have push_mem : push ∈ pushes := by simp only [List.mem_append] at push_mem; tauto
      exists push
    -- we identify the "previous" transition (pulls[j], pushes[j]) in the chain, where pushes[j] = pulls[i]
    intro i hi push_i_req
    have ⟨ push', push'_mem, push_j_msg ⟩ := exists_push_of_pull pulls[i] (List.getElem_mem ..)
    set msg := pulls[i].msg with pull_i_msg
    have ⟨ j, hj, hpush' ⟩ := List.getElem_of_mem push'_mem
    subst hpush'
    rw [len_pushes] at hj
    -- thanks to the channel being consistent, it suffices to show the requirements of pushes[j]
    have push_j_imp_pull_i : pushes[j].Requirements data → pulls[i].Guarantees data := by
      intro push_j_req
      have pulls_i_channel := pulls_channel pulls[i] (List.getElem_mem ..)
      have pushes_j_channel := pushes_channel pushes[j] (List.getElem_mem ..) |>.symm
      have pulls_i_mult := pulls_mult pulls[i] (List.getElem_mem ..)
      have pushes_j_mult := pushes_mult pushes[j] (List.getElem_mem ..) |>.symm
      have msg_size : msg.size = channel.arity := by rw [pulls[i].same_size, pulls_i_channel]
      suffices grt' : channel.Guarantees (-1) ⟨ msg, msg_size ⟩ data by
        simp only [Interaction.Guarantees]
        convert fun _ => grt'
      apply RawChannel.Normal.grts_of_reqs ⟨ msg, msg_size ⟩ 1 data one_ne_zero one_ne_neg_one
      simp only [Interaction.Requirements, Interaction.msgVector, push_j_msg] at push_j_req
      convert push_j_req
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
    -- we need to re-check all assumptions about as', bs' for the induction hypothesis
    -- most of these are straightforward
    have pulls'_mult : ∀ a ∈ pulls', a.mult = -1 := by
      simp only [pulls', List.forall_mem_iff_getElem, List.getElem_eraseIdx]
      intros; split_ifs <;> simp [*]
    have pushes'_mult : ∀ b ∈ pushes', b.mult = 1 := by
      simp only [pushes', List.forall_mem_iff_getElem, List.getElem_eraseIdx, List.getElem_set]
      intros; split_ifs <;> simp [*]
    apply ih pulls' pushes' ?balance' pulls'_len pushes'_len ?pulls'_channel ?pushes'_channel pulls'_mult pushes'_mult ?constraints' j' hj'
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
    -- it only remains to prove the balance condition for pulls' ++ pushes'.
    -- at a high level, this is obvious because we removed two opposing elements with the same message
    -- (pushes[j] and pulls[i]), so balance for any message is unaffected.
    rcases balance with ⟨ lt_ringChar, balance ⟩
    simp only [len_pulls, len_pushes, List.length_append] at lt_ringChar
    constructor
    · simp only [pulls'_len, pushes'_len, List.length_append]
      rcases lt_ringChar with lt_ringChar | ringChar_zero
      · left; linarith
      · right; assumption
    intro msg'
    specialize balance msg'
    simp only [balanceOf_append] at balance ⊢
    rw [balanceOf_eq_of_const_mult' pulls_mult, balanceOf_eq_of_const_mult' pushes_mult] at balance
    rw [balanceOf_eq_of_const_mult' pulls'_mult, balanceOf_eq_of_const_mult' pushes'_mult]
    simp only [neg_mul, one_mul, neg_add_eq_zero] at balance ⊢
    have count_eq : pulls.countP (·.msg = msg') = pushes.countP (·.msg = msg') := by
      rcases lt_ringChar with lt_ringChar | ringChar_zero
      · have a_lt_ringChar : pulls.countP (·.msg = msg') < ringChar F := by
          grw [List.countP_le_length, len_pulls, Nat.le_add_right (n + 1) (n + 1)]
          exact lt_ringChar
        have b_lt_ringChar : pushes.countP (·.msg = msg') < ringChar F := by
          grw [List.countP_le_length, len_pushes, Nat.le_add_right (n + 1) (n + 1)]
          exact lt_ringChar
        rw [Lean.Grind.IsCharP.natCast_eq_iff_of_lt _ a_lt_ringChar b_lt_ringChar] at balance
        exact balance
      · rw [CharP.ringChar_zero_iff_CharZero] at ringChar_zero
        rw [Nat.cast_inj] at balance
        exact balance
    have pushes_eq : pushes' = (pushes.set j pushes[i]).eraseIdx i := by
      simp [pushes', List.eraseIdx_set, j']
      split_ifs <;> (simp_all; try omega)
    simp only [pulls', pushes_eq]
    rw [List.countP_eraseIdx (by linarith), ←pull_i_msg]
    rw [List.countP_eraseIdx (by simp_all), List.countP_set (len_pushes ▸ hj), push_j_msg]
    simp [h_ij, count_eq]

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

lemma balanceOf_active_append_eq {pulls pushes : List (Interaction F)} {msg : Array F}
    (h_len : pulls.length = pushes.length)
    (h_pair : ∀ i (hpi : i < pulls.length) (hqi : i < pushes.length),
      pulls[i].mult = 0 ↔ pushes[i].mult = 0) :
    balanceOf (activeInteractions pulls ++ activeInteractions pushes) msg =
      balanceOf (pulls ++ pushes) msg := by
  induction pulls generalizing pushes with
  | nil =>
    cases pushes <;> simp [activeInteractions, balanceOf] at h_len ⊢
  | cons pull pulls ih =>
    cases pushes with
    | nil => simp at h_len
    | cons push pushes =>
      simp only [List.length_cons, Nat.succ.injEq] at h_len
      have h_pair_tail : ∀ i (hpi : i < pulls.length) (hqi : i < pushes.length),
          pulls[i].mult = 0 ↔ pushes[i].mult = 0 := by
        intro i hpi hqi
        exact h_pair (i+1) (by simpa) (by simpa)
      have ih' := ih h_len h_pair_tail
      by_cases h_zero : pull.mult = 0
      · have h_push_zero : push.mult = 0 := (h_pair 0 (by simp) (by simp)).mp h_zero
        simp [activeInteractions, h_zero, h_push_zero, balanceOf_append,
          balanceOf_cons] at ih' ⊢
        exact ih'
      · have h_push_ne_zero : push.mult ≠ 0 := by
          intro h_push_zero
          exact h_zero ((h_pair 0 (by simp) (by simp)).mpr h_push_zero)
        simp [activeInteractions, h_zero, h_push_ne_zero, balanceOf_append,
          balanceOf_cons] at ih' ⊢
        ring_nf at ih' ⊢
        exact congrArg (fun x => x + if push.msg = msg then push.mult else 0) ih'

lemma balancedInteractions_active_append {pulls pushes : List (Interaction F)}
    (balance : BalancedInteractions (pulls ++ pushes))
    (h_len : pulls.length = pushes.length)
    (h_pair : ∀ i (hpi : i < pulls.length) (hqi : i < pushes.length),
      pulls[i].mult = 0 ↔ pushes[i].mult = 0) :
    BalancedInteractions (activeInteractions pulls ++ activeInteractions pushes) := by
  constructor
  · rcases balance.1 with h_lt | h_char
    · left
      have h_len_pulls : (activeInteractions pulls).length ≤ pulls.length := by
        rw [activeInteractions]
        have h := pulls.length_eq_length_filter_add (fun i => i.mult ≠ 0)
        omega
      have h_len_pushes : (activeInteractions pushes).length ≤ pushes.length := by
        rw [← activeInteractions_length_eq h_len h_pair, ← h_len]
        exact h_len_pulls
      simp only [List.length_append] at h_lt ⊢
      omega
    · right
      exact h_char
  · intro msg
    rw [balanceOf_active_append_eq h_len h_pair]
    exact balance.2 msg

/--
Zero-padded variant of `guarantees_of_requirements_of_requirements_of_guarantees`.

The input lists may contain padded pull/push pairs with multiplicity `0`. The active
subsequence, where pull multiplicity is `-1` and push multiplicity is `1`, satisfies
the original VM theorem. `0` multiplicities can be discarded as they don't affect balance.
-/
theorem guarantees_of_requirements_of_requirements_of_guarantees_of_mult_zero_iff [Fact (ringChar F ≠ 2)]
    (channel : RawChannel F) [channel.Normal]
    (pulls pushes : List (Interaction F))
    (balance : BalancedInteractions (pulls ++ pushes)) (data : ProverData F)
  -- same length before filtering
  (len_pulls_pushes : pulls.length = pushes.length)
  -- all interactions are on the input channel
  (pulls_channel : ∀ a ∈ pulls, a.channel = channel) (pushes_channel : ∀ b ∈ pushes, b.channel = channel)
  -- pulls are either active `-1` pulls or disabled, pushes are either active `1` pushes or disabled
  (pulls_mult : ∀ a ∈ pulls, a.mult = 0 ∨ a.mult = -1)
  (pushes_mult : ∀ b ∈ pushes, b.mult = 0 ∨ b.mult = 1)
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
  have active_balance : BalancedInteractions (active_pulls ++ active_pushes) := by
    simpa [active_pulls, active_pushes] using
      balancedInteractions_active_append balance len_pulls_pushes pair_zero
  have active_pulls_channel : ∀ a ∈ active_pulls, a.channel = channel := by
    intro a ha
    simp only [active_pulls, activeInteractions, List.mem_filter] at ha
    exact pulls_channel a ha.1
  have active_pushes_channel : ∀ b ∈ active_pushes, b.channel = channel := by
    intro b hb
    simp only [active_pushes, activeInteractions, List.mem_filter] at hb
    exact pushes_channel b hb.1
  have active_pulls_mult : ∀ a ∈ active_pulls, a.mult = -1 := by
    intro a ha
    simp only [active_pulls, activeInteractions, List.mem_filter] at ha
    have a_mult_ne_zero : a.mult ≠ 0 := by simpa using ha.2
    rcases pulls_mult a ha.1 with h_mult | h_mult
    · contradiction
    · exact h_mult
  have active_pushes_mult : ∀ b ∈ active_pushes, b.mult = 1 := by
    intro b hb
    simp only [active_pushes, activeInteractions, List.mem_filter] at hb
    have b_mult_ne_zero : b.mult ≠ 0 := by simpa using hb.2
    rcases pushes_mult b hb.1 with h_mult | h_mult
    · contradiction
    · exact h_mult
  have active_len : active_pulls.length = active_pushes.length := by
    simpa [active_pulls, active_pushes] using
      activeInteractions_length_eq len_pulls_pushes pair_zero
  have theorem_active := guarantees_of_requirements_of_requirements_of_guarantees
    channel active_pulls active_pushes active_balance data active_pulls.length rfl active_len.symm
    active_pulls_channel active_pushes_channel active_pulls_mult active_pushes_mult
  have constraints' : ∀ (i : ℕ) (hi : i < active_pulls.length),
      active_pulls[i].Guarantees data → (active_pushes[i]'(by rw [← active_len]; exact hi)).Requirements data := by
    simpa [active_pulls, active_pushes] using constraints
  exact theorem_active constraints'
