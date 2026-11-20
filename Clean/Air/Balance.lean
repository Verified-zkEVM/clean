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
/-- A pull of multiplicity `1`: the interactions that typed channels give their guarantee. -/
def Pull (i : Interaction F) : Prop := i.direction = .pull ∧ i.mult = 1

/--
An interaction that pushes its message: an active push, or a pull of multiplicity other than `0` or
`1`, which acts as a push under field-sum balance.
-/
def Push (i : Interaction F) : Prop := i.mult ≠ 0 ∧ (i.direction = .pull → i.mult ≠ 1)

/-- Every interaction is in exactly one of three cases: inactive (`mult = 0`), a `Pull`, or a
`Push`. -/
lemma not_push_iff {i : Interaction F} : ¬i.Push ↔ i.mult = 0 ∨ i.Pull := by
  simp only [Push, Pull, not_and, Classical.not_imp]
  tauto
end Interaction

/-- The number of active interactions in a direction that carry a message. -/
def activeCount (interactions : List (Interaction F)) (direction : Channel.Direction)
    (msg : Array F) : ℕ :=
  interactions.countP fun i => i.direction = direction ∧ i.msg = msg ∧ i.mult ≠ 0

/-- The messages of the active interactions in a direction. -/
def activeMessages (interactions : List (Interaction F)) (direction : Channel.Direction) :
    List (Array F) :=
  (interactions.filter fun i => i.direction = direction ∧ i.mult ≠ 0).map (·.msg)

lemma count_activeMessages (interactions : List (Interaction F)) (direction : Channel.Direction)
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
- a pull of multiplicity `1` is matched by a push of its message, and
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
A balance check: the condition that a verifier checks on the interactions with each channel, the
numbers of interactions with a channel that the check is sound for, and its proof that the condition
implies `BalancedInteractions` for those.
-/
structure Balance (F : Type) [FiniteField F] where
  Balanced : List (Interaction F) → Prop
  fits : ℕ → Bool
  balancedInteractions_of_balanced : ∀ interactions, fits interactions.length →
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
LogUp balance: for every message, the signed multiplicities sum to zero.
-/
def LogUpBalanced (interactions : List (Interaction F)) : Prop :=
  ∀ msg, balanceOf interactions msg = 0

/-- If all interactions carrying a message have multiplicity `0` or `1`, it is pushed and pulled
equally often, as long as there are fewer interactions than the characteristic, so that counts
can't wrap around. -/
theorem LogUpBalanced.activeCount_push_eq_activeCount_pull_of_isBool
    {interactions : List (Interaction F)} (length_lt : interactions.length < ringChar F)
    (sums : LogUpBalanced interactions) (msg : Array F)
    (isBool : ∀ i ∈ interactions, i.msg = msg → IsBool i.mult) :
    activeCount interactions .push msg = activeCount interactions .pull msg := by
  have activeCount_lt (direction : Channel.Direction) :
      activeCount interactions direction msg < ringChar F :=
    lt_of_le_of_lt (List.countP_le_length) length_lt
  have sum := sums msg
  rw [balanceOf_eq_sub_of_isBool isBool, sub_eq_zero,
    Lean.Grind.IsCharP.natCast_eq_iff_of_lt _ (activeCount_lt _) (activeCount_lt _)] at sum
  exact sum

/-- Every pull of multiplicity `1` is matched by a push of its message, if there are fewer
interactions than the characteristic. -/
theorem LogUpBalanced.exists_push_of_pull {interactions : List (Interaction F)}
    (length_lt : interactions.length < ringChar F) (balanced : LogUpBalanced interactions) :
    ∀ a ∈ interactions, a.Pull → ∃ b ∈ interactions, b.msg = a.msg ∧ b.Push := by
  intro a a_mem a_pull
  -- assuming no such push exists, all interactions with the message are pulls of multiplicity `1`
  -- or inactive, so balance says that there are none
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
  have := balanced.activeCount_push_eq_activeCount_pull_of_isBool length_lt a.msg isBool
  omega

/-- LogUp: field sums, sound for fewer interactions than the characteristic. -/
def Balance.logUp [ComputableRingChar F] : Balance F where
  Balanced := LogUpBalanced
  fits count := count < ComputableRingChar.char F
  balancedInteractions_of_balanced _ fits balanced :=
    have length_lt := ComputableRingChar.char_eq (R := F) ▸ of_decide_eq_true fits
    ⟨ balanced.exists_push_of_pull length_lt,
      balanced.activeCount_push_eq_activeCount_pull_of_isBool length_lt ⟩

/-
## Multiset balance with `0`/`1` activations
-/

/--
Multiset balance: every multiplicity is `0` or `1`, and the messages of the active pushes are a
permutation of the messages of the active pulls. The permutation gives equal counts for any number
of interactions; the soundness error of a randomized check of it, like a product argument, is up to
the proof system.
-/
def Balance.multiset : Balance F where
  Balanced interactions :=
    (∀ i ∈ interactions, IsBool i.mult) ∧
      (activeMessages interactions .push).Perm (activeMessages interactions .pull)
  fits _ := true
  balancedInteractions_of_balanced interactions _ h_check := by
    have counts (msg : Array F) :
        activeCount interactions .push msg = activeCount interactions .pull msg := by
      rw [← count_activeMessages, ← count_activeMessages]
      exact h_check.2.count_eq msg
    refine ⟨ ?_, fun msg _ => counts msg ⟩
    intro a a_mem a_pull
    have pull_pos : 0 < activeCount interactions .pull a.msg := by
      apply List.countP_pos_iff.mpr
      exact ⟨ a, a_mem, by simp [a_pull.1, a_pull.2] ⟩
    rw [← counts] at pull_pos
    obtain ⟨ b, b_mem, h_b ⟩ := List.countP_pos_iff.mp pull_pos
    simp only [decide_eq_true_eq] at h_b
    exact ⟨ b, b_mem, h_b.2.1, h_b.2.2, by simp [h_b.1] ⟩

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

/-- Normal channels are consistent: every pull of multiplicity `1` is matched by a push, whose requirements
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

A VM performs one transition per row: it pulls a state from a channel and pushes the next state.
This section shows how balance turns these local transitions into a global statement: a pulled state
is reached from a pushed one, by a chain of transitions that is no longer than the list of all
transitions.

See `Vm.lean` for the application to VM ensembles.
-/

/--
Assume a list of transitions `(pull_i, push_i)`, each of which takes a message reached after `k`
steps to a message reached after `k + 1` steps, and one more pair `(pull, push)`, such that the
pulled messages are a permutation of the pushed messages.

Then, if `push` is reached after `k` steps, `pull` is reached after at most `k + n` steps, where `n`
is the number of transitions.

The intuition is that we can follow transitions backwards from `pull`: it is pushed by `push` itself
or by a transition, whose pulled message is in turn pushed by `push` or another transition, and so
on. Every transition is used at most once, so we arrive at `push` after at most `n` transitions.

The formulation avoids talking about chains, and achieves a simple proof by induction: a transition
that pushes `pull` can be merged with the pair `(pull, push)`.
-/
theorem exists_reached_of_perm {α : Type} (Reached : ℕ → α → Prop)
    (transitions : List (α × α))
    (step : ∀ t ∈ transitions, ∀ k, Reached k t.1 → Reached (k + 1) t.2)
    (pull push : α) (perm : (pull :: transitions.map (·.1)).Perm (push :: transitions.map (·.2)))
    (k : ℕ) (reached : Reached k push) :
    ∃ k' ≤ k + transitions.length, Reached k' pull := by
  obtain ⟨n, len⟩ : ∃ n, transitions.length = n := ⟨_, rfl⟩
  induction n generalizing transitions pull with
  | zero =>
    simp only [List.length_eq_zero_iff] at len
    subst len
    simp only [List.map_nil, List.perm_singleton, List.cons.injEq, and_true] at perm
    exact ⟨k, by simp, perm ▸ reached⟩
  | succ n ih =>
    by_cases pull_eq : pull = push
    · exact ⟨k, by omega, pull_eq ▸ reached⟩
    -- `pull` is pushed by a transition `t`
    have pull_mem : pull ∈ transitions.map (·.2) := by
      have := perm.subset List.mem_cons_self
      simp only [List.mem_cons, pull_eq, false_or] at this
      exact this
    obtain ⟨t, t_mem, rfl⟩ := List.mem_map.mp pull_mem
    -- we merge `t` with `(t.2, push)` into `(t.1, push)`
    obtain ⟨s, u, rfl⟩ := List.append_of_mem t_mem
    have rest_perm : (t.1 :: (s ++ u).map (·.1)).Perm (push :: (s ++ u).map (·.2)) := by
      have h_perm := (List.perm_middle (l₁ := s) (l₂ := u) (a := t))
      have := ((h_perm.map (·.1)).cons t.2).symm.trans perm |>.trans ((h_perm.map (·.2)).cons push)
      simp only [List.map_cons] at this
      exact (this.trans (List.Perm.swap t.2 push _)).cons_inv
    obtain ⟨k', hk', reached'⟩ := ih (s ++ u)
      (fun t' t'_mem => step t' (by simp only [List.mem_append, List.mem_cons] at t'_mem ⊢; tauto))
      t.1 rest_perm (by simp only [List.length_append, List.length_cons] at len ⊢; omega)
    exact ⟨k' + 1, by simp only [List.length_append, List.length_cons] at hk' ⊢; omega,
      step t t_mem k' reached'⟩

/-- Concatenation of a list of pairs. -/
def List.flattenPairs {α : Type} (pairs : List (α × α)) : List α :=
  pairs.map (fun (a, b) => [a, b]) |>.flatten

lemma List.flattenPairs_cons {α : Type} (a b : α) (pairs : List (α × α)) :
    List.flattenPairs ((a, b) :: pairs) = a :: b :: List.flattenPairs pairs := by
  simp [List.flattenPairs]

lemma List.length_flattenPairs {α : Type} (pairs : List (α × α)) :
    pairs.flattenPairs.length = 2 * pairs.length := by
  induction pairs with
  | nil => simp [List.flattenPairs]
  | cons pair pairs ih => simp [List.flattenPairs] at ih ⊢; omega

/-- A pull and a push, which are active with multiplicity `1` or disabled together. -/
def Interaction.Transition (t : Interaction F × Interaction F) : Prop :=
  t.1.direction = .pull ∧ t.2.direction = .push ∧ t.1.mult = t.2.mult ∧ IsBool t.1.mult

/-- The active transitions count the active interactions with a message in each direction. -/
lemma activeCount_flattenPairs {transitions : List (Interaction F × Interaction F)}
    (h_transitions : ∀ t ∈ transitions, Interaction.Transition t) (msg : Array F) :
    activeCount transitions.flattenPairs .pull msg =
        ((transitions.filter (·.1.mult = 1)).map (·.1.msg)).count msg ∧
      activeCount transitions.flattenPairs .push msg =
        ((transitions.filter (·.1.mult = 1)).map (·.2.msg)).count msg := by
  induction transitions with
  | nil => simp [List.flattenPairs, activeCount]
  | cons t ts ih =>
    obtain ⟨a, b⟩ := t
    obtain ⟨h_pull, h_push, h_mult, h_bool⟩ := h_transitions (a, b) List.mem_cons_self
    obtain ⟨ih_pull, ih_push⟩ := ih fun t' h => h_transitions t' (List.mem_cons_of_mem _ h)
    simp only at h_pull h_push h_mult h_bool
    have h_cons (i : Interaction F) (l : List (Interaction F)) (direction : Channel.Direction) :
        activeCount (i :: l) direction msg = activeCount l direction msg +
          if i.direction = direction ∧ i.msg = msg ∧ i.mult ≠ 0 then 1 else 0 := by
      simp [activeCount, List.countP_cons]
    rw [List.flattenPairs_cons, h_cons, h_cons, h_cons, h_cons, ih_pull, ih_push]
    rcases h_bool with h_zero | h_one
    · simp [h_zero, ← h_mult]
    · simp [h_one, ← h_mult, h_pull, h_push, List.count_cons]

/--
`exists_reached_of_perm` for balanced interactions: a unit pull and a unit push, and transitions,
each a pull and a push that are both active with multiplicity `1` or both disabled. Disabled
transitions don't affect balance and are left out of the chain.
-/
theorem exists_reached_of_balancedInteractions (Reached : ℕ → Array F → Prop)
    (pull push : Interaction F) (transitions : List (Interaction F × Interaction F))
    (balance : BalancedInteractions ((pull, push) :: transitions).flattenPairs)
    (pull_unit : pull.Pull) (push_unit : push.direction = .push ∧ push.mult = 1)
    (h_transitions : ∀ t ∈ transitions, Interaction.Transition t)
    (step : ∀ t ∈ transitions, t.1.mult = 1 → ∀ k, Reached k t.1.msg → Reached (k + 1) t.2.msg)
    (k : ℕ) (reached : Reached k push.msg) :
    ∃ k' ≤ k + transitions.length, Reached k' pull.msg := by
  let active := transitions.filter (·.1.mult = 1)
  have perm : (pull.msg :: active.map (·.1.msg)).Perm (push.msg :: active.map (·.2.msg)) := by
    rw [List.perm_iff_count]
    intro msg
    obtain ⟨count_pull, count_push⟩ := activeCount_flattenPairs h_transitions msg
    have counts := balance.activeCount_push_eq_activeCount_pull_of_isBool msg (by
      intro i hi _
      simp only [List.flattenPairs_cons, List.mem_cons] at hi
      rcases hi with rfl | rfl | hi
      · exact .inr pull_unit.2
      · exact .inr push_unit.2
      obtain ⟨t, t_mem, hi⟩ : ∃ t ∈ transitions, i = t.1 ∨ i = t.2 := by
        simp only [List.flattenPairs, List.mem_flatten, List.mem_map] at hi
        obtain ⟨_, ⟨t, t_mem, rfl⟩, hi⟩ := hi
        exact ⟨t, t_mem, by simp_all⟩
      obtain ⟨-, -, h_mult, h_bool⟩ := h_transitions t t_mem
      rcases hi with rfl | rfl
      · exact h_bool
      · exact h_mult ▸ h_bool)
    simp only [List.flattenPairs_cons, activeCount, List.countP_cons, pull_unit.1, push_unit.1,
      pull_unit.2, push_unit.2] at counts
    simp only [activeCount] at count_pull count_push
    simp only [List.count_cons, active, ← count_pull, ← count_push]
    simp_all
  obtain ⟨k', hk', reached'⟩ := exists_reached_of_perm Reached
    (active.map fun t => (t.1.msg, t.2.msg))
    (by simp only [List.mem_map, List.mem_filter, active]
        rintro _ ⟨t, ⟨t_mem, t_active⟩, rfl⟩
        exact step t t_mem (of_decide_eq_true t_active))
    pull.msg push.msg (by simp only [List.map_map, Function.comp_def]; exact perm) k reached
  refine ⟨k', ?_, reached'⟩
  have := List.length_filter_le (·.1.mult = 1) transitions
  simp only [List.length_map, active] at hk'
  omega
