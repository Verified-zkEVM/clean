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

/-- A multiplicity of `k` for some `1 ≤ k ≤ N`: what a table that answers `k` identical lookups
with one row pulls the facts it relies on with. `CountUpTo 1` is multiplicity `1`.

What this says is that the multiplicity is named by such a `k`, and nothing about the field it
lives in. It does not ask for `N < ringChar F`, so in a small enough field two of those `k` name
the same element, and `CountUpTo 2 (0 : ZMod 2)` holds because `(2 : ZMod 2) = 0`. Asking for the
bound here would carry a condition on the field through every requirement, guarantee and proof that
mentions a count, to exclude a case the balance check excludes already: `Balance.logUpUpTo N` fits
an interaction count only when `count * N < ringChar F`, which over `ZMod 2` with `N = 2` leaves
`count = 0`, so a witness holding such a pull fails the check independently of its multiplicity. -/
def CountUpTo (N : ℕ) (mult : F) : Prop := ∃ k : ℕ, 1 ≤ k ∧ k ≤ N ∧ mult = k

lemma countUpTo_one_iff {mult : F} : CountUpTo 1 mult ↔ mult = 1 := by
  constructor
  · rintro ⟨k, hk1, hk2, h⟩
    obtain rfl : k = 1 := by omega
    simpa using h
  · intro h
    exact ⟨1, le_rfl, le_rfl, by simp [h]⟩

omit [FiniteField F] in
/-- A nonzero multiplicity whose value is at most `N`. -/
lemma countUpTo_of_val {p : ℕ} [Fact p.Prime] {N : ℕ} {mult : ZMod p} (h0 : mult ≠ 0)
    (hN : mult.val ≤ N) : CountUpTo N mult :=
  ⟨ mult.val, Nat.one_le_iff_ne_zero.mpr ((ZMod.val_ne_zero mult).mpr h0), hN,
    (ZMod.natCast_zmod_val mult).symm ⟩

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

/-- A pull of multiplicity `k` for some `1 ≤ k ≤ N`: a table that answers `k` identical lookups
with one row pulls the facts it relies on with the same multiplicity. `Pull` is `PullUpTo 1`. -/
def PullUpTo (N : ℕ) (i : Interaction F) : Prop :=
  i.direction = .pull ∧ CountUpTo N i.mult

/-- An interaction that pushes its message when pulls of multiplicity up to `N` are allowed: an
active push, or a pull of another nonzero multiplicity. `Push` is `PushUpTo 1`. -/
def PushUpTo (N : ℕ) (i : Interaction F) : Prop :=
  i.mult ≠ 0 ∧ (i.direction = .pull → ¬CountUpTo N i.mult)

lemma pullUpTo_one_iff {i : Interaction F} : i.PullUpTo 1 ↔ i.Pull := by
  simp only [PullUpTo, Pull, countUpTo_one_iff]

lemma pushUpTo_one_iff {i : Interaction F} : i.PushUpTo 1 ↔ i.Push := by
  simp only [PushUpTo, Push, countUpTo_one_iff]

lemma not_pushUpTo_iff {N : ℕ} {i : Interaction F} : ¬i.PushUpTo N ↔ i.mult = 0 ∨ i.PullUpTo N := by
  simp only [PushUpTo, PullUpTo, not_and, Classical.not_imp, not_not]
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
Every pull of multiplicity up to `N` is matched by an interaction that pushes its message. For
`N = 1` this is `BalancedInteractions.exists_push_of_pull`. For larger `N` it needs more than balance
of the counts: under field-sum balance, `(p - 1) / 2` pulls of multiplicity `2` and one pull of
multiplicity `1` sum to `p ≡ 0` with no push. It holds when the number of interactions times `N`
is below the characteristic, see `LogUpBalanced.matchedUpTo`.
-/
def MatchedUpTo (N : ℕ) (interactions : List (Interaction F)) : Prop :=
  ∀ a ∈ interactions, a.PullUpTo N → ∃ b ∈ interactions, b.msg = a.msg ∧ b.PushUpTo N

lemma MatchedUpTo.of_perm {N : ℕ} {as bs : List (Interaction F)} :
    MatchedUpTo N as → List.Perm as bs → MatchedUpTo N bs := by
  intro matched perm a a_mem a_pull
  obtain ⟨ b, b_mem, b_msg, b_push ⟩ := matched a (perm.mem_iff.mpr a_mem) a_pull
  exact ⟨ b, perm.mem_iff.mp b_mem, b_msg, b_push ⟩

lemma MatchedUpTo.nil (N : ℕ) : MatchedUpTo N ([] : List (Interaction F)) := by
  simp [MatchedUpTo]

/-- Matching pulls of multiplicity up to `N` matches those up to any `M ≤ N`. -/
lemma MatchedUpTo.mono {M N : ℕ} {interactions : List (Interaction F)} (h : M ≤ N) :
    MatchedUpTo N interactions → MatchedUpTo M interactions := by
  rintro matched a a_mem ⟨ a_direction, k, hk1, hk2, hk ⟩
  obtain ⟨ b, b_mem, b_msg, b_ne_zero, b_not_pull ⟩ :=
    matched a a_mem ⟨ a_direction, k, hk1, hk2.trans h, hk ⟩
  exact ⟨ b, b_mem, b_msg, b_ne_zero,
    fun b_direction ⟨ j, hj1, hj2, hj ⟩ => b_not_pull b_direction ⟨ j, hj1, hj2.trans h, hj ⟩ ⟩

lemma BalancedInteractions.matchedUpTo_one {interactions : List (Interaction F)}
    (balanced : BalancedInteractions interactions) : MatchedUpTo 1 interactions := by
  intro a a_mem a_pull
  obtain ⟨ b, b_mem, b_msg, b_push ⟩ :=
    balanced.exists_push_of_pull a a_mem (Interaction.pullUpTo_one_iff.mp a_pull)
  exact ⟨ b, b_mem, b_msg, Interaction.pushUpTo_one_iff.mpr b_push ⟩

/-- Balance, with pulls of multiplicity up to `N` matched by a push. -/
structure BalancedUpTo (N : ℕ) (interactions : List (Interaction F)) : Prop
    extends BalancedInteractions interactions where
  matchedUpTo : MatchedUpTo N interactions

lemma BalancedUpTo.of_perm {N : ℕ} {as bs : List (Interaction F)} :
    BalancedUpTo N as → List.Perm as bs → BalancedUpTo N bs :=
  fun balanced perm =>
    ⟨ balanced.toBalancedInteractions.of_perm perm, balanced.matchedUpTo.of_perm perm ⟩

lemma BalancedUpTo.nil (N : ℕ) : BalancedUpTo N ([] : List (Interaction F)) :=
  ⟨ .nil, .nil N ⟩

/-- At bound `1`, balance with matched pulls is `BalancedInteractions`: a channel that does not
count keeps the balance premise its soundness proofs had before counted pulls. -/
lemma balancedUpTo_one_iff {interactions : List (Interaction F)} :
    BalancedUpTo 1 interactions ↔ BalancedInteractions interactions :=
  ⟨ fun balanced => balanced.toBalancedInteractions,
    fun balanced => ⟨ balanced, balanced.matchedUpTo_one ⟩ ⟩

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
  /-- The largest pull multiplicity that the check matches with a push. -/
  pullBound : ℕ := 1
  /--
  Pulls of multiplicity up to `pullBound` are matched by a push.

  For the default `pullBound := 1` this is `BalancedInteractions.matchedUpTo_one`, so a check that
  matches nothing beyond unit pulls does not have to provide it. That is why the conclusion of
  `balancedInteractions_of_balanced` is a premise here: a structure's default value is either
  elaborated once with `pullBound` still abstract (a term default, which then cannot be
  `matchedUpTo_one`) or elaborated per instance but without the earlier fields in scope (a tactic
  default). Passing the weaker balance in makes the second form work. A check that sets
  `pullBound := N` for `N > 1` and omits this field gets a type error, not a wrong default.
  -/
  matchedUpTo_of_balanced : ∀ interactions, fits interactions.length →
    Balanced interactions → BalancedInteractions interactions →
      MatchedUpTo pullBound interactions := by
    exact fun _ _ _ h_weak => h_weak.matchedUpTo_one

lemma Balance.balancedUpTo_of_balanced (balance : Balance F) {interactions : List (Interaction F)}
    (fits : balance.fits interactions.length) (balanced : balance.Balanced interactions) :
    BalancedUpTo balance.pullBound interactions :=
  have weak := balance.balancedInteractions_of_balanced _ fits balanced
  ⟨ weak, balance.matchedUpTo_of_balanced _ fits balanced weak ⟩

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

/--
If every interaction carrying `msg` is inactive or a pull of multiplicity at most `N`, the balance
of `msg` is minus a natural number at most `length · N`, which is positive if one of them is an
active pull.
-/
lemma balanceOf_eq_neg_of_pullUpTo {N : ℕ} {msg : Array F} (hN : N < ringChar F) :
    ∀ {interactions : List (Interaction F)},
    (∀ i ∈ interactions, i.msg = msg → i.mult = 0 ∨ i.PullUpTo N) →
    ∃ S : ℕ, balanceOf interactions msg = -(S : F) ∧ S ≤ interactions.length * N ∧
      ∀ a ∈ interactions, a.msg = msg → a.PullUpTo N → 1 ≤ S
  | [], _ => ⟨ 0, by simp [balanceOf], by simp, by simp ⟩
  | i :: is, h => by
    obtain ⟨ S, hS, hle, hpos ⟩ := balanceOf_eq_neg_of_pullUpTo hN (interactions := is)
      fun j hj => h j (List.mem_cons_of_mem i hj)
    rw [balanceOf_cons]
    simp only [List.length_cons]
    by_cases h_msg : i.msg = msg
    case neg =>
      refine ⟨ S, by simp [h_msg, hS], by nlinarith, ?_ ⟩
      intro a a_mem a_msg a_pull
      rcases List.mem_cons.mp a_mem with rfl | a_mem
      · exact absurd a_msg h_msg
      · exact hpos a a_mem a_msg a_pull
    rcases h i List.mem_cons_self h_msg with h_zero | ⟨ h_direction, k, hk1, hk2, hk ⟩
    · have signed_zero : i.signedMult = 0 := by
        cases h_direction : i.direction <;> simp [Interaction.signedMult, h_direction, h_zero]
      refine ⟨ S, by simp [h_msg, signed_zero, hS], by nlinarith, ?_ ⟩
      intro a a_mem a_msg a_pull
      rcases List.mem_cons.mp a_mem with rfl | a_mem
      · -- an inactive pull of multiplicity `k` would need `k ≡ 0`, but `0 < k < ringChar F`
        obtain ⟨ _, j, hj1, hj2, hj ⟩ := a_pull
        rw [h_zero] at hj
        have := (Lean.Grind.IsCharP.natCast_eq_iff_of_lt (α := F) _ (lt_of_le_of_lt hj2 hN)
          (lt_of_le_of_lt (Nat.zero_le N) hN)).mp (by simpa using hj.symm)
        omega
      · exact hpos a a_mem a_msg a_pull
    · refine ⟨ S + k, ?_, by nlinarith, fun _ _ _ _ => by omega ⟩
      simp only [h_msg, ↓reduceIte, Interaction.signedMult, h_direction, hk, hS]
      push_cast
      ring

/--
Every pull of multiplicity up to `N` is matched by a push, when the number of interactions times
`N` is below the characteristic: otherwise the multiplicities of the pulls of a message could add
up to a multiple of the characteristic.
-/
theorem LogUpBalanced.matchedUpTo {N : ℕ} {interactions : List (Interaction F)}
    (balanced : LogUpBalanced interactions) (length_mul_lt : interactions.length * N < ringChar F) :
    MatchedUpTo N interactions := by
  intro a a_mem a_pull
  -- assuming no such push exists, all interactions with the message are inactive or pulls of
  -- multiplicity at most `N`, so their balance is a negative number that can't wrap around
  by_contra! no_push
  have hN : N < ringChar F :=
    lt_of_le_of_lt (Nat.le_mul_of_pos_left N (List.length_pos_of_mem a_mem)) length_mul_lt
  obtain ⟨ S, hS, hle, hpos ⟩ := balanceOf_eq_neg_of_pullUpTo hN (msg := a.msg)
    (interactions := interactions)
    fun i i_mem i_msg => Interaction.not_pushUpTo_iff.mp (no_push i i_mem i_msg)
  have S_pos := hpos a a_mem rfl a_pull
  rw [balanced a.msg, eq_comm, neg_eq_zero] at hS
  have := (Lean.Grind.IsCharP.natCast_eq_iff_of_lt (α := F) _ (lt_of_le_of_lt hle length_mul_lt)
    (lt_of_le_of_lt (Nat.zero_le _) length_mul_lt)).mp (by simpa using hS)
  omega

/--
The bound of `matchedUpTo` is necessary, not an artifact of its proof: once the number of
interactions times `N` reaches the characteristic, the multiplicities of the pulls of a message can
add up to a multiple of it, and the field sums see a balanced list in which nothing was pushed.

Two pulls, of multiplicities `N` and `ringChar F - N`, are such a list whenever `N < ringChar F`
and `ringChar F ≤ 2 * N`: both multiplicities count up to `N`, they sum to the characteristic, and
a list of length `2` passes a bound on the length alone, which is all `Balance.logUp` asks. This is
what `Balance.logUpUpTo N` rules out by asking for `count * N < ringChar F` as well.
-/
theorem exists_logUpBalanced_not_matchedUpTo {N : ℕ} (hN : 2 ≤ N) (h_lt : N < ringChar F)
    (h_le : ringChar F ≤ 2 * N) (channel : RawChannel F) (msg : Array F)
    (h_size : msg.size = channel.arity) :
    ∃ interactions : List (Interaction F), LogUpBalanced interactions ∧
      interactions.length < ringChar F ∧ ¬ MatchedUpTo N interactions := by
  have h_one_le : 1 ≤ ringChar F - N := by omega
  have h_le_N : ringChar F - N ≤ N := by omega
  have h_sum : (N : F) + ((ringChar F - N : ℕ) : F) = 0 := by
    rw [← Nat.cast_add, show N + (ringChar F - N) = ringChar F by omega]
    exact (ringChar.spec F _).mpr dvd_rfl
  have h_count_rest : CountUpTo N ((ringChar F - N : ℕ) : F) :=
    ⟨ ringChar F - N, h_one_le, h_le_N, rfl ⟩
  let mk (mult : F) : Interaction F := ⟨ channel, .pull, mult, msg, h_size ⟩
  refine ⟨ [mk (N : F), mk ((ringChar F - N : ℕ) : F)], fun m => ?_,
    by simp only [List.length_cons, List.length_nil]; omega, fun matched => ?_ ⟩
  · -- the two multiplicities sum to the characteristic, so every message balances
    by_cases h_msg : msg = m
    · have h_bal : balanceOf [mk (N : F), mk ((ringChar F - N : ℕ) : F)] m
          = -((N : F) + ((ringChar F - N : ℕ) : F)) := by
        simp [balanceOf, mk, Interaction.signedMult, h_msg]
        ring
      rw [h_bal, h_sum, neg_zero]
    · simp [balanceOf, mk, h_msg]
  · -- every interaction of the list is a pull counting up to `N`, so none of them is a push
    obtain ⟨ b, b_mem, -, b_push ⟩ :=
      matched (mk ((ringChar F - N : ℕ) : F)) (by simp) ⟨ rfl, h_count_rest ⟩
    obtain ⟨ -, h_not ⟩ := b_push
    simp only [List.mem_cons, List.not_mem_nil, or_false] at b_mem
    rcases b_mem with rfl | rfl
    · exact h_not rfl ⟨ N, by omega, le_rfl, rfl ⟩
    · exact h_not rfl h_count_rest

/-- LogUp: field sums, sound for fewer interactions than the characteristic. -/
def Balance.logUp [ComputableRingChar F] : Balance F where
  Balanced := LogUpBalanced
  fits count := count < ComputableRingChar.char F
  balancedInteractions_of_balanced _ fits balanced :=
    have length_lt := ComputableRingChar.char_eq (R := F) ▸ of_decide_eq_true fits
    ⟨ balanced.exists_push_of_pull length_lt,
      balanced.activeCount_push_eq_activeCount_pull_of_isBool length_lt ⟩
  matchedUpTo_of_balanced _ fits balanced _ :=
    have length_lt := ComputableRingChar.char_eq (R := F) ▸ of_decide_eq_true fits
    balanced.matchedUpTo (by simpa using length_lt)

/-- `Balance.logUp` matches pulls of multiplicity `1` only. Stated so that `simp`/`circuit_norm`
can reduce a `ConsistentUpTo (Balance.logUp).pullBound` goal, which instance search cannot do on
its own: `Balance.logUp` is a plain `def`, so the projection is not reducible. -/
@[simp, circuit_norm] lemma Balance.logUp_pullBound [ComputableRingChar F] :
    (Balance.logUp : Balance F).pullBound = 1 := rfl

/--
LogUp with counted pulls: field sums, sound for interaction counts whose product with `N` is below
the characteristic, so that pulls of multiplicity up to `N` are matched by a push.

Reducible so that instance search can project `pullBound` out of it.
`SoundEnsemble.markFinished` takes `[channel.ConsistentUpTo balance.pullBound]` as an instance
argument, and the counted channel's instance ties that bound to the channel's own `N`, so synthesis
has to see `(logUpUpTo N).pullBound` as `N`. It cannot unfold a plain `def`, and an instance
argument leaves no place to `simp` first.
-/
@[reducible] def Balance.logUpUpTo [ComputableRingChar F] (N : ℕ) : Balance F where
  Balanced := LogUpBalanced
  fits count := count < ComputableRingChar.char F && count * N < ComputableRingChar.char F
  balancedInteractions_of_balanced _ fits balanced :=
    have length_lt := ComputableRingChar.char_eq (R := F) ▸
      (of_decide_eq_true (Bool.and_eq_true_iff.mp fits).1)
    ⟨ balanced.exists_push_of_pull length_lt,
      balanced.activeCount_push_eq_activeCount_pull_of_isBool length_lt ⟩
  pullBound := N
  matchedUpTo_of_balanced _ fits balanced _ :=
    have length_mul_lt := ComputableRingChar.char_eq (R := F) ▸
      (of_decide_eq_true (Bool.and_eq_true_iff.mp fits).2)
    balanced.matchedUpTo length_mul_lt

/-- `Balance.logUpUpTo N` matches pulls of multiplicity up to `N`, for `simp` and `circuit_norm`.
Instance search needs the same fact, and gets it from the check being `@[reducible]`: a `simp`
lemma plays no part in synthesis. -/
@[simp, circuit_norm] lemma Balance.logUpUpTo_pullBound [ComputableRingChar F] (N : ℕ) :
    (Balance.logUpUpTo N : Balance F).pullBound = N := rfl

/-- At bound `1`, the counted check is `Balance.logUp` itself, so an ensemble that does not count
keeps the check it already had, down to the proposition its witness has to satisfy. -/
theorem Balance.logUpUpTo_one [ComputableRingChar F] :
    (Balance.logUpUpTo 1 : Balance F) = Balance.logUp := by
  unfold Balance.logUpUpTo Balance.logUp
  congr 1
  funext n
  simp

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
  -- `matchedUpTo_of_balanced` is the default: `pullBound` is `1`.

/-- `Balance.multiset` matches pulls of multiplicity `1` only. -/
@[simp, circuit_norm] lemma Balance.multiset_pullBound :
    (Balance.multiset : Balance F).pullBound = 1 := rfl

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

/--
Consistency on balanced lists whose pulls of multiplicity up to `N` are matched by a push
(`MatchedUpTo N`). Channels with counted pulls are consistent in this sense, under a balance check
whose `pullBound` is at least `N`.
-/
class ConsistentUpTo (N : ℕ) (channel : RawChannel F) : Prop where
  consistent : ∀ (interactions : List (Interaction F)) (data : ProverData F),
    BalancedUpTo N interactions →
    (∀ i ∈ interactions, i.channel = channel ∧ i.Requirements data) →
    (∀ i ∈ interactions, i.Guarantees data)

instance (N : ℕ) (channel : RawChannel F) [channel.Consistent] : channel.ConsistentUpTo N where
  consistent interactions data balanced :=
    Consistent.consistent interactions data balanced.toBalancedInteractions

/-- At bound `1`, consistency under counted pulls is `Consistent`: `ConsistentUpTo` generalizes
that class rather than replacing it. -/
lemma consistentUpTo_one_iff (channel : RawChannel F) :
    channel.ConsistentUpTo 1 ↔ channel.Consistent := by
  constructor
  · intro h
    exact ⟨ fun interactions data balanced reqs =>
      h.consistent interactions data (balancedUpTo_one_iff.mpr balanced) reqs ⟩
  · intro h
    have := h
    infer_instance
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
Assume you have a list of channel interactions that is made up of pairs (pull_i, push_i),
where for each i, `Guarantees pull_i → Requirements push_i`.
We want to think of (pull_i → push_i) as the state transition of a VM circuit.

Furthermore, assume pulls and pushes are balanced, and the channel is normal.

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
  -- all pulls and pushes have multiplicity 1
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

lemma activeCount_append (as bs : List (Interaction F)) (direction : Channel.Direction)
    (msg : Array F) :
    activeCount (as ++ bs) direction msg = activeCount as direction msg + activeCount bs direction msg :=
  List.countP_append ..

lemma activeCount_eq_zero_of_direction_ne {interactions : List (Interaction F)}
    {direction : Channel.Direction} (h_direction : ∀ i ∈ interactions, i.direction ≠ direction)
    (msg : Array F) : activeCount interactions direction msg = 0 := by
  simp only [activeCount, List.countP_eq_zero, decide_eq_true_eq, not_and]
  exact fun i hi h => absurd h (h_direction i hi)

/--
Zero-padded variant of `guarantees_of_requirements_of_requirements_of_guarantees`.

Pulls and pushes come in pairs, which are either active, with multiplicity `1`, or disabled, with
multiplicity `0` on both sides. Disabled pairs don't affect balance, and the guarantees of their
pulls hold trivially.
-/
theorem guarantees_of_requirements_of_requirements_of_guarantees_of_mult_zero_iff
    (channel : RawChannel F) [channel.Normal]
    (pulls pushes : List (Interaction F))
    (balance : BalancedInteractions (pulls ++ pushes)) (data : ProverData F)
  (len_pulls_pushes : pulls.length = pushes.length)
  -- all interactions are on the input channel
  (pulls_channel : ∀ a ∈ pulls, a.channel = channel)
  (pushes_channel : ∀ b ∈ pushes, b.channel = channel)
  -- pulls and pushes are either active, with multiplicity `1`, or disabled
  (pulls_direction : ∀ a ∈ pulls, a.direction = .pull ∧ IsBool a.mult)
  (pushes_direction : ∀ b ∈ pushes, b.direction = .push ∧ IsBool b.mult)
  -- a pair is disabled on one side iff it is disabled on the other
  (pair_zero : ∀ pair ∈ pulls.zip pushes, pair.1.mult = 0 ↔ pair.2.mult = 0) :
    (∀ pair ∈ pulls.zip pushes, pair.1.Guarantees data → pair.2.Requirements data) →
    ∀ pair ∈ pulls.zip pushes, pair.2.Requirements data → pair.1.Guarantees data := by
  intro constraints
  let active := (pulls.zip pushes).filter fun pair => pair.1.mult ≠ 0
  have mem_active : ∀ pair ∈ active, pair ∈ pulls.zip pushes ∧ pair.1.mult ≠ 0 := by
    intro pair h
    simpa [active] using h
  have count_eq : ∀ msg, (active.map (·.1)).countP (·.msg = msg) =
      (active.map (·.2)).countP (·.msg = msg) := by
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
    rw [activeCount_append, activeCount_append, activeCount_eq_zero_of_direction_ne pulls_ne_push,
      activeCount_eq_zero_of_direction_ne pushes_ne_pull] at counts
    have pulls_count : (active.map (·.1)).countP (·.msg = msg) = activeCount pulls .pull msg := by
      conv_rhs => rw [← List.map_fst_zip (l₁ := pulls) (l₂ := pushes) (by omega)]
      simp only [active, activeCount, List.countP_map, List.countP_filter]
      apply List.countP_congr
      intro pair h
      simp [(pulls_direction _ (List.of_mem_zip h).1).1]
    have pushes_count : (active.map (·.2)).countP (·.msg = msg) = activeCount pushes .push msg := by
      conv_rhs => rw [← List.map_snd_zip (l₁ := pulls) (l₂ := pushes) (by omega)]
      simp only [active, activeCount, List.countP_map, List.countP_filter]
      apply List.countP_congr
      intro pair h
      simp [(pushes_direction _ (List.of_mem_zip h).2).1, pair_zero pair h]
    omega
  have theorem_active := guarantees_of_requirements_of_requirements_of_guarantees
    channel (active.map (·.1)) (active.map (·.2)) count_eq data active.length (by simp) (by simp)
    (by
      simp only [List.mem_map]
      rintro a ⟨pair, h, rfl⟩
      exact pulls_channel _ (List.of_mem_zip (mem_active pair h).1).1)
    (by
      simp only [List.mem_map]
      rintro b ⟨pair, h, rfl⟩
      exact pushes_channel _ (List.of_mem_zip (mem_active pair h).1).2)
    (by
      simp only [List.mem_map]
      rintro a ⟨pair, h, rfl⟩
      obtain ⟨pair_mem, mult_ne_zero⟩ := mem_active pair h
      obtain ⟨h_direction, h_mult⟩ := pulls_direction _ (List.of_mem_zip pair_mem).1
      exact ⟨h_direction, h_mult.resolve_left mult_ne_zero⟩)
    (by
      simp only [List.mem_map]
      rintro b ⟨pair, h, rfl⟩
      obtain ⟨pair_mem, mult_ne_zero⟩ := mem_active pair h
      obtain ⟨h_direction, h_mult⟩ := pushes_direction _ (List.of_mem_zip pair_mem).2
      exact ⟨h_direction, h_mult.resolve_left ((pair_zero pair pair_mem).not.mp mult_ne_zero)⟩)
    (by
      intro i hi
      simp only [List.getElem_map]
      exact constraints _ (mem_active _ (List.getElem_mem _)).1)
  intro pair pair_mem requirements
  by_cases mult_zero : pair.1.mult = 0
  · apply RawChannel.Normal.guarantees_of_not_pull _ _
      (pulls_channel _ (List.of_mem_zip pair_mem).1)
    simp [Interaction.Pull, mult_zero]
  have pair_active : pair ∈ active := by simp [active, pair_mem, mult_zero]
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem pair_active
  have := theorem_active i (by simpa using hi)
  simp only [List.getElem_map] at this
  exact this requirements
