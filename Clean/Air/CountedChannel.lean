module

public import Clean.Air.Balance
public import Clean.Circuit.Explicit

@[expose] public section

/-!
# Channels with counted pulls

A table that answers `k` identical lookups with one row pulls the facts it relies on with the same
multiplicity `k`. `Channel.counted N channel` is `channel` with pulls of multiplicity up to `N`: such
a pull gets the guarantee, and an active push owes it. It is consistent in the sense of
`RawChannel.ConsistentUpTo N`, so it can be finished in a `SoundEnsemble` whose balance check has a
`pullBound` of at least `N`, e.g. `Balance.logUpUpTo N`.
-/

variable {F : Type} [FiniteField F]
variable {Message : TypeMap} [ProvableType Message]

namespace Channel

/-- `channel`, with pulls of multiplicity up to `N`. -/
def counted (N : ℕ) (channel : Channel F Message) : RawChannel F where
  name := channel.name
  arity := size Message
  Guarantees mult message data :=
    CountUpTo N mult → channel.Guarantees (fromElements message) data
  Requirements direction mult message data :=
    match direction with
    | .push => mult ≠ 0 → channel.Guarantees (fromElements message) data
    | .pull => mult = 0 ∨ CountUpTo N mult

omit [FiniteField F] in
/-- Channels with different names are different. Lets `circuit_norm` tell a counted channel apart
from the other channels of a circuit without unfolding them. -/
@[circuit_norm] lemma _root_.RawChannel.eq_false_of_name_ne {a b : RawChannel F}
    (h : a.name ≠ b.name) : (a = b) = False :=
  eq_false fun h_eq => h (congrArg RawChannel.name h_eq)

@[circuit_norm] lemma counted_name (N : ℕ) (channel : Channel F Message) :
    (channel.counted N).name = channel.name := rfl
@[circuit_norm] lemma counted_arity (N : ℕ) (channel : Channel F Message) :
    (channel.counted N).arity = size Message := rfl

/-- `counted 1` gives what the plain typed channel gives: only a pull of multiplicity `1` gets the
guarantee. -/
lemma counted_one_guarantees_iff (channel : Channel F Message) (mult : F)
    (message : Vector F (size Message)) (data : ProverData F) :
    (channel.counted 1).Guarantees mult message data ↔
      channel.toRaw.Guarantees mult message data := by
  simp [counted, toRaw, countUpTo_one_iff]

/-- `counted 1` owes what the plain typed channel owes: an active push owes the guarantee, and a
pull has multiplicity `0` or `1`. Together with `counted_one_guarantees_iff`, counting up to `1` is the
channel Clean already had. -/
lemma counted_one_requirements_iff (channel : Channel F Message) (direction : Direction) (mult : F)
    (message : Vector F (size Message)) (data : ProverData F) :
    (channel.counted 1).Requirements direction mult message data ↔
      channel.toRaw.Requirements direction mult message data := by
  cases direction <;> simp [counted, toRaw, countUpTo_one_iff]

/-- The interaction of pulling `msg` `count` times from `channel.counted N`. -/
def pulledUpTo (N : ℕ) (channel : Channel F Message) (count : Expression F)
    (msg : Message (Expression F)) : AbstractInteraction F :=
  ⟨ channel.counted N, .pull, count, toElements msg ⟩

/-- The interaction of pushing `msg` `mult` times to `channel.counted N`. -/
def emittedUpTo (N : ℕ) (channel : Channel F Message) (mult : Expression F)
    (msg : Message (Expression F)) : AbstractInteraction F :=
  ⟨ channel.counted N, .push, mult, toElements msg ⟩

/-- Pull `msg` `count` times, for `count` up to `N`. -/
@[circuit_norm]
def pullUpTo (N : ℕ) (channel : Channel F Message) (count : Expression F)
    (msg : Message (Expression F)) : Circuit F Unit := fun _ =>
  ((), [.interact (pulledUpTo N channel count msg)])

/-- Push `msg` `mult` times to `channel.counted N`. -/
@[circuit_norm]
def emitUpTo (N : ℕ) (channel : Channel F Message) (mult : Expression F)
    (msg : Message (Expression F)) : Circuit F Unit := fun _ =>
  ((), [.interact (emittedUpTo N channel mult msg)])

instance {N : ℕ} {channel : Channel F Message} {count : Expression F} :
    ExplicitCircuits (F := F) (channel.pullUpTo N count) where
  output _ _ := ()
  localLength _ _ := 0
  operations msg _ := [.interact (pulledUpTo N channel count msg)]
  channelsWithGuarantees _ _ := [channel.counted N]

instance {N : ℕ} {channel : Channel F Message} {mult : Expression F} :
    ExplicitCircuits (F := F) (channel.emitUpTo N mult) where
  output _ _ := ()
  localLength _ _ := 0
  operations msg _ := [.interact (emittedUpTo N channel mult msg)]
  channelsWithGuarantees _ _ := []

attribute [explicit_circuit_no_unfold] pullUpTo emitUpTo

section
variable {N : ℕ} {channel : Channel F Message} {mult : Expression F}
  {msg : Message (Expression F)} {env : Environment F}

@[circuit_norm] lemma pulledUpTo_channel :
    (pulledUpTo N channel mult msg).channel = channel.counted N := rfl
@[circuit_norm] lemma pulledUpTo_direction :
    (pulledUpTo N channel mult msg).direction = .pull := rfl
@[circuit_norm] lemma pulledUpTo_mult :
    (pulledUpTo N channel mult msg).mult = mult := rfl
@[circuit_norm] lemma pulledUpTo_msg :
    (pulledUpTo N channel mult msg).msg = toElements msg := rfl
@[circuit_norm] lemma emittedUpTo_channel :
    (emittedUpTo N channel mult msg).channel = channel.counted N := rfl
@[circuit_norm] lemma emittedUpTo_direction :
    (emittedUpTo N channel mult msg).direction = .push := rfl
@[circuit_norm] lemma emittedUpTo_mult :
    (emittedUpTo N channel mult msg).mult = mult := rfl
@[circuit_norm] lemma emittedUpTo_msg :
    (emittedUpTo N channel mult msg).msg = toElements msg := rfl

@[circuit_norm] lemma pulledUpTo_guarantees :
    (pulledUpTo N channel mult msg).Guarantees env ↔
      (CountUpTo N (Expression.eval env mult) → channel.Guarantees (eval env msg) env.data) := by
  simp [pulledUpTo, AbstractInteraction.Guarantees, counted,
    ProvableType.fromElements_toElements]

@[circuit_norm] lemma pulledUpTo_requirements :
    (pulledUpTo N channel mult msg).Requirements env ↔
      (Expression.eval env mult = 0 ∨ CountUpTo N (Expression.eval env mult)) := by
  simp [pulledUpTo, AbstractInteraction.Requirements, counted]

@[circuit_norm] lemma emittedUpTo_guarantees :
    (emittedUpTo N channel mult msg).Guarantees env := by
  simp [emittedUpTo, AbstractInteraction.Guarantees]

@[circuit_norm] lemma emittedUpTo_requirements :
    (emittedUpTo N channel mult msg).Requirements env ↔
      (Expression.eval env mult ≠ 0 → channel.Guarantees (eval env msg) env.data) := by
  simp [emittedUpTo, AbstractInteraction.Requirements, counted,
    ProvableType.fromElements_toElements]
end

/-- A pull of multiplicity up to `N` is matched by a push, whose requirement gives the
guarantee. Every other interaction gets no guarantee. -/
instance (N : ℕ) (channel : Channel F Message) : (channel.counted N).ConsistentUpTo N where
  consistent interactions data balanced reqs a a_mem := by
    obtain ⟨ a_channel, - ⟩ := reqs a a_mem
    by_cases a_pull : a.PullUpTo N
    case neg =>
      rcases a with ⟨ _, a_direction, a_mult, a_msg, a_size ⟩
      subst a_channel
      simp only [Interaction.Guarantees, counted]
      exact fun h_direction h_count => absurd ⟨ h_direction, h_count ⟩ a_pull
    obtain ⟨ b, b_mem, b_msg, b_ne_zero, b_not_pull ⟩ := balanced.matchedUpTo a a_mem a_pull
    obtain ⟨ b_channel, b_reqs ⟩ := reqs b b_mem
    rcases a with ⟨ _, a_direction, a_mult, a_msg, a_size ⟩
    rcases b with ⟨ _, b_direction, b_mult, b_msg', b_size ⟩
    subst a_channel b_channel
    simp only at b_msg
    subst b_msg
    simp only [Interaction.Guarantees, Interaction.Requirements, Interaction.msgVector,
      counted] at b_reqs ⊢
    intro _ _
    cases b_direction with
    | push => exact b_reqs b_ne_zero
    | pull => exact absurd (b_reqs.resolve_left b_ne_zero) (b_not_pull rfl)

/-- Synthesis finds the instance for the `pullBound` of a concrete balance check on its own. That is
what `SoundEnsemble.markFinished` needs, since it takes the instance as an instance argument, where
no `simp` step can run first. -/
example [ComputableRingChar F] (N : ℕ) (channel : Channel F Message) :
    (channel.counted N).ConsistentUpTo (Balance.logUpUpTo (F := F) N).pullBound :=
  inferInstance

/-- The counted channel is also consistent for balance checks with a larger bound. -/
theorem counted_consistentUpTo_of_le {M N : ℕ} (h : N ≤ M) (channel : Channel F Message) :
    (channel.counted N).ConsistentUpTo M where
  consistent interactions data balanced :=
    RawChannel.ConsistentUpTo.consistent (N := N) interactions data
      ⟨ balanced.toBalancedInteractions, balanced.matchedUpTo.mono h ⟩

/--
Why `ConsistentUpTo` is needed: for `2 ≤ N` the counted channel is **not**
`RawChannel.Consistent`, so it could not be finished in a `SoundEnsemble` under Clean's unmodified
balance premise `BalancedInteractions`.

The counterexample is two pulls of a message the channel does not guarantee, one of multiplicity
`N` and one of multiplicity `1`, with nothing pushed. `BalancedInteractions` is satisfied:
`exists_push_of_pull` only has to match pulls of multiplicity `1`, and it counts the pull of `N` as
an `Interaction.Push` of the message, so the pull of `1` is matched; the count condition is vacuous
because `N` is neither `0` nor `1`. The counted channel, in contrast, reads both as pulls and hands
the guarantee to the pull of `1`, which is false.

This is exactly the gap that `MatchedUpTo N` / `BalancedUpTo N` and `Balance.pullBound` close, and
the reason `Channel.counted` carries a `RawChannel.ConsistentUpTo N` instance instead of a
`RawChannel.Consistent` one.

The hypothesis `N < ringChar F` is what makes `N` distinct from both `0` and `1` in `F`; together
with `2 ≤ N` it is all the counterexample needs.
-/
theorem counted_not_consistent {N : ℕ} (hN : 2 ≤ N) (h_char : N < ringChar F)
    (channel : Channel F Message) (m : Message F) (data : ProverData F)
    (h_m : ¬ channel.Guarantees m data) : ¬ (channel.counted N).Consistent := by
  rintro ⟨ consistent ⟩
  have cast_inj {a b : ℕ} (ha : a < ringChar F) (hb : b < ringChar F) :
      (a : F) = (b : F) → a = b :=
    fun h => (Lean.Grind.IsCharP.natCast_eq_iff_of_lt (α := F) _ ha hb).mp h
  have hN0 : (N : F) ≠ 0 := fun h => by
    have := cast_inj h_char (b := 0) (by omega) (by simpa using h); omega
  have hN1 : (N : F) ≠ 1 := fun h => by
    have := cast_inj h_char (b := 1) (by omega) (by simpa using h); omega
  let mk : F → Interaction F :=
    fun mult => ⟨ channel.counted N, .pull, mult, (toElements m).toArray, by simp [counted] ⟩
  let l := [mk (N : F), mk 1]
  have h_bal : BalancedInteractions l := by
    constructor
    · -- the pull of `1` is matched by the pull of `N`, which `Interaction.Push` counts as a push
      intro a a_mem _
      refine ⟨ mk (N : F), by simp [l], ?_, hN0, fun _ => hN1 ⟩
      simp only [l, List.mem_cons, List.not_mem_nil, or_false] at a_mem
      rcases a_mem with rfl | rfl <;> rfl
    · -- the multiplicity `N` is neither `0` nor `1`, so only untouched messages qualify
      intro msg is_bool
      by_cases h_msg : (toElements m).toArray = msg
      · exfalso
        rcases is_bool (mk (N : F)) (by simp [l]) h_msg with h | h
        · exact hN0 h
        · exact hN1 h
      · simp [activeCount, l, mk, h_msg]
  have h_reqs : ∀ i ∈ l, i.channel = channel.counted N ∧ i.Requirements data := by
    intro i h_i
    simp only [l, List.mem_cons, List.not_mem_nil, or_false] at h_i
    rcases h_i with rfl | rfl
    · refine ⟨ rfl, ?_ ⟩
      simp only [Interaction.Requirements, mk, counted, Interaction.msgVector]
      exact .inr ⟨ N, by omega, le_rfl, rfl ⟩
    · refine ⟨ rfl, ?_ ⟩
      simp only [Interaction.Requirements, mk, counted, Interaction.msgVector]
      exact .inr ⟨ 1, le_rfl, by omega, by simp ⟩
  have h_g := consistent l data h_bal h_reqs (mk 1) (by simp [l])
  simp only [Interaction.Guarantees, mk, counted, Interaction.msgVector] at h_g
  apply h_m
  have h := h_g trivial ⟨ 1, le_rfl, by omega, by simp ⟩
  convert h
  simp [ProvableType.fromElements_toElements]

end Channel
