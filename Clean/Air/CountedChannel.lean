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

/-- `k` for some `1 ≤ k ≤ N`. -/
def CountUpTo (N : ℕ) (mult : F) : Prop := ∃ k : ℕ, 1 ≤ k ∧ k ≤ N ∧ mult = k

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
@[circuit_norm] lemma emittedUpTo_channel :
    (emittedUpTo N channel mult msg).channel = channel.counted N := rfl
@[circuit_norm] lemma emittedUpTo_direction :
    (emittedUpTo N channel mult msg).direction = .push := rfl

@[circuit_norm] lemma pulledUpTo_guarantees :
    (pulledUpTo N channel mult msg).Guarantees env ↔
      (CountUpTo N (Expression.eval env mult) → channel.Guarantees (eval env msg) env.data) := by
  simp [pulledUpTo, AbstractInteraction.Guarantees, counted,
    ProvableType.fromElements_eval_toElements]

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
    ProvableType.fromElements_eval_toElements]
end

omit [FiniteField F] in
/-- A nonzero multiplicity whose value is at most `N`. -/
lemma countUpTo_of_val {p : ℕ} [Fact p.Prime] {N : ℕ} {mult : ZMod p} (h0 : mult ≠ 0)
    (hN : mult.val ≤ N) : CountUpTo N mult :=
  ⟨ mult.val, Nat.one_le_iff_ne_zero.mpr ((ZMod.val_ne_zero mult).mpr h0), hN,
    (ZMod.natCast_zmod_val mult).symm ⟩

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

/-- The counted channel is also consistent for balance checks with a larger bound. -/
theorem counted_consistentUpTo_of_le {M N : ℕ} (h : N ≤ M) (channel : Channel F Message) :
    (channel.counted N).ConsistentUpTo M where
  consistent interactions data balanced :=
    RawChannel.ConsistentUpTo.consistent (N := N) interactions data
      ⟨ balanced.toBalancedInteractions, balanced.matchedUpTo.mono h ⟩

end Channel
