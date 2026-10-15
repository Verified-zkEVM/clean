/-
Drawing the challenge: the one thing the proof system provides.

A backend that supports challenges implements `Challenge.interface m`: commit to `m` values, get
a challenge back. Its contract says nothing about the challenge: the verifier samples it, the
prover does not choose it. On R1CS it is one native operation (`R1CSOp.challenge`), in the style of
gnark's `Commit`.

Everything else is a circuit. A *check* for a contract `p` is an implementation of
`p.withChallenge`: the same contract, given a challenge on the side, with all of the input
committed. `Protocol.impl` closes it: commit to the input, draw the challenge, run the check. The
result implements `p` itself, an ordinary contract with no challenge in it, and

- `Protocol.soundness_error`: with the committed input fixed, the values of the drawn challenge at
  which a false statement is accepted are at most `errorBound` of the check;
- `Protocol.completeness_error`: with the committed input fixed, and the challenge in the heap,
  the values at which the honest prover fails are at most `honestErrorBound` of the check.

The challenge is shared by passing it: a check that runs several tables (`Lookup`: the table side
and the lookup side) hands the same variable to each, and combines their final sums.
-/
module

public import Clean2.Challenge.Basic

@[expose] public section

namespace Clean2

namespace Challenge
variable {F K : Type}

/-- Commit to `m` values, receive a challenge in `K`, laid out by `kty`. Nothing is promised about
the challenge. -/
@[reducible]
def interface (m : ℕ) (kty : CType F K) : Interface F where
  input := Vector F m
  inputCType := .natives m
  output := K
  outputCType := kty

variable {B : Backend}

/-- A challenge that constrains nothing: every assignment, in particular every value of the
challenge, satisfies its constraints. -/
class Free {m : ℕ} {kty : CType B.Native K} (challenge : Impl B (interface m kty)) : Prop where
  holds : ∀ input s env, ((challenge.main input).operations s).ConstraintsHold env s

end Challenge

/-- The contract `p`, for a check that is given a challenge in `K` on the side. -/
@[reducible]
def Interface.withChallenge {F K : Type} (p : Interface F) (kty : CType F K) : Interface F where
  input := p.input × K
  inputCType := p.inputCType ×ᵗ kty
  output := p.output
  outputCType := p.outputCType
  Assumptions x := p.Assumptions x.1
  Spec x y := p.Spec x.1 y
  ProverAssumptions x := p.ProverAssumptions x.1
  ProverSpec x y := p.ProverSpec x.1 y

/-- All of the input is committed. -/
@[reducible]
def Interface.withChallenge.phases {F K : Type} (p : Interface F) (kty : CType F K) : (p.withChallenge kty).Phases where
  Committed := p.input
  committed x := x.1
  Challenge := K
  challenge x := x.2

namespace Protocol
variable {B : Backend} {K : Type} {p : Interface B.Native} {kty : CType B.Native K} [kty.Faithful]
  (challenge : Impl B (Challenge.interface (size p.Input) kty)) (check : Impl B (p.withChallenge kty))

/-- Commit to the input, draw a challenge, check. -/
def impl : Impl B p where
  main x := do
    let α ← challenge (toElements x)
    check (x, α)
  spatial := by
    intro x s h
    simp only [circuit_norm]
    exact ⟨h, fun h_α m => ⟨Set.union_subset (h.trans m) h_α, fun h_out _ => h_out⟩⟩
  soundness := by
    intro s env x h h_holds
    simp only [circuit_norm] at h h_holds ⊢
    exact h_holds h
  completeness := by
    intro s env x h_honest h
    simp only [circuit_norm] at h h_honest ⊢
    exact ⟨h, (h_honest h).2⟩

variable [Impl.NoEvents challenge]

/-- The rare events of a protocol depend on the committed input, and determine the drawn
challenge. -/
theorem phased [Impl.Phased check (Interface.withChallenge.phases p kty)] (s : B.State) (x : p.Input B.Var) :
    (((impl challenge check).main x).operations s).Phased (fun env => p.inputCType.decode (B.evalT env x))
      (fun env => kty.decode (B.evalT env (challenge.output (toElements x) s))) := by
  simp only [impl, circuit_norm]
  refine (Ops.phased_cons_call _ _).mpr ⟨Impl.phased_call_of_noEvents _ _ _,
    (Ops.phased_cons_call _ _).mpr ⟨Impl.phased_call _ _ _ ?_ ?_, Ops.phased_nil⟩⟩
  · intro e₁ e₂ h
    simp only [Interface.Phases.key, circuit_norm] at h ⊢
    exact h
  · intro e₁ e₂ h
    simp only [Interface.Phases.chal, circuit_norm] at h ⊢
    exact h

instance {M : Type} [AddCommMonoid M] (μ : B.Measure M) [Impl.Measured μ challenge] [Impl.Measured μ check] :
    Impl.Measured μ (impl challenge check) where
  value := μ.of challenge + μ.of check
  value_eq := by measure [impl]

/-- The values of the drawn challenge at which a false statement is accepted, with the committed
input fixed to `x₀`. -/
def BadChallenges (s : B.State) (x : p.Input B.Var) (x₀ : p.input) : Set K :=
  {a | ∃ env : B.Cell → B.Native, p.inputCType.decode (B.evalT env x) = x₀ ∧
    kty.decode (B.evalT env (challenge.output (toElements x) s)) = a ∧
    p.inputCType.Valid (B.evalT env x) ∧ p.Assumptions x₀ ∧
    (((impl challenge check).main x).operations s).ConstraintsHold env s ∧
    ¬(p.outputCType.Valid (B.evalT env ((impl challenge check).output x s)) ∧
      p.Spec x₀ (p.outputCType.decode (B.evalT env ((impl challenge check).output x s))))}

/-- The values of the drawn challenge at which the honest prover fails, with the committed input
fixed to `x₀`: it continues from an assignment of the heap that holds the input and the
challenge. -/
def HonestFailures (s : B.State) (x : p.Input B.Var) (x₀ : p.input) : Set K :=
  {a | ∃ env₀ : B.Cell → B.Native, p.inputCType.decode (B.evalT env₀ x) = x₀ ∧
    kty.decode (B.evalT env₀ (challenge.output (toElements x) s)) = a ∧
    p.inputCType.Valid (B.evalT env₀ x) ∧ p.ProverAssumptions x₀ ∧
    ¬∃ env : B.Cell → B.Native, (∀ c ∈ B.Alloc (challenge.advance (toElements x) s), env c = env₀ c) ∧
      (((impl challenge check).main x).operations s).ConstraintsHold env s}

variable [Impl.Phased check (Interface.withChallenge.phases p kty)]

/-- **Soundness error of a protocol.** Fix the committed input `x₀`. The values of the drawn
challenge at which some assignment satisfies the real constraints, but the input does not satisfy
the spec, are at most `errorBound` of the check. -/
theorem soundness_error [Impl.Measured errorBound challenge] [Impl.Measured errorBound check]
    (h_zero : errorBound.of challenge = 0) (s : B.State) (x : p.Input B.Var) (x₀ : p.input) :
    (BadChallenges challenge check s x x₀).encard ≤ errorBound.of check := by
  have h := (impl challenge check).soundness_error_ops s x (phased challenge check s x) x₀
  have h_val : Impl.Measured.value errorBound (impl challenge check) = errorBound.of check := by
    show errorBound.of challenge + errorBound.of check = _
    rw [h_zero, zero_add]
  rw [Impl.Measured.value_eq, h_val] at h
  refine le_trans (Set.encard_le_encard ?_) h
  rintro a ⟨env, rfl, h_a, h_valid, h_assumptions, h_holds, h_spec⟩
  exact ⟨env, rfl, h_a, h_valid, h_assumptions, h_holds, h_spec⟩

omit [Impl.NoEvents challenge] in
/-- **Completeness error of a protocol.** Fix the committed input `x₀`, and let the challenge be
drawn: the heap after it holds the input and the challenge. The values of the challenge at which
the honest prover, continuing from some assignment of that heap, fails are at most
`honestErrorBound` of the check. -/
theorem completeness_error [Challenge.Free challenge] [Impl.Measured honestErrorBound check]
    (s : B.State) (x : p.Input B.Var) (h_in : B.footprintT x ⊆ B.Alloc s) (x₀ : p.input) :
    (HonestFailures challenge check s x x₀).encard ≤ honestErrorBound.of check := by
  set α := challenge.output (toElements x) s
  set s' := challenge.advance (toElements x) s
  -- after the challenge, the input and the challenge are in the heap
  have h_post := (challenge.toSubcircuit s (toElements x)).post_of_pre h_in
  have h_mono := (challenge.toSubcircuit s (toElements x)).alloc_mono
  simp only [circuit_norm] at h_post h_mono
  have h_in' : B.footprintT (M := (p.withChallenge kty).Input) (x, α) ⊆ B.Alloc s' :=
    Backend.footprintT_ctypeProd_subset.mpr ⟨h_in.trans h_mono, h_post⟩
  refine le_trans (Set.encard_le_encard ?_) (check.completeness_error_of s' (x, α) h_in' x₀)
  rintro a ⟨env₀, h_x, h_a, h_valid, h_prover, h_fail⟩
  refine ⟨env₀, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try simp only [Interface.Phases.key, Interface.Phases.chal, circuit_norm]
  · exact h_x
  · exact h_a
  · exact h_valid
  · have h_x' : p.inputCType.decode (ProvableType.map (B.eval env₀) x) = x₀ := h_x
    rw [h_x']
    exact h_prover
  rintro ⟨env, h_agree, h_holds⟩
  refine h_fail ⟨env, h_agree, ?_⟩
  -- the challenge constrains nothing
  simp only [impl, circuit_norm]
  simp only [Ops.ConstraintsHold, Ops.toFlat, Backend.flatHolds_append, List.append_nil]
  refine ⟨Challenge.Free.holds _ _ _, ?_⟩
  rw [← (challenge.toSubcircuit s (toElements x)).next_eq]
  exact h_holds

end Protocol
end Clean2
