/-
Verifier challenges, with no probabilities in circuit proofs.

A challenge is a field element `α` that the verifier samples after the prover has committed to
some values, the *phase-1* values `x`. A circuit that uses a challenge is an ordinary Clean 2
circuit that takes `α` as one more input: the backends and the circuit monad do not change. What
changes is the contract it is checked against, a `ChallengeCheck`:

- *pointwise* (the implementation's ordinary soundness, `α` universally quantified): if the
  constraints hold at `α`, then the polynomial `poly x` vanishes at `α`. The polynomial depends on
  the phase-1 values only.
- *symbolic* (pure algebra, no circuit): `poly x = 0` as a polynomial implies the statement.

`ChallengeCheck.soundness_error` combines the two: if the statement is false, then the set of
challenges at which any prover is accepted has at most `natDegree (poly x)` elements. That is the
soundness error, `natDegree (poly x) / |F|` for a uniform challenge. It is the only place where
counting happens, and it is proved once.

Why not read constraints that mention `α` as polynomial identities in `F[X]` directly? Because a
cheating prover chooses the cells it fills after `α` pointwise, as arbitrary functions of `α`, not as
polynomials in `X`. See `Clean2/Challenge/NaiveSymbolic.lean` for a constraint that is
unsatisfiable symbolically but accepted at half of all challenges. Here every cell other than the
phase-1 inputs is quantified after `α` (`Accepts`), which over-approximates the real protocol (where
some of those cells are committed together with `x`), so the bound holds a fortiori.
-/
module

public import Clean2.Core
public import Lean.Elab.Tactic
meta import Clean2.Core.Spatial
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Data.Set.Card

@[expose] public section

namespace Clean2
open Polynomial

/-! ## Counting roots -/

section Roots
variable {F : Type} [Field F]

/-- The points where a nonzero polynomial vanishes are its roots. -/
theorem setOf_eval_eq_zero {P : F[X]} (hP : P ≠ 0) [DecidableEq F] :
    {α | P.eval α = 0} = ↑P.roots.toFinset := by
  ext α
  simp [mem_roots hP, IsRoot]

/-- A nonzero polynomial vanishes at no more points than its degree. -/
theorem ncard_eval_eq_zero_le {P : F[X]} (hP : P ≠ 0) : {α | P.eval α = 0}.ncard ≤ P.natDegree := by
  classical
  rw [setOf_eval_eq_zero hP, Set.ncard_coe_finset]
  exact (Multiset.toFinset_card_le _).trans (card_roots' P)

/-- **Soundness error from a symbolic argument.** If acceptance at a challenge implies that `P`
vanishes there, and `P = 0` implies the statement, then a false statement is accepted at no more
challenges than the degree of `P`. -/
theorem ncard_accepting_le {Accept : F → Prop} {Statement : Prop} (P : F[X])
    (pointwise : ∀ α, Accept α → P.eval α = 0) (symbolic : P = 0 → Statement) (h : ¬Statement) :
    {α | Accept α}.ncard ≤ P.natDegree := by
  classical
  have hP : P ≠ 0 := fun h0 => h (symbolic h0)
  have h_finite : {α | P.eval α = 0}.Finite := by
    rw [setOf_eval_eq_zero hP]
    exact Finset.finite_toSet _
  exact (Set.ncard_le_ncard (fun α hα => pointwise α hα) h_finite).trans (ncard_eval_eq_zero_le hP)

end Roots

/-! ## Challenge checks -/

/-- The contract of a circuit that checks a statement about phase-1 values with one challenge. -/
structure ChallengeCheck (Native : Type) [Field Native] where
  /-- the meaning of the phase-1 values, committed before the challenge -/
  Phase1 : Type
  /-- how the phase-1 values are laid out -/
  phase1CType : CType Native Phase1
  /-- assumed of the phase-1 values -/
  Assumptions : Phase1 → Prop := fun _ => True
  /-- the statement the check establishes, with a soundness error -/
  Statement : Phase1 → Prop
  /-- what the circuit proves at the challenge: this polynomial vanishes there -/
  poly : Phase1 → Native[X]
  /-- the symbolic argument: the polynomial identity implies the statement -/
  symbolic : ∀ x, Assumptions x → poly x = 0 → Statement x
  /-- assumed for completeness, of the phase-1 values and the challenge; typically the statement,
  and that the challenge avoids the points where the honest prover would divide by zero -/
  ProverAssumptions : Phase1 → Native → Prop

namespace ChallengeCheck
variable {Native : Type} [Field Native] (cc : ChallengeCheck Native)

/-- The interface a challenge check is implemented against: phase-1 values and a challenge in,
nothing out; the spec is the pointwise half of the check. -/
@[reducible]
def interface : Interface Native where
  input := cc.Phase1 × Native
  inputCType := cc.phase1CType ×ᵗ .native
  output := Unit
  outputCType := .unit
  Assumptions := fun (x, _) => cc.Assumptions x
  Spec := fun (x, α) _ => (cc.poly x).eval α = 0
  ProverAssumptions := fun (x, α) => cc.ProverAssumptions x α

variable {B : Backend} [Field B.Native] {cc : ChallengeCheck B.Native}

/-- The challenges at which a prover is accepted, for phase-1 values `x`: some assignment of all
cells (chosen after the challenge, as an arbitrary function of it) has inputs that mean `x` and the
challenge, and satisfies the constraints. -/
def Accepts (impl : Impl B cc.interface) (x : cc.Phase1) (α : B.Native) : Prop :=
  ∃ (s : B.State) (env : B.Cell → B.Native) (input : cc.interface.Input B.Var),
    cc.interface.inputCType.Valid (B.evalT env input) ∧
    cc.interface.inputCType.decode (B.evalT env input) = (x, α) ∧
    ((impl.main input).operations s).ConstraintsHold env s

/-- **Soundness error.** For phase-1 values satisfying the assumptions but not the statement, the
prover is accepted at no more challenges than the degree of the check's polynomial. -/
theorem soundness_error (impl : Impl B cc.interface) (x : cc.Phase1) (h_assumptions : cc.Assumptions x)
    (h_false : ¬cc.Statement x) :
    {α | Accepts impl x α}.ncard ≤ (cc.poly x).natDegree := by
  refine ncard_accepting_le (cc.poly x) ?_ (cc.symbolic x h_assumptions) h_false
  rintro α ⟨s, env, input, h_valid, h_decode, h_holds⟩
  have h := impl.soundness s env input ⟨h_valid, by rw [h_decode]; exact h_assumptions⟩
    (Ops.soundnessHold_of_constraintsHold (impl.consistent input s) h_holds)
  have h_spec := h.2
  rw [h_decode] at h_spec
  exact h_spec

/-- **Completeness.** On inputs that exist in the heap and mean phase-1 values and a challenge
satisfying the prover assumptions, an honest assignment satisfies the constraints. -/
theorem completeness (impl : Impl B cc.interface) (x : cc.Phase1) (α : B.Native)
    (s : B.State) (env₀ : B.Cell → B.Native) (input : cc.interface.Input B.Var)
    (h_in : B.footprintT input ⊆ B.Alloc s)
    (h_valid : cc.interface.inputCType.Valid (B.evalT env₀ input))
    (h_decode : cc.interface.inputCType.decode (B.evalT env₀ input) = (x, α))
    (h_prover : cc.ProverAssumptions x α) :
    ∃ env, (∀ c ∈ B.Alloc s, env c = env₀ c) ∧ ((impl.main input).operations s).ConstraintsHold env s := by
  obtain ⟨env, h_agree, h_holds, -⟩ := impl.exists_honest_env input s env₀ h_in
    ⟨h_valid, by rw [h_decode]; exact h_prover⟩
  exact ⟨env, h_agree, h_holds⟩

end ChallengeCheck

/--
Discharge the spatial obligation of a challenge check: `spatial`, after splitting what the input
reads into what the phase-1 values read and what the challenge reads. (The input type of
`cc.interface` is `(cc.phase1CType ×ᵗ .native).Shape` only after unfolding the interface, which
`simp` does not do inside `footprintT`.)
-/
syntax "challenge_spatial" : tactic

/-- The second half of `spatial`: split a normalized spatial goal along `∧` and `→` and close the
leaves from the hypotheses. For loop lemmas, where the goal is not an `Impl`'s obligation. -/
syntax "spatial_split" : tactic

meta section
open Lean Elab Tactic in
elab_rules : tactic
  | `(tactic| challenge_spatial) => do
    evalTactic (← `(tactic| intro input s h_in))
    destructProds
    evalTactic (← `(tactic| (
      obtain ⟨h_x, h_α⟩ := Backend.footprintT_ctypeProd_subset.mp h_in
      simp only [circuit_norm, Set.union_subset_iff, Set.empty_subset, and_imp] at h_x h_α ⊢
      try casesm* _ ∧ _)))
    spatialSplit #[]
  | `(tactic| spatial_split) => spatialSplit #[]
end

end Clean2
