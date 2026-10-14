/-
The boundary: from "the value is zero at the challenge" to "the identity holds".

`AssertIdentity.interface k d R` takes committed values `c`, a value `x`, and the challenge `α`.
It assumes that `x` stands for `R c` at `α` (`x ≙[α] R c`, typically the final value of a running
sum or product), and that `R c` has a numerator of degree at most `d`. Its spec is the identity
`R c = 0`, an equation between rational functions: the challenge is gone.

The implementation asserts `x = 0` and assumes, for soundness, the rare event that `R c ≠ 0` but
`α` is a root of its numerator: at most `d` challenges. This is the only place where a
challenge costs soundness.
-/
module

public import Clean2.Challenge.Symbolic
public import Clean2.Functionalities.Arith

@[expose] public section

namespace Clean2
open Polynomial

namespace AssertIdentity
variable {F : Type} [Field F]

/-- `x` stands for `R c`, and is zero at the challenge: so `R c = 0`. -/
@[reducible]
def interface (k d : ℕ) (R : Vector F k → RatFunc F) : Interface F where
  input := (Vector F k × F) × F
  inputCType := (.natives k ×ᵗ .native) ×ᵗ .native
  output := Unit
  outputCType := .unit
  Assumptions := fun ((c, x), α) => (x ≙[α] R c) ∧ NumDegLE (R c) d
  Spec := fun ((c, _), _) _ => R c = 0
  ProverAssumptions := fun ((c, x), α) => (x ≙[α] R c) ∧ R c = 0

/-- The bad challenges: `R c` is not zero, but its numerator, of degree at most `d`, vanishes. -/
def Bad (d : ℕ) {k : ℕ} (R : Vector F k → RatFunc F) (c : Vector F k) (a : F) : Prop :=
  R c ≠ 0 ∧ (RatFunc.num (R c)).eval a = 0 ∧ (RatFunc.num (R c)).natDegree ≤ d

theorem encard_bad_le (d : ℕ) {k : ℕ} (R : Vector F k → RatFunc F) (c : Vector F k) :
    {a | Bad d R c a}.encard ≤ d := by
  by_cases hd : (RatFunc.num (R c)).natDegree ≤ d
  · refine (Set.encard_le_encard fun a ha => ?_).trans ((encard_polyBad_le _).trans (Nat.cast_le.mpr hd))
    exact ⟨fun h => ha.1 (RatFunc.num_eq_zero_iff.mp h), ha.2.1⟩
  · simp [Bad, hd]

variable {B : Backend} [Field B.Native]

/-- The rare event of a boundary. It depends on the committed values and the challenge only. -/
def event (d : ℕ) {k : ℕ} (R : Vector B.Native k → RatFunc B.Native) (c : Vector B.Var k) (α : B.Var) :
    RareEvent B where
  committed := c
  challenge := α
  Bad := Bad d R
  bound := d
  encard_bad_le := encard_bad_le d R

variable (arith : ∀ n, Impl B (Arith.interface n))

def impl {k : ℕ} (d : ℕ) (R : Vector B.Native k → RatFunc B.Native) : Impl B (interface k d R) where
  main | ((c, x), α) => do
    arith .assertZero x
    Circuit.assumeRare (event d R c α)
  spatial := by
    intro ((c, x), α) s h
    obtain ⟨⟨-, h_x⟩, -⟩ := (Backend.footprintT_ctypeProd_subset.mp h).imp_left
      Backend.footprintT_ctypeProd_subset.mp
    simp only [circuit_norm] at h_x ⊢
    exact ⟨h_x, fun _ _ => Set.empty_subset _⟩
  soundness := by
    intro s env ((c, x), α) h_assumptions h
    simp only [circuit_norm, event] at h_assumptions h ⊢
    obtain ⟨h_rep, h_deg⟩ := h_assumptions
    obtain ⟨h_zero, h_rare⟩ := h
    rcases h_rep.eq_zero_or_bad h_zero with h_R | ⟨h_ne, h_root⟩
    · exact h_R
    · exact absurd ⟨h_ne, h_root, h_deg.natDegree_num_le⟩ h_rare
  completeness := by
    intro s env ((c, x), α) _ h_prover
    simp only [circuit_norm, event] at h_prover ⊢
    obtain ⟨h_rep, h_R⟩ := h_prover
    exact ⟨(h_R ▸ h_rep).eq_zero, fun h_bad => h_bad.1 h_R⟩

end AssertIdentity
end Clean2
