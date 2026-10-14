/-
A permutation check, as a user writes it: an ordinary circuit, with an ordinary spec.

`b` is a permutation of `a`, using a challenge `α`. Two variants, both one call to an identity:

- `Permutation.impl`, product form: `∏ (X - a i) - ∏ (X - b i) = 0`. No division, so complete at
  every challenge; `2n` multiplications on R1CS; error bound `n`.
- `PermutationQuotient.impl`, quotient form: `∏ (X - a i) / (X - b i) - 1 = 0`. A division per
  entry, so completeness needs the challenge to avoid every `b i`; error bound `2n`.

The proofs only see the identity, as an equation between rational functions; the symbolic
argument is that equal products of linear factors have equal roots.
-/
module

public import Clean2.Challenge.Variants.Identity
public import Clean2.Challenge.Fractions
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

namespace Clean2
open Polynomial

namespace Permutation
variable {Native : Type} [Field Native]

/-- `b` is a permutation of `a`. The challenge is an input, the spec does not mention it. -/
@[reducible]
def interface (n : ℕ) : Interface Native where
  input := (Vector Native n × Vector Native n) × Native
  inputCType := (.natives n ×ᵗ .natives n) ×ᵗ .native
  output := Unit
  outputCType := .unit
  Spec := fun ((a, b), _) _ => elems a = elems b
  ProverAssumptions := fun ((a, b), _) => elems a = elems b

/-- `∏ (X - a i) - ∏ (X - b i)`, in the committed values `a ++ b`. -/
def expr (n : ℕ) : RExpr Native (n + n) :=
  .prod n (fun i => .X - .leaf (Fin.castAdd n i)) - .prod n (fun i => .X - .leaf (Fin.natAdd n i))

variable {B : Backend} [Field B.Native]
  (identity : ∀ {k : ℕ} (e : RExpr B.Native k), Impl B (Identity.interface e))

def impl (n : ℕ) : Impl B (interface n) where
  main | ((a, b), α) => identity (expr n) (a ++ b, α)
  spatial := by
    intro ((a, b), α) s h
    obtain ⟨⟨h_a, h_b⟩, h_α⟩ := (Backend.footprintT_ctypeProd_subset.mp h).imp_left
      Backend.footprintT_ctypeProd_subset.mp
    simp only [circuit_norm]
    exact ⟨Backend.footprintT_ctypeProd_subset.mpr ⟨Backend.footprintT_append_subset h_a h_b, h_α⟩,
      fun _ _ => Set.empty_subset _⟩
  soundness := by
    intro s env ((a, b), α) _ h
    simp only [circuit_norm] at h ⊢
    apply elems_eq_of_prod_eq
    simpa [expr, sub_eq_zero] using h (by simp [expr])
  completeness := by
    intro s env ((a, b), α) _ h_prover
    simp only [circuit_norm] at h_prover ⊢
    have h := prod_eq_of_elems_eq h_prover (fun x => RatFunc.X - RatFunc.C x)
    exact ⟨by simp [expr], by simpa [expr, sub_eq_zero] using h, by simp [expr]⟩

end Permutation

namespace PermutationQuotient
open Permutation
variable {Native : Type} [Field Native]

/-- `b` is a permutation of `a`. The honest prover divides by `α - b i`, so it needs the challenge
to avoid the entries of `b`. -/
@[reducible]
def interface (n : ℕ) : Interface Native where
  input := (Vector Native n × Vector Native n) × Native
  inputCType := (.natives n ×ᵗ .natives n) ×ᵗ .native
  output := Unit
  outputCType := .unit
  Spec := fun ((a, b), _) _ => elems a = elems b
  ProverAssumptions := fun ((a, b), α) => elems a = elems b ∧ ∀ i : Fin n, α ≠ b[i]

/-- `∏ (X - a i) / (X - b i) - 1`. -/
def expr (n : ℕ) : RExpr Native (n + n) :=
  .prod n (fun i => (.X - .leaf (Fin.castAdd n i)) / (.X - .leaf (Fin.natAdd n i))) - .const 1

variable {B : Backend} [Field B.Native]
  (identity : ∀ {k : ℕ} (e : RExpr B.Native k), Impl B (Identity.interface e))

def impl (n : ℕ) : Impl B (interface n) where
  main | ((a, b), α) => identity (expr n) (a ++ b, α)
  spatial := by
    intro ((a, b), α) s h
    obtain ⟨⟨h_a, h_b⟩, h_α⟩ := (Backend.footprintT_ctypeProd_subset.mp h).imp_left
      Backend.footprintT_ctypeProd_subset.mp
    simp only [circuit_norm]
    exact ⟨Backend.footprintT_ctypeProd_subset.mpr ⟨Backend.footprintT_append_subset h_a h_b, h_α⟩,
      fun _ _ => Set.empty_subset _⟩
  soundness := by
    intro s env ((a, b), α) _ h
    simp only [circuit_norm] at h ⊢
    apply elems_eq_of_prod_eq
    simpa [expr, sub_eq_zero, div_eq_one_iff_eq] using h (by simp [expr])
  completeness := by
    intro s env ((a, b), α) _ h_prover
    simp only [circuit_norm] at h_prover ⊢
    obtain ⟨h_perm, h_avoid⟩ := h_prover
    have h := prod_eq_of_elems_eq h_perm (fun x => RatFunc.X - RatFunc.C x)
    exact ⟨by simp [expr], by simpa [expr, sub_eq_zero, div_eq_one_iff_eq] using h,
      by simpa [expr, sub_eq_zero] using h_avoid⟩

end PermutationQuotient
end Clean2
