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

public import Clean2.Challenge.Identity
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

namespace Clean2
open Polynomial

namespace Permutation
variable {Native : Type} [Field Native]

/-- The entries of a vector, as a multiset. -/
def elems {n : ℕ} (v : Vector Native n) : Multiset Native := Finset.univ.val.map fun i : Fin n => v[i]

omit [Field Native] in
/-- Equal multisets have equal products. -/
theorem prod_eq_of_elems_eq {M : Type} [CommMonoid M] {n : ℕ} {a b : Vector Native n}
    (h : elems a = elems b) (f : Native → M) : ∏ i : Fin n, f a[i] = ∏ i : Fin n, f b[i] := by
  rw [Finset.prod_eq_multiset_prod, Finset.prod_eq_multiset_prod]
  have h := congrArg (fun m => (m.map f).prod) h
  simp only [elems, Multiset.map_map] at h
  exact h

theorem prod_X_sub_C_eq {n : ℕ} (v : Vector Native n) :
    ∏ i : Fin n, (RatFunc.X - RatFunc.C v[i]) =
      algebraMap Native[X] (RatFunc Native) ((elems v).map fun x => X - C x).prod := by
  have h : ∏ i : Fin n, (X - C v[i]) = ((elems v).map fun x => X - C x).prod := by
    rw [Finset.prod_eq_multiset_prod, elems, Multiset.map_map]; rfl
  rw [← h, map_prod]
  simp [RatFunc.algebraMap_X, RatFunc.algebraMap_C]

/-- The symbolic argument: equal products of linear factors have the same roots. -/
theorem elems_eq_of_prod_eq {n : ℕ} {a b : Vector Native n}
    (h : ∏ i : Fin n, (RatFunc.X - RatFunc.C a[i]) = ∏ i : Fin n, (RatFunc.X - RatFunc.C b[i])) :
    elems a = elems b := by
  rw [prod_X_sub_C_eq, prod_X_sub_C_eq] at h
  have h := congrArg roots (RatFunc.algebraMap_injective Native h)
  rwa [roots_multiset_prod_X_sub_C, roots_multiset_prod_X_sub_C] at h

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
    exact ⟨Backend.footprintT_ctypeProd_subset.mpr ⟨Identity.footprintT_append_subset h_a h_b, h_α⟩,
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
    exact ⟨Backend.footprintT_ctypeProd_subset.mpr ⟨Identity.footprintT_append_subset h_a h_b, h_α⟩,
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
