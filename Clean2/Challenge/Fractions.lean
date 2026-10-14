/-
Partial fractions with simple poles: the symbolic arguments behind logUp-style protocols.

- `eq_zero_of_sum_div_eq_zero`: if `∑_{y ∈ S} d y / (X - y) = 0` for distinct `y`, every `d y` is 0.
- `balance_iff`: a sum of simple fractions `∑ m i / (X - v i)` vanishes iff, for every value `y`,
  the multiplicities of `y` add up to zero. This is bus balance, with signed multiplicities.
- `logUp_iff`: the lookup form, a table with multiplicities against lookups.
-/
module

public import Clean2.Challenge.Symbolic
public import Mathlib.Algebra.BigOperators.Field

@[expose] public section

namespace Clean2
open Polynomial

namespace Fractions
variable {F : Type} [Field F] [DecidableEq F]

/-- Uniqueness of partial fractions with simple poles. -/
theorem eq_zero_of_sum_div_eq_zero (S : Finset F) (d : F → F)
    (h : ∑ y ∈ S, RatFunc.C (d y) / (RatFunc.X - RatFunc.C y) = 0) : ∀ y ∈ S, d y = 0 := by
  -- clear denominators: `P = ∑ d y ∏_{z ≠ y} (X - z)` is zero
  set P : F[X] := ∑ y ∈ S, Polynomial.C (d y) * ∏ z ∈ S.erase y, (Polynomial.X - Polynomial.C z)
  have hP : algebraMap F[X] (RatFunc F) P =
      (∏ z ∈ S, (RatFunc.X - RatFunc.C z)) * ∑ y ∈ S, RatFunc.C (d y) / (RatFunc.X - RatFunc.C y) := by
    rw [Finset.mul_sum, map_sum]
    refine Finset.sum_congr rfl fun y hy => ?_
    rw [← Finset.mul_prod_erase S _ hy]
    simp only [map_mul, map_prod, map_sub, RatFunc.algebraMap_C, RatFunc.algebraMap_X]
    field_simp [RatFunc.X_sub_C_ne_zero y]
  have hP0 : P = 0 := by
    apply RatFunc.algebraMap_injective F
    rw [hP, h, mul_zero, map_zero]
  -- and at `y`, only the `y`-th term survives
  intro y hy
  have h_eval := congrArg (Polynomial.eval y) hP0
  rw [eval_zero, eval_finsetSum, Finset.sum_eq_single y] at h_eval
  · simp only [eval_mul, eval_C, eval_prod, eval_sub, eval_X] at h_eval
    refine (mul_eq_zero.mp h_eval).resolve_right ?_
    exact Finset.prod_ne_zero_iff.mpr fun z hz => sub_ne_zero.mpr (Finset.ne_of_mem_erase hz).symm
  · intro z hz hzy
    simp only [eval_mul, eval_prod, eval_sub, eval_X, eval_C]
    rw [Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨Ne.symm hzy, hy⟩) (sub_self y), mul_zero]
  · intro h; exact absurd hy h

/-- Group a sum of simple fractions by pole. -/
theorem sum_div_eq_sum_poles {n : ℕ} (S : Finset F) (g : Fin n → F) (w : Fin n → F) (hg : ∀ i, g i ∈ S) :
    ∑ i, RatFunc.C (w i) / (RatFunc.X - RatFunc.C (g i)) =
      ∑ y ∈ S, RatFunc.C (∑ i ∈ Finset.univ.filter (fun i => g i = y), w i) / (RatFunc.X - RatFunc.C y) := by
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := S) (g := g) (fun i _ => hg i)]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [map_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [(Finset.mem_filter.mp hi).2]

/-- The logUp statement, as an identity of rational functions. -/
theorem logUp_iff {n l : ℕ} (t m : Fin n → F) (f : Fin l → F) :
    ∑ i, RatFunc.C (m i) / (RatFunc.X - RatFunc.C (t i)) = ∑ j, (RatFunc.X - RatFunc.C (f j))⁻¹ ↔
      ∀ y, ((Finset.univ.filter fun j => f j = y).card : F) =
        ∑ i ∈ Finset.univ.filter (fun i => t i = y), m i := by
  set S := Finset.univ.image t ∪ Finset.univ.image f
  have ht : ∀ i, t i ∈ S := fun i => Finset.mem_union_left _ (Finset.mem_image_of_mem t (Finset.mem_univ i))
  have hf : ∀ j, f j ∈ S := fun j => Finset.mem_union_right _ (Finset.mem_image_of_mem f (Finset.mem_univ j))
  have h_one : ∑ j, (RatFunc.X - RatFunc.C (f j))⁻¹ =
      ∑ j, RatFunc.C (1 : F) / (RatFunc.X - RatFunc.C (f j)) := by simp
  rw [h_one, sum_div_eq_sum_poles S t m ht, sum_div_eq_sum_poles S f (fun _ => 1) hf, ← sub_eq_zero,
    ← Finset.sum_sub_distrib]
  simp only [← sub_div, ← map_sub, Finset.sum_const, nsmul_eq_mul, mul_one]
  constructor
  · intro h y
    by_cases hy : y ∈ S
    · exact (sub_eq_zero.mp (eq_zero_of_sum_div_eq_zero S _ h y hy)).symm
    · have h_t : Finset.univ.filter (fun i => t i = y) = ∅ :=
        Finset.filter_eq_empty_iff.mpr fun i _ hi => hy (hi ▸ ht i)
      have h_f : Finset.univ.filter (fun j => f j = y) = ∅ :=
        Finset.filter_eq_empty_iff.mpr fun j _ hj => hy (hj ▸ hf j)
      simp [h_t, h_f]
  · intro h
    refine Finset.sum_eq_zero fun y _ => ?_
    rw [h y, sub_self, map_zero, zero_div]

/-- **Bus balance.** A sum of simple fractions vanishes iff every value's multiplicities add up
to zero. -/
theorem balance_iff {n : ℕ} (v m : Fin n → F) :
    ∑ i, RatFunc.C (m i) / (RatFunc.X - RatFunc.C (v i)) = 0 ↔
      ∀ y, ∑ i ∈ Finset.univ.filter (fun i => v i = y), m i = 0 := by
  set S := Finset.univ.image v
  have hv : ∀ i, v i ∈ S := fun i => Finset.mem_image_of_mem v (Finset.mem_univ i)
  rw [sum_div_eq_sum_poles S v m hv]
  constructor
  · intro h y
    by_cases hy : y ∈ S
    · exact eq_zero_of_sum_div_eq_zero S _ h y hy
    · have h_v : Finset.univ.filter (fun i => v i = y) = ∅ :=
        Finset.filter_eq_empty_iff.mpr fun i _ hi => hy (hi ▸ hv i)
      simp [h_v]
  · intro h
    refine Finset.sum_eq_zero fun y _ => ?_
    rw [h y, map_zero, zero_div]

end Fractions
end Clean2
