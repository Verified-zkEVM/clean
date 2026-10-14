/-
Symbolic meanings: what a value computed after the challenge stands for.

`x ≙[α] R` says that the value `x` stands for the rational function `R` at the challenge `α`:
`R` has no pole at `α`, and evaluates to `x` there. `R` is built from committed values and `X`,
so it is fixed before the challenge is sampled. Only values that the constraints pin down get a
meaning: an unconstrained witness has none.

Users never prove `≙` from scratch. Gadgets have ordinary pointwise specs (`out = acc + m / (α - v)`),
and the lemmas here carry meanings through them: `≙` respects constants, `X`, `+ - * /`, sums and
products. The one place where a meaning is turned into a symbolic fact is the boundary
(`eq_zero_or_bad`): if `x ≙[α] R` and `x = 0`, then `R ≡ 0`, unless `α` is a root of `R`'s
numerator. That is a rare event, at no more challenges than the numerator's degree, which
`NumDegLE` bounds statically.
-/
module

public import Clean2.Challenge.Basic
public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination

@[expose] public section

namespace Clean2
open Polynomial

variable {F : Type} [Field F]

local notation "A" => algebraMap F[X] (RatFunc F)

/-- The value `x` stands for the rational function `R` at `α`: `R` has no pole at `α`, and
evaluates to `x` there. -/
def Represents (α x : F) (R : RatFunc F) : Prop :=
  ∃ N D : F[X], D.eval α ≠ 0 ∧ R = A N / A D ∧ x = N.eval α / D.eval α

@[inherit_doc] notation:50 x " ≙[" α "] " R:51 => Represents α x R

namespace Represents
variable {α x y : F} {R S : RatFunc F}

theorem const (c : F) : c ≙[α] RatFunc.C c :=
  ⟨Polynomial.C c, 1, by simp, by simp [RatFunc.algebraMap_C], by simp⟩

theorem X : α ≙[α] RatFunc.X :=
  ⟨Polynomial.X, 1, by simp, by simp [RatFunc.algebraMap_X], by simp⟩

theorem add (hx : x ≙[α] R) (hy : y ≙[α] S) : x + y ≙[α] R + S := by
  obtain ⟨N, D, hD, rfl, rfl⟩ := hx
  obtain ⟨N', D', hD', rfl, rfl⟩ := hy
  have hD0 : D ≠ 0 := fun h => hD (by simp [h])
  have hD0' : D' ≠ 0 := fun h => hD' (by simp [h])
  refine ⟨N * D' + N' * D, D * D', by simp [hD, hD'], ?_, ?_⟩
  · rw [div_add_div _ _ (RatFunc.algebraMap_ne_zero hD0) (RatFunc.algebraMap_ne_zero hD0')]
    simp only [map_add, map_mul]; ring
  · rw [div_add_div _ _ hD hD']; simp only [eval_add, eval_mul]; ring

theorem sub (hx : x ≙[α] R) (hy : y ≙[α] S) : x - y ≙[α] R - S := by
  obtain ⟨N, D, hD, rfl, rfl⟩ := hx
  obtain ⟨N', D', hD', rfl, rfl⟩ := hy
  have hD0 : D ≠ 0 := fun h => hD (by simp [h])
  have hD0' : D' ≠ 0 := fun h => hD' (by simp [h])
  refine ⟨N * D' - N' * D, D * D', by simp [hD, hD'], ?_, ?_⟩
  · rw [div_sub_div _ _ (RatFunc.algebraMap_ne_zero hD0) (RatFunc.algebraMap_ne_zero hD0')]
    simp only [map_sub, map_mul]; ring
  · rw [div_sub_div _ _ hD hD']; simp only [eval_sub, eval_mul]; ring

theorem mul (hx : x ≙[α] R) (hy : y ≙[α] S) : x * y ≙[α] R * S := by
  obtain ⟨N, D, hD, rfl, rfl⟩ := hx
  obtain ⟨N', D', hD', rfl, rfl⟩ := hy
  refine ⟨N * N', D * D', by simp [hD, hD'], ?_, ?_⟩
  · rw [div_mul_div_comm]; simp only [map_mul]
  · rw [div_mul_div_comm]; simp only [eval_mul]

/-- Division by a non-zero value: the divisor's meaning has no zero at `α`. -/
theorem div (hx : x ≙[α] R) (hy : y ≙[α] S) (hne : y ≠ 0) : x / y ≙[α] R / S := by
  obtain ⟨N, D, hD, rfl, rfl⟩ := hx
  obtain ⟨N', D', hD', rfl, rfl⟩ := hy
  have hN' : N'.eval α ≠ 0 := fun h => hne (by rw [h, zero_div])
  refine ⟨N * D', D * N', by simp [hD, hN'], ?_, ?_⟩
  · rw [div_div_div_eq]; simp only [map_mul]
  · rw [div_div_div_eq]; simp only [eval_mul]

theorem congr (hx : x ≙[α] R) (h : R = S) : x ≙[α] S := h ▸ hx

theorem sum {ι : Type} (s : Finset ι) {f : ι → F} {R : ι → RatFunc F} (h : ∀ i ∈ s, f i ≙[α] R i) :
    ∑ i ∈ s, f i ≙[α] ∑ i ∈ s, R i := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using const (α := α) (0 : F)
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact add (h i (Finset.mem_insert_self i s)) (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem prod {ι : Type} (s : Finset ι) {f : ι → F} {R : ι → RatFunc F} (h : ∀ i ∈ s, f i ≙[α] R i) :
    ∏ i ∈ s, f i ≙[α] ∏ i ∈ s, R i := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using const (α := α) (1 : F)
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi]
    exact mul (h i (Finset.mem_insert_self i s)) (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

/-- A value that stands for `0` is zero. -/
theorem eq_zero (h : x ≙[α] 0) : x = 0 := by
  obtain ⟨N, D, hD, hR, rfl⟩ := h
  have hD0 : D ≠ 0 := fun h => hD (by simp [h])
  have hN : N = 0 := by
    rw [eq_comm, div_eq_zero_iff] at hR
    exact RatFunc.algebraMap_injective F
      ((hR.resolve_right (RatFunc.algebraMap_ne_zero hD0)).trans (map_zero _).symm)
  rw [hN, eval_zero, zero_div]

/-- **The boundary.** A value that stands for `R` and is zero: either `R ≡ 0`, or `α` is a root of
`R`'s numerator. -/
theorem eq_zero_or_bad (h : x ≙[α] R) (hx : x = 0) :
    R = 0 ∨ (R ≠ 0 ∧ (RatFunc.num R).eval α = 0) := by
  by_cases hR : R = 0
  · exact .inl hR
  refine .inr ⟨hR, ?_⟩
  obtain ⟨N, D, hD, rfl, rfl⟩ := h
  have hD0 : D ≠ 0 := fun h => hD (by simp [h])
  have hNα : N.eval α = 0 := by
    rw [div_eq_zero_iff] at hx
    exact hx.resolve_right hD
  -- `N / D = num / denom`, so `N * denom = num * D`, and at `α`: `0 = num(α) * D(α)`
  have h_eq : N * RatFunc.denom (A N / A D) = RatFunc.num (A N / A D) * D := by
    apply RatFunc.algebraMap_injective F
    have h1 := RatFunc.num_div_denom (A N / A D)
    rw [div_eq_div_iff (RatFunc.algebraMap_ne_zero (RatFunc.denom_ne_zero _))
      (RatFunc.algebraMap_ne_zero hD0)] at h1
    simp only [map_mul]
    linear_combination -h1
  have h_at := congrArg (Polynomial.eval α) h_eq
  rw [eval_mul, eval_mul, hNα, zero_mul, eq_comm, mul_eq_zero] at h_at
  exact h_at.resolve_right hD

end Represents

/-- The divisors users write: `X - c` is never zero. -/
@[simp] theorem _root_.RatFunc.X_sub_C_ne_zero (c : F) : (RatFunc.X - RatFunc.C c : RatFunc F) ≠ 0 := by
  rw [← RatFunc.algebraMap_X, ← RatFunc.algebraMap_C, ← map_sub]
  exact RatFunc.algebraMap_ne_zero (Polynomial.X_sub_C_ne_zero c)

/-- So is a product of them: `simp` uses this to discharge `div_eq_one_iff_eq`. -/
@[simp] theorem _root_.RatFunc.prod_X_sub_C_ne_zero {n : ℕ} (c : Fin n → F) :
    ∏ i, (RatFunc.X - RatFunc.C (c i) : RatFunc F) ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun i _ => RatFunc.X_sub_C_ne_zero (c i)

/-! ### Static degree bounds -/

/-- `R` is `N / D` with `deg N ≤ d`: so its numerator has degree at most `d`. -/
def NumDegLE (R : RatFunc F) (d : ℕ) : Prop :=
  ∃ N D : F[X], D ≠ 0 ∧ R = A N / A D ∧ N.natDegree ≤ d

theorem NumDegLE.natDegree_num_le {R : RatFunc F} {d : ℕ} (h : NumDegLE R d) :
    (RatFunc.num R).natDegree ≤ d := by
  obtain ⟨N, D, hD, rfl, hN⟩ := h
  by_cases hN0 : N = 0
  · simp [hN0]
  have h_dvd : RatFunc.num (A N / A D) ∣ N := (RatFunc.num_dvd hN0).mpr ⟨D, hD, rfl⟩
  exact (natDegree_le_of_dvd h_dvd hN0).trans hN

/-- A sum of simple fractions `∑ c i / (X - a i)` has a numerator of degree at most `n`. -/
theorem NumDegLE.sum_div_X_sub_C {n : ℕ} (c a : Fin n → F) :
    NumDegLE (∑ i, RatFunc.C (c i) / (RatFunc.X - RatFunc.C (a i))) n := by
  classical
  refine ⟨∑ i, Polynomial.C (c i) * ∏ j ∈ Finset.univ.erase i, (Polynomial.X - Polynomial.C (a j)),
    ∏ j, (Polynomial.X - Polynomial.C (a j)), Finset.prod_ne_zero_iff.mpr fun j _ => X_sub_C_ne_zero _, ?_, ?_⟩
  · rw [eq_div_iff (RatFunc.algebraMap_ne_zero (Finset.prod_ne_zero_iff.mpr fun j _ => X_sub_C_ne_zero _)),
      Finset.sum_mul, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
    simp only [map_mul, map_prod, map_sub, RatFunc.algebraMap_C, RatFunc.algebraMap_X]
    rw [← mul_assoc, div_mul_cancel₀ _ (RatFunc.X_sub_C_ne_zero (a i)), mul_comm]
  · refine (natDegree_sum_le_of_forall_le _ _ fun i _ => ?_)
    refine (natDegree_C_mul_le _ _).trans ((natDegree_prod_le _ _).trans ?_)
    calc ∑ j ∈ Finset.univ.erase i, (Polynomial.X - Polynomial.C (a j)).natDegree
        = ∑ j ∈ Finset.univ.erase i, 1 := Finset.sum_congr rfl fun j _ => natDegree_X_sub_C _
      _ ≤ n := by simp

/-- `∏ (X - a i) / (X - b i) - 1` has a numerator of degree at most `n`. -/
theorem NumDegLE.prod_div_sub_one {n : ℕ} (a b : Fin n → F) :
    NumDegLE (∏ i, (RatFunc.X - RatFunc.C (a i)) / (RatFunc.X - RatFunc.C (b i)) - 1) n := by
  refine ⟨∏ i, (Polynomial.X - Polynomial.C (a i)) - ∏ i, (Polynomial.X - Polynomial.C (b i)),
    ∏ i, (Polynomial.X - Polynomial.C (b i)), Finset.prod_ne_zero_iff.mpr fun j _ => X_sub_C_ne_zero _, ?_, ?_⟩
  · rw [eq_div_iff (RatFunc.algebraMap_ne_zero (Finset.prod_ne_zero_iff.mpr fun j _ => X_sub_C_ne_zero _))]
    simp only [map_sub, map_prod, RatFunc.algebraMap_C, RatFunc.algebraMap_X, sub_mul, one_mul,
      Finset.prod_div_distrib]
    rw [div_mul_cancel₀ _ (Finset.prod_ne_zero_iff.mpr fun j _ => RatFunc.X_sub_C_ne_zero _)]
  · refine (natDegree_sub_le _ _).trans (max_le ?_ ?_) <;>
    · rw [natDegree_prod _ _ fun i _ => X_sub_C_ne_zero _]
      simp

end Clean2
