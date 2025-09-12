import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.BigOperators.Fin

set_option linter.unusedSimpArgs false

namespace Fin

/-! ## Lemmas about Fin.foldl and sums -/

/-- The ZMod.val of a Fin.foldl sum is bounded by the sum of individual ZMod.vals -/
lemma foldl_sum_val_bound {p : ℕ} [Fact p.Prime] {ops : ℕ} (f : Fin ops → ZMod p) (M : ℕ)
    (h_bound : ∀ j : Fin ops, (f j).val ≤ M) (h_no_overflow : ops * M < p) :
    (Fin.foldl ops (fun sum j => sum + f j) 0).val ≤ ops * M := by
  -- Use induction on ops
  induction ops with
  | zero =>
    simp only [Fin.foldl_zero, ZMod.val_zero, zero_mul, le_refl]
  | succ k ih =>
    -- For the inductive step, use Fin.foldl_succ_last
    rw [Fin.foldl_succ_last]
    -- The key insight: use ZMod.val_add_of_lt when the sum doesn't overflow
    have h_partial_bound := ih (fun j => f j.castSucc)
                               (fun j => h_bound j.castSucc)
                               (by
                                 -- k * M < (k+1) * M < p
                                 apply Nat.lt_of_le_of_lt _ h_no_overflow
                                 apply Nat.mul_le_mul_right
                                 exact Nat.le_succ k)

    -- Show that the partial sum + new element doesn't overflow
    have h_add_lt : (Fin.foldl k (fun sum j => sum + f j.castSucc) 0).val + (f (Fin.last k)).val < p := by
      apply Nat.lt_of_le_of_lt
      · apply Nat.add_le_add h_partial_bound (h_bound (Fin.last k))
      · rw [← Nat.succ_mul]
        exact h_no_overflow

    -- Use the fact that ZMod.val preserves addition when no overflow
    rw [ZMod.val_add_of_lt h_add_lt]
    -- We want to show: partial_sum + element ≤ (k+1) * M
    -- We know: partial_sum ≤ k * M and element ≤ M
    -- So: partial_sum + element ≤ k * M + M = (k+1) * M
    have h_succ : (k + 1) * M = k * M + M := by rw [Nat.succ_mul]
    rw [h_succ]
    apply Nat.add_le_add h_partial_bound (h_bound (Fin.last k))

/-- Factoring out a constant from a foldl sum -/
lemma foldl_factor_const {α : Type*} [CommSemiring α] {n : ℕ} (f : Fin n → α) (c : α) (init : α) :
    Fin.foldl n (fun acc i => acc + f i * c) init =
    init + c * Fin.foldl n (fun acc i => acc + f i) 0 := by
  induction n generalizing init with
  | zero => simp [Fin.foldl_zero]
  | succ m ih =>
    -- Unfold the foldl on both sides
    simp only [Fin.foldl_succ_last]
    -- Apply IH to the castSucc part
    have h_eq : Fin.foldl m (fun x1 x2 => x1 + f x2.castSucc * c) init =
                Fin.foldl m (fun x1 x2 => x1 + (f ∘ Fin.castSucc) x2 * c) init := by
      congr
    rw [h_eq, ih (f ∘ Fin.castSucc)]
    -- Now simplify the RHS
    have h_rhs : Fin.foldl m (fun x1 x2 => x1 + f x2.castSucc) 0 =
                 Fin.foldl m (fun x1 x2 => x1 + (f ∘ Fin.castSucc) x2) 0 := by
      congr
    rw [← h_rhs]
    -- Now we have: init + c * (foldl of castSucc) + f(last) * c
    -- We want: init + c * (foldl of castSucc + f(last))
    rw [mul_add, add_assoc]
    congr 1
    rw [mul_comm c (f (Fin.last m)), add_comm]

/-- Convert Fin.foldl to Finset.sum via range -/
lemma foldl_eq_sum_range {α : Type*} [AddCommMonoid α] : ∀ (n' : ℕ) (f' : Fin n' → α),
    Fin.foldl n' (fun acc i => acc + f' i) 0 = ∑ i ∈ Finset.range n', if h : i < n' then f' ⟨i, h⟩ else 0 := by
  intro n' f'
  induction n' with
  | zero =>
    simp [Fin.foldl_zero, Finset.range_zero, Finset.sum_empty]
  | succ n'' ih =>
    rw [Fin.foldl_succ_last]
    rw [Finset.sum_range_succ]
    simp only [ih]
    -- We need to show that the sum equals itself plus the last term
    congr 1
    -- For the sum part, we need to show the functions are equal
    · apply Finset.sum_congr rfl
      intro i hi
      simp only [Finset.mem_range] at hi
      simp only [Fin.castSucc_mk]
      simp only [hi]
      simp only [↓reduceDIte]
      have hi' : i < n'' + 1 := by omega
      simp only [hi', ↓reduceDIte]
    · -- For the last term
      simp only [Fin.last, Nat.lt_succ_self, dif_pos]

/-- Convert Fin.foldl to a standard sum -/
lemma foldl_to_sum {α : Type*} [AddCommMonoid α] : ∀ (n' : ℕ) (f' : Fin n' → α),
    Fin.foldl n' (fun acc i => acc + f' i) 0 = ∑ i : Fin n', f' i := by
  intro n' f'
  simp only [Finset.sum_fin_eq_sum_range]
  exact foldl_eq_sum_range n' f'

/-- Summation interchange for double sums -/
lemma sum_interchange {α : Type*} [CommSemiring α] {n ops : ℕ} (f : Fin ops → Fin n → α) (g : ℕ → α) :
    Fin.foldl n (fun acc k => acc + g k.val *
      Fin.foldl ops (fun acc' j => acc' + f j k) 0) 0 =
    Fin.foldl ops (fun acc j => acc +
      Fin.foldl n (fun acc' k => acc' + f j k * g k.val) 0) 0 := by
  simp only [foldl_to_sum, Finset.mul_sum]
  -- Now: ∑ k, (∑ j, g k * f j k) = ∑ j, (∑ k, f j k * g k)
  -- Use sum_comm to swap order
  rw [Finset.sum_comm]
  -- Just need to show g k * f j k = f j k * g k
  simp only [mul_comm]

end Fin
