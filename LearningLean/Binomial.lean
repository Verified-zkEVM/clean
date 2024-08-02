/--
Goals: Define binomial coefficients and prove:
- the reductions (Bin n k+1) -> (Bin n k) and (Bin n+1 k) -> (Bin n k)
- the binomial theorem
-/

def Bin : Nat → Nat → Nat := fun
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 1
  | n + 1, k + 1 => Bin n (k + 1) + Bin n k

namespace Bin

variable (n k : Nat)


theorem zero : Bin n 0 = 1 := by cases n <;> rfl

theorem recursive : Bin (n + 1) (k + 1) = Bin n (k + 1) + Bin n k := rfl


theorem greater : ∀ n k, n < k → Bin n k = 0 := fun n => by
  induction n with
  | zero =>
    intro k (hk : 0 < k)
    -- goal: `Bin 0 k = 0`
    -- write k as _ + 1 to apply Bin definition `0, _ + 1 => 0`
    let ⟨ _, (k_succ : k = _ + 1) ⟩ :=
      Nat.ne_zero_iff_zero_lt.mpr hk |> Nat.exists_eq_succ_of_ne_zero
    rw [k_succ]
    rfl

  | succ n greater_n =>
    intro k (hk : n + 1 < k)
    -- goal: `Bin (n + 1) k = 0`
    -- write k as _ + 1 to apply recursive Bin definition for `n + 1, _ + 1`
    let ⟨ km1, (k_succ : k = km1 + 1) ⟩ :=
      Nat.zero_lt_of_lt hk |> Nat.ne_zero_iff_zero_lt.mpr |> Nat.exists_eq_succ_of_ne_zero
    rw [k_succ]
    -- now simp expands the goal to `Bin n (km1 + 1) + Bin n km1 = 0`
    -- _both_ summands are 0 by the induction hypothesis
    simp [Bin]
    have hk' : n + 1 < km1 + 1 := k_succ ▸ hk
    have h : n < km1 := Nat.lt_of_succ_lt_succ hk'
    have h' : n < km1 + 1 := Nat.lt_of_succ_lt hk'
    simp [greater_n, h, h']


theorem greater1 : Bin n (n+1) = 0 := by
  simp [greater n (n+1)] -- simp knows `n < n + 1`!


theorem same : Bin n n = 1 := by
  induction n with
  | zero => rfl -- `Bin 0 0 = 1`
  | succ n same_n => simp [recursive n n, greater1 n, same_n]


theorem one : Bin n 1 = n := by
  induction n with
  | zero => rfl -- `Bin 0 1 = 0`
  | succ n one_n => simp [recursive n 0, one_n, zero]


theorem smaller1 : Bin (n + 1) n = n + 1 := by
  induction n with
  | zero => rfl -- `Bin 1 0 = 1`
  | succ n smaller1_n =>
    simp [recursive (n + 1), same (n + 1), smaller1_n]
    rw [Nat.add_comm]


/--
  This proves k_reduction but with the denominator multiplied out first so we don't have to
  deal with the division in several places.
-/
theorem k_reduction' : ∀ n k, n > k →

  (k + 1) * (Bin n (k + 1)) = (n - k) * (Bin n k)

  := fun n => by
  induction n with
  | zero =>
    intro _ (_ : 0 > _) -- impossible
    simp; contradiction

  | succ n k_reduction_n =>
    intro k
    cases k with
    -- the case k = 0 is easy, handle it separately to be able to expand the recursive definition below
    | zero => simp [one (n + 1), zero]

    -- case for k + 1
    | succ k =>
      intro (hk : n + 1 > k + 1)

      -- we have n > k, so either n = k + 1 or n > k + 1;
      -- when n = k + 1, we can't neatly use the induction hypothesis, so we handle it separately (it easily follows from `smaller1`)
      cases (Nat.le_of_lt_succ hk |> Nat.eq_or_lt_of_le : k + 1 = n ∨ k + 1 < n) with

      -- case n = k + 1
      | inl k1_eq_n =>
        have n_eq_k1 : n = k + 1 := by apply Eq.symm; assumption
        simp [n_eq_k1, same (k + 2), smaller1 (k + 1), Nat.add_sub_cancel_left]

      -- main case: n > k + 1
      | inr n_gt_k1 =>
        have n_gt_k : n > k := by apply Nat.lt_of_succ_lt; assumption

        -- goal: `(k + 2) * Bin (n + 1) (k + 2) = (n - k) * Bin (n + 1) (k + 1)`

        simp [Bin]
        -- expanding both sides gave us:
        -- `(k + 2) * (Bin n (k + 2) + Bin n (k + 1)) = (n - k) * (Bin n (k + 1) + Bin n k)`

        repeat rw [Nat.mul_add] -- expand the multiplication on both sides

        -- we can apply the induction hypothesis twice to make all 4 terms multiples of `Bin n (k + 1)`!
        have n_k2 : (k+2) * Bin n (k+2) = (n - (k + 1)) * Bin n (k+1) := k_reduction_n (k + 1) n_gt_k1
        have n_k1 : (k+1) * Bin n (k+1) = (n - k) * Bin n k := k_reduction_n k n_gt_k

        simp [n_k2, ← n_k1]

        repeat rw [← Nat.add_mul _ _ (Bin n (k+1))]; -- collect multiples on both sides

        have factors_eq : ∀ k, n > k → n - k + (k + 1) = n + 1 := fun k n_gt_k => by
          rw [← Nat.sub_add_comm (Nat.le_of_lt n_gt_k), Nat.add_comm k, ← Nat.add_assoc, Nat.add_sub_cancel]

        rw [factors_eq k n_gt_k, factors_eq (k + 1) n_gt_k1]

namespace DivisionHelpers
  variable {n m k l : Nat}

  private theorem n_div_n : n > 0 -> n/n = 1 := by
    intro n_gt_0
    have : 1 * n/n = 1 := Nat.mul_div_cancel 1 n_gt_0
    simp_all

  private theorem divide_both : n > 0 → n*m = k → m = k/n := by
    intro a_gt_0 h
    rw [← h, Nat.mul_div_cancel_left m a_gt_0]

  private theorem mul_both_right (k : Nat) : n = m → n*k = m*k := by
    intro n_eq_m
    rw [n_eq_m]
end DivisionHelpers

/--
  How to compute `(Bin n k)` from `(Bin n (k-1))`:

  `(Bin n k) = (n-k+1)/k * (Bin n (k-1))`

  Rolling that out to the right yields the explicit formula,

  `(Bin n k) = (n-k+1)/k * (n-k+2)/(k-1) * ... * n/1 = n! / (n-k)! k!`
-/
theorem k_reduction : ∀ n k, n > k →

  (Bin n (k + 1)) = (n - k) * (Bin n k) / (k + 1)

  := fun n k n_gt_k =>
    by simp [k_reduction' n k n_gt_k |> DivisionHelpers.divide_both _]


/--
`k_reduction` showed how to get the binomial coefficiant from smaller k, this one gets it from smaller n.

`(Bin n k) = n/(n-k) * (Bin (n-1) k)`
-/
theorem n_reduction : ∀ n k, n ≥ k →

  Bin (n + 1) k = (n + 1) * (Bin n k) / (n - k + 1)

  := fun n k => by
  cases k with
  | zero => simp [zero, DivisionHelpers.n_div_n]
  | succ k =>
    intro (n_ge_k1 : n ≥ k + 1)
    have n_gt_k : n > k := Nat.lt_of_succ_le n_ge_k1
    have n1_gt_k : n + 1 > k := Nat.lt_succ_of_lt n_gt_k

    simp [recursive n k]
    repeat rw [k_reduction n k n_gt_k]

    have k1_gt_0 : k + 1 > 0 := Nat.zero_lt_succ k

    rw (config := {occs := .pos [2]}) [← Nat.mul_div_cancel_left (Bin n k) k1_gt_0]

    -- multiply goal from both sides with k + 1
    apply (Nat.mul_right_cancel k1_gt_0)

    admit


end Bin
