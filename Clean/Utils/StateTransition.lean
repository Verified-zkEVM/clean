import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# State Transition with +1 Source and -1 Sink

This file formalizes a foundational result about state transition systems.

## Setup

Given:
- `S`: A finite set of states
- `T ⊆ S × S`: A set of allowed transitions
- `R`: A run, represented as a nat-multiset on `T` (for each transition `t ∈ T`,
  `R(t)` counts how many times the transition is used)

## Net Flow

For each state `x`, we can compute the net flow `R#(x)` as:
```
R#(x) = (sum of R(t) for all t = ⟨x, ·⟩) - (sum of R(t) for all t = ⟨·, x⟩)
```

This represents outflow minus inflow for state `x`.

## Main Result

**Proposition**: If `R#(s) = 1`, `R#(d) = -1`, and `R#(x) = 0` for all other states,
then there exists a cycle-free path from `s` to `d` following transitions in `R`.

## Proof Sketch

1. If `R` contains a cycle, we can remove it. The resulting `R'` is smaller and still
   satisfies the net flow conditions.
2. After removing all cycles, we have a DAG structure.
3. The states reachable from `s` form a finite DAG, which must have at least one leaf `l`.
4. Since `l` has incoming edges but no outgoing edges in `R`, we have `R#(l) < 0`.
5. The only state with negative net flow is `d`, so `l = d`.
6. Therefore, `d` is reachable from `s` via a cycle-free path.

-/

namespace Utils.StateTransition

variable {S : Type*} [DecidableEq S] [Fintype S]

/-- A transition from one state to another. -/
def Transition (S : Type*) := S × S

instance [Fintype S] : Fintype (Transition S) := instFintypeProd S S

instance [DecidableEq S] : DecidableEq (Transition S) := instDecidableEqProd

/-- A run is a function assigning a natural number to each transition,
    representing how many times that transition is used. -/
def Run (S : Type*) := Transition S → ℕ

/-- The net flow at state `x`: outflow minus inflow.
    Outflow: sum of R(x, y) for all y
    Inflow: sum of R(y, x) for all y -/
noncomputable def Run.netFlow {S : Type*} [Fintype S] [DecidableEq S] (R : Run S) (x : S) : ℤ :=
  (∑ y : S, (R (x, y) : ℤ)) - (∑ y : S, (R (y, x) : ℤ))

/-- The total number of transitions used in a run. -/
noncomputable def Run.size {S : Type*} [Fintype S] [DecidableEq S] (R : Run S) : ℕ :=
  ∑ t : Transition S, R t

/-- Check if consecutive elements in a list form valid transitions with positive count. -/
def Run.validPath (R : Run S) : List S → Prop
  | [] => True
  | [_] => True
  | x :: y :: rest => R (x, y) > 0 ∧ Run.validPath R (y :: rest)

/-- A path in the transition system is a list of states where consecutive states
    form transitions in the run. -/
def Run.hasPath (R : Run S) (path : List S) : Prop :=
  path ≠ [] ∧ R.validPath path

/-- A cycle is a non-empty path where the first and last states are the same. -/
def Run.hasCycle (R : Run S) : Prop :=
  ∃ (cycle : List S), cycle.length ≥ 2 ∧
    cycle.head? = cycle.getLast? ∧
    R.validPath cycle

/-- A run is acyclic if it contains no cycles. -/
def Run.isAcyclic (R : Run S) : Prop :=
  ¬R.hasCycle

/-- Count how many times a transition appears in a path (as consecutive elements). -/
def countTransitionInPath [DecidableEq S] (t : Transition S) (path : List S) : ℕ :=
  (path.zip path.tail).count t

/-- Remove one instance of a cycle from a run. -/
def Run.removeCycle (R : Run S) (cycle : List S) : Run S :=
  fun t => R t - countTransitionInPath t cycle

/-- A state is reachable from another via transitions in the run. -/
def Run.reachable (R : Run S) (start finish : S) : Prop :=
  ∃ (path : List S), path.head? = some start ∧ path.getLast? = some finish ∧ R.hasPath path

/-- A leaf in the run from a given state is a reachable state with no outgoing transitions. -/
def Run.isLeaf (R : Run S) (root leaf : S) : Prop :=
  R.reachable root leaf ∧ ∀ y, R (leaf, y) = 0

-- Helper lemmas

/-- Folding addition over non-negative terms preserves the accumulator's lower bound. -/
lemma foldl_add_nonneg_ge_acc {S : Type*} (R : S × S → ℕ) (leaf : S) (xs : List S) (acc : ℤ) :
    xs.foldl (fun a z => a + (R (z, leaf) : ℤ)) acc ≥ acc := by
  induction xs generalizing acc with
  | nil => simp [List.foldl]
  | cons hd tl ih =>
    simp [List.foldl]
    have : tl.foldl (fun a z => a + (R (z, leaf) : ℤ)) (acc + ↑(R (hd, leaf))) ≥ acc + ↑(R (hd, leaf)) := ih _
    omega

-- Lemmas about folds and sums

/-- foldl with accumulator is equal to foldl without plus accumulator. -/
lemma foldl_add_acc {α : Type*} (f : α → ℕ) (xs : List α) (acc : ℕ) :
    xs.foldl (fun a x => a + f x) acc = acc + xs.foldl (fun a x => a + f x) 0 := by
  induction xs generalizing acc with
  | nil => simp [List.foldl]
  | cons hd tl ih =>
    simp [List.foldl]
    rw [ih (acc + f hd), ih (f hd)]
    omega

/-- If g x ≤ f x for all x, then the fold sum of g is ≤ fold sum of f. -/
lemma foldl_sum_le {α : Type*} (f g : α → ℕ) (xs : List α)
    (h_le : ∀ x, g x ≤ f x) :
    xs.foldl (fun acc x => acc + g x) 0 ≤ xs.foldl (fun acc x => acc + f x) 0 := by
  induction xs with
  | nil => simp [List.foldl]
  | cons hd tl ih =>
    simp [List.foldl]
    rw [foldl_add_acc g tl (g hd), foldl_add_acc f tl (f hd)]
    have h_hd : g hd ≤ f hd := h_le hd
    omega

-- Lemmas about folds and sums

/-- If we decrease one element in a sum and all others are non-negative, the sum decreases. -/
lemma foldl_sum_decrease {α : Type*} [DecidableEq α] (f g : α → ℕ) (xs : List α) (a : α)
    (h_a_in : a ∈ xs) (h_a_decrease : g a < f a)
    (h_others_le : ∀ x, g x ≤ f x) :
    xs.foldl (fun acc x => acc + g x) 0 < xs.foldl (fun acc x => acc + f x) 0 := by
  induction xs with
  | nil => simp at h_a_in
  | cons hd tl ih =>
    simp [List.foldl]
    by_cases h_eq : hd = a
    · -- If hd = a, then we have the strict decrease here
      rw [h_eq]
      rw [foldl_add_acc g tl (g a), foldl_add_acc f tl (f a)]
      have h_rest_le : tl.foldl (fun acc x => acc + g x) 0 ≤ tl.foldl (fun acc x => acc + f x) 0 := by
        exact foldl_sum_le f g tl h_others_le
      omega
    · -- If hd ≠ a, then a ∈ tl, so we use IH
      have h_a_in_tl : a ∈ tl := by
        cases h_a_in with
        | head => contradiction
        | tail _ h => exact h
      rw [foldl_add_acc g tl (g hd), foldl_add_acc f tl (f hd)]
      have ih_result := ih h_a_in_tl
      have h_hd_le : g hd ≤ f hd := h_others_le hd
      omega

/-- If one element strictly decreases and others are ≤, the sum decreases -/
lemma sum_decrease {α : Type*} [Fintype α] [DecidableEq α] (f g : α → ℕ) (a : α)
    (h_a_decrease : g a < f a)
    (h_others_le : ∀ x, g x ≤ f x) :
    ∑ x : α, g x < ∑ x : α, f x := by
  have h1 : ∑ x : α, f x = f a + ∑ x ∈ Finset.univ.erase a, f x := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ a)]
    omega
  have h2 : ∑ x : α, g x = g a + ∑ x ∈ Finset.univ.erase a, g x := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ a)]
    omega
  rw [h1, h2]
  -- The sum over the rest is ≤ because each component is ≤
  -- And g a < f a gives us the strict inequality
  sorry

-- Lemmas about valid paths and transitions

/-- A valid path with at least 2 elements has at least one transition with positive count. -/
lemma validPath_has_transition {S : Type*} [DecidableEq S] (R : Run S) (path : List S)
    (h_valid : R.validPath path) (h_len : path.length ≥ 2) :
    ∃ (x y : S), (x, y) ∈ path.zip path.tail ∧ R (x, y) > 0 := by
  cases path with
  | nil => simp at h_len
  | cons hd tl =>
    cases tl with
    | nil => simp at h_len
    | cons hd2 tl2 =>
      unfold Run.validPath at h_valid
      simp at h_valid
      obtain ⟨h_pos, _⟩ := h_valid
      use hd, hd2
      constructor
      · simp [List.zip, List.tail]
      · exact h_pos

-- Lemmas about cycle removal and net flow

/-- For any list, count how many times x appears as first component in consecutive pairs. -/
def countAsFirst [DecidableEq S] (xs : List S) (x : S) : ℕ :=
  (xs.zip xs.tail).countP (fun p => p.1 = x)

/-- For any list, count how many times x appears as second component in consecutive pairs. -/
def countAsSecond [DecidableEq S] (xs : List S) (x : S) : ℕ :=
  (xs.zip xs.tail).countP (fun p => p.2 = x)

set_option linter.unusedSectionVars false in
/-- Helper: cons adds a pair that contributes to first count if head matches -/
lemma countAsFirst_cons (hd : S) (tl : List S) (x : S) :
    countAsFirst (hd :: tl) x = (if hd = x ∧ tl ≠ [] then 1 else 0) + countAsFirst tl x := by
  unfold countAsFirst
  cases tl with
  | nil =>
    -- [hd] has no pairs, tail is empty
    simp [List.zip, List.tail, List.countP]
  | cons hd2 tl2 =>
    -- [hd, hd2] ++ tl2: zip creates (hd, hd2) :: rest
    simp [List.zip, List.tail]
    rw [List.countP_cons]
    simp
    by_cases h : hd = x <;> simp [h]
    omega

set_option linter.unusedSectionVars false in
/-- Helper: cons adds a pair that contributes to second count if head of tail matches -/
lemma countAsSecond_cons (hd : S) (tl : List S) (x : S) :
    countAsSecond (hd :: tl) x = (if tl.head? = some x then 1 else 0) + countAsSecond tl x := by
  unfold countAsSecond
  cases tl with
  | nil =>
    -- [hd] has no pairs, tail is empty
    simp [List.zip, List.tail, List.countP]
  | cons hd2 tl2 =>
    -- [hd, hd2] ++ tl2: zip creates (hd, hd2) :: rest
    simp [List.zip, List.tail, List.head?]
    rw [List.countP_cons]
    simp
    by_cases h : hd2 = x <;> simp [h]
    omega

set_option linter.unusedSectionVars false in
/-- General lemma: countAsFirst + last = countAsSecond + head -/
lemma countAsFirst_add_last_eq_countAsSecond_add_head (xs : List S) (x : S) :
    countAsFirst xs x + (if xs.getLast? = some x then 1 else 0) =
    countAsSecond xs x + (if xs.head? = some x then 1 else 0) := by
  -- Induction on list structure
  induction xs with
  | nil =>
    -- Empty list
    unfold countAsFirst countAsSecond
    simp
  | cons hd tl ih =>
    -- Use helper lemmas
    rw [countAsFirst_cons, countAsSecond_cons]

    cases tl with
    | nil =>
      -- Single element [hd]: no pairs, both counts are 0
      unfold countAsFirst countAsSecond at ih ⊢
      simp
    | cons hd2 tl2 =>
      -- At least 2 elements: [hd, hd2] ++ tl2
      simp [List.head?, List.getLast?] at ih ⊢
      -- LHS = (if hd = x then 1 else 0) + countAsFirst (hd2::tl2) x + last
      -- RHS = (if hd2 = x then 1 else 0) + countAsSecond (hd2::tl2) x + 1
      -- IH: countAsFirst (hd2::tl2) x + last = countAsSecond (hd2::tl2) x + (if hd2 = x then 1 else 0)
      -- So: LHS = (if hd = x then 1 else 0) + countAsSecond (hd2::tl2) x + (if hd2 = x then 1 else 0)
      --         = (if hd2 = x then 1 else 0) + countAsSecond (hd2::tl2) x + (if hd = x then 1 else 0)
      --         = RHS ✓
      omega

set_option linter.unusedSectionVars false in
/-- In a cycle, the number of edges leaving x equals the number entering x. -/
lemma cycle_balanced_at_node (cycle : List S) (x : S)
    (h_cycle : cycle.head? = cycle.getLast?) :
    (cycle.zip cycle.tail).countP (fun p => p.1 = x) =
    (cycle.zip cycle.tail).countP (fun p => p.2 = x) := by
  -- Use the general lemma
  have h := countAsFirst_add_last_eq_countAsSecond_add_head cycle x
  unfold countAsFirst countAsSecond at h
  -- Since cycle.head? = cycle.getLast?, we have countFirst + last = countSecond + last
  -- So countFirst = countSecond
  rw [h_cycle] at h
  omega

set_option linter.unusedSectionVars false in
/-- Helper: foldl with integer accumulator starting from acc -/
lemma foldl_int_add_from_acc (f : S → ℤ) (xs : List S) (acc : ℤ) :
    xs.foldl (fun a y => a + f y) acc = acc + xs.foldl (fun a y => a + f y) 0 := by
  induction xs generalizing acc with
  | nil => simp [List.foldl]
  | cons hd tl ih =>
    simp [List.foldl]
    rw [ih (acc + f hd), ih (f hd)]
    omega

set_option linter.unusedSectionVars false in
/-- Distributing addition over foldl -/
lemma foldl_add_distrib {α : Type*} (f g : S → α) (xs : List S) [AddCommMonoid α] :
    xs.foldl (fun acc y => acc + (f y + g y)) 0 =
    xs.foldl (fun acc y => acc + f y) 0 + xs.foldl (fun acc y => acc + g y) 0 := by
  induction xs with
  | nil => simp [List.foldl]
  | cons hd tl ih =>
    simp only [List.foldl]
    sorry

set_option linter.unusedSectionVars false in
/-- Casting a nat fold to int -/
lemma foldl_nat_cast_to_int (f : S → ℕ) (xs : List S) :
    (xs.foldl (fun acc y => acc + f y) 0 : ℤ) =
    xs.foldl (fun acc y => acc + (f y : ℤ)) 0 := by
  induction xs with
  | nil => simp [List.foldl]
  | cons hd tl ih => simp only [List.foldl]

/-- Helper: foldl with accumulator adjustment -/
lemma foldl_add_const_aux {α : Type*} (xs : List α) (c acc : ℕ) :
    xs.foldl (fun a _ => a + c) acc = acc + xs.length * c := by
  induction xs generalizing acc with
  | nil => simp [List.foldl]
  | cons _ tl ih =>
    simp only [List.foldl, List.length_cons]
    rw [ih]
    rw [Nat.add_mul]
    omega

/-- Folding addition of a constant function over a list -/
lemma foldl_add_const {α : Type*} (xs : List α) (c : ℕ) :
    xs.foldl (fun acc _ => acc + c) 0 = xs.length * c := by
  rw [foldl_add_const_aux]
  simp

/-- Sum of counts of specific pairs equals count of pairs with fixed first component -/
lemma sum_count_pairs_fst (xs : List (S × S)) (a : S) :
    ∑ b : S, List.count (a, b) xs = List.countP (fun p => p.1 = a) xs := by
  -- Key: each pair (a, b') in xs contributes 1 when summing over b = b'
  sorry

/-- Sum of counts of specific pairs equals count of pairs with fixed second component -/
lemma sum_count_pairs_snd (xs : List (S × S)) (b : S) :
    ∑ a : S, List.count (a, b) xs = List.countP (fun p => p.2 = b) xs := by
  sorry

/-- Helper: convert foldl of nat subtraction to int subtraction when bounds hold -/
lemma foldl_nat_sub_to_int_sub (f g : S → ℕ) (xs : List S)
    (h_bound : ∀ y ∈ xs, g y ≤ f y) :
    xs.foldl (fun acc y => acc + (↑(f y - g y) : ℤ)) 0 =
    xs.foldl (fun acc y => acc + (f y : ℤ)) 0 - xs.foldl (fun acc y => acc + (g y : ℤ)) 0 := by
  induction xs with
  | nil => simp [List.foldl]
  | cons hd tl ih =>
    have h_hd : g hd ≤ f hd := h_bound hd (by simp)
    have h_tl : ∀ y ∈ tl, g y ≤ f y := fun y hy => h_bound y (by simp [hy])

    simp only [List.foldl]

    -- Convert nat subtraction to int subtraction for hd
    have h_cast : (↑(f hd - g hd) : ℤ) = ↑(f hd) - ↑(g hd) := Int.ofNat_sub h_hd

    rw [h_cast]
    simp only [zero_add]

    -- Use the accumulator lemma
    rw [foldl_int_add_from_acc (fun y => ↑(f y - g y)) tl (↑(f hd) - ↑(g hd))]
    rw [foldl_int_add_from_acc (fun y => (f y : ℤ)) tl (↑(f hd))]
    rw [foldl_int_add_from_acc (fun y => (g y : ℤ)) tl (↑(g hd))]

    -- Apply IH
    rw [ih h_tl]

    omega

/-- Net flow distributes over run subtraction when the subtraction is valid -/
lemma netFlow_sub (R R' : Run S) (x : S)
    (h_valid : ∀ t, R' t ≤ R t) :
    Run.netFlow (fun t => R t - R' t) x = R.netFlow x - R'.netFlow x := by
  unfold Run.netFlow
  -- Goal: (∑ y, ↑(R(x,y) - R'(x,y))) - (∑ y, ↑(R(y,x) - R'(y,x))) =
  --       (∑ y, ↑R(x,y)) - (∑ y, ↑R(y,x)) - ((∑ y, ↑R'(x,y)) - (∑ y, ↑R'(y,x)))

  -- Use sum_sub_distrib to distribute subtraction over sums
  have h_out : ∑ y : S, (↑(R (x, y) - R' (x, y)) : ℤ) =
               ∑ y : S, (↑(R (x, y)) : ℤ) - ∑ y : S, (↑(R' (x, y)) : ℤ) := by
    rw [← Finset.sum_sub_distrib]
    congr 1
    ext y
    exact Int.natCast_sub (h_valid (x, y))

  have h_in : ∑ y : S, (↑(R (y, x) - R' (y, x)) : ℤ) =
              ∑ y : S, (↑(R (y, x)) : ℤ) - ∑ y : S, (↑(R' (y, x)) : ℤ) := by
    rw [← Finset.sum_sub_distrib]
    congr 1
    ext y
    exact Int.natCast_sub (h_valid (y, x))

  rw [h_out, h_in]
  omega

/-- A cycle has zero net flow at any node -/
lemma cycle_netFlow_zero (cycle : List S) (x : S)
    (h_cycle : cycle.head? = cycle.getLast?) :
    Run.netFlow (fun t => countTransitionInPath t cycle) x = 0 := by
  unfold Run.netFlow
  -- Goal: (∑ y, count(x,y)) - (∑ y, count(y,x)) = 0
  -- This follows from cycle_balanced_at_node which says countAsFirst = countAsSecond

  -- We need to show the sums equal countAsFirst and countAsSecond
  -- These will use sum_count_pairs_fst and sum_count_pairs_snd once proven
  have h_outflow_eq : ∑ y : S, (countTransitionInPath (x, y) cycle : ℤ) =
                      (countAsFirst cycle x : ℤ) := by
    unfold countAsFirst countTransitionInPath
    -- Need: ∑ y, List.count (x, y) (cycle.zip cycle.tail) = List.countP (λ p, p.1 = x) (cycle.zip cycle.tail)
    sorry

  have h_inflow_eq : ∑ y : S, (countTransitionInPath (y, x) cycle : ℤ) =
                     (countAsSecond cycle x : ℤ) := by
    unfold countAsSecond countTransitionInPath
    -- Need: ∑ y, List.count (y, x) (cycle.zip cycle.tail) = List.countP (λ p, p.2 = x) (cycle.zip cycle.tail)
    sorry

  -- Use cycle balance: countAsFirst = countAsSecond (both count pairs in zip)
  have h_balance := cycle_balanced_at_node cycle x h_cycle

  rw [h_outflow_eq, h_inflow_eq]
  -- Now goal is: ↑(countAsFirst) - ↑(countAsSecond) = 0
  -- Unfold to get the countP forms
  unfold countAsFirst countAsSecond
  simp [h_balance]

/-- Removing a cycle preserves net flow at each state. -/
lemma netFlow_removeCycle_eq (R : Run S) (cycle : List S) (x : S)
    (h_valid : R.validPath cycle)
    (h_cycle : cycle.head? = cycle.getLast?) :
    (R.removeCycle cycle).netFlow x = R.netFlow x := by
  -- First, we need h_valid_sub: countTransitionInPath t cycle ≤ R t for all t
  have h_valid_sub : ∀ t, countTransitionInPath t cycle ≤ R t := by
    sorry

  -- Unfold removeCycle and use netFlow_sub
  have h_eq : (R.removeCycle cycle).netFlow x = Run.netFlow (fun t => R t - countTransitionInPath t cycle) x := by
    unfold Run.removeCycle
    rfl

  rw [h_eq, netFlow_sub R (fun t => countTransitionInPath t cycle) x h_valid_sub]
  rw [cycle_netFlow_zero cycle x h_cycle]
  simp

/-- Removing a cycle decreases the total size of the run. -/
lemma size_removeCycle_lt (R : Run S) (cycle : List S)
    (h_len : cycle.length ≥ 2)
    (h_valid : R.validPath cycle)
    (_h_cycle : cycle.head? = cycle.getLast?) :
    (R.removeCycle cycle).size < R.size := by
  -- Get a transition with positive count
  obtain ⟨x, y, h_in_zip, h_pos⟩ := validPath_has_transition R cycle h_valid h_len
  -- Show that this transition appears in the cycle, so countTransitionInPath > 0
  have h_count_pos : countTransitionInPath (x, y) cycle > 0 := by
    unfold countTransitionInPath
    exact List.count_pos_iff.mpr h_in_zip
  -- The size decreases because we subtract countTransitionInPath (x,y) cycle from R(x,y)
  -- Since R(x,y) > 0 and countTransitionInPath (x,y) cycle > 0, the total decreases.
  unfold Run.size Run.removeCycle
  -- We'll prove that the sum of (R t - countTransitionInPath t cycle) is less than sum of R t
  have h_decrease : (fun t => R t - countTransitionInPath t cycle) (x, y) < R (x, y) := by
    -- R(x,y) > 0 and countTransitionInPath (x,y) cycle > 0
    -- So R(x,y) - count < R(x,y) by Nat.sub_lt
    exact Nat.sub_lt h_pos h_count_pos
  have h_xy_in_univ : (x, y) ∈ (Finset.univ : Finset (Transition S)).toList := by
    simp [Finset.mem_toList]
  have h_others_le : ∀ t, (fun t => R t - countTransitionInPath t cycle) t ≤ R t := by
    intro t
    simp only
    exact Nat.sub_le (R t) (countTransitionInPath t cycle)
  -- Apply the general lemma about folds - but Run.size now uses ∑, not foldl!
  sorry

/-- If a run has a cycle, it can be removed. -/
lemma exists_smaller_run_with_same_netFlow (R : Run S) (h_cycle : R.hasCycle) :
    ∃ (R' : Run S), (∀ x, R'.netFlow x = R.netFlow x) ∧ R'.size < R.size := by
  -- Extract the cycle from the hypothesis
  obtain ⟨cycle, h_len, h_cycle_prop, h_valid⟩ := h_cycle
  -- Use R.removeCycle as the witness
  use R.removeCycle cycle
  constructor
  · -- Net flow is preserved
    intro x
    apply netFlow_removeCycle_eq
    · exact h_valid
    · exact h_cycle_prop
  · -- Size decreases
    apply size_removeCycle_lt
    · exact h_len
    · exact h_valid
    · exact h_cycle_prop

/-- A finite DAG reachable from a root has at least one leaf. -/
lemma acyclic_has_leaf (R : Run S) (root : S)
    (h_acyclic : R.isAcyclic)
    (h_has_out : ∃ y, R (root, y) > 0) :
    ∃ leaf, R.isLeaf root leaf := by
  -- Key idea: In a finite acyclic graph, if we start from a node with an outgoing edge
  -- and follow any maximal path, we must reach a leaf within at most Fintype.card S steps.
  -- This is because:
  -- 1. We can't revisit a node (would create a cycle)
  -- 2. We can't have a path longer than the number of states
  -- 3. If we're at a node with no outgoing edges, we've found a leaf

  -- This proof requires well-founded induction or classical reasoning about
  -- the existence of maximal elements in finite partially ordered sets.
  -- The standard approach would be:
  -- 1. Consider all paths starting from root
  -- 2. Among all finite acyclic paths, there exist maximal ones (by finiteness)
  -- 3. Any maximal path must end at a leaf (by maximality)

  -- For now, we admit this fundamental graph-theoretic result
  sorry

/-- A leaf with an incoming edge has negative net flow. -/
lemma leaf_has_negative_netFlow (R : Run S) (root leaf : S)
    (h_leaf : R.isLeaf root leaf)
    (h_in : ∃ y, R (y, leaf) > 0) :
    R.netFlow leaf < 0 := by
  -- Unfold the definition of isLeaf
  obtain ⟨_, h_no_out⟩ := h_leaf
  obtain ⟨y, hy⟩ := h_in
  -- Unfold netFlow definition
  unfold Run.netFlow
  -- The outflow is 0 because leaf has no outgoing transitions
  have h_outflow_zero : ∑ y : S, (R (leaf, y) : ℤ) = 0 := by
    sorry -- TODO: prove using h_no_out
  -- The inflow is positive because there exists y with R(y, leaf) > 0
  have h_inflow_pos : ∑ z : S, (R (z, leaf) : ℤ) > 0 := by
    sorry -- TODO: prove using hy and that sum includes y term
  -- Combine: 0 - (positive) < 0
  rw [h_outflow_zero]
  omega

/-- Main theorem: If the net flow is +1 at source s, -1 at sink d, and 0 elsewhere,
    then there exists a cycle-free path from s to d. -/
theorem exists_path_from_source_to_sink
    (R : Run S) (s d : S)
    (h_source : R.netFlow s = 1)
    (h_sink : R.netFlow d = -1)
    (h_others : ∀ x, x ≠ s → x ≠ d → R.netFlow x = 0) :
    ∃ (path : List S), path.head? = some s ∧ path.getLast? = some d ∧
      R.hasPath path ∧ path.Nodup := by
  -- Proof sketch:
  -- 1. If R has a cycle, remove it using exists_smaller_run_with_same_netFlow
  --    The resulting R' is smaller and has the same net flows
  -- 2. Repeat until R is acyclic (terminates by well-founded induction on R.size)
  -- 3. Since netFlow(s) = 1 > 0, s must have some outgoing edge
  -- 4. Use acyclic_has_leaf to find a leaf reachable from s
  -- 5. The leaf must have negative net flow by leaf_has_negative_netFlow
  -- 6. Since d is the only state with negative net flow, the leaf = d
  -- 7. The path from s to d is cycle-free by acyclicity
  -- 8. Extract a simple (no-duplicate) path from the reachability path
  sorry

end Utils.StateTransition
