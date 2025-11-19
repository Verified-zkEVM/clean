import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset

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

/-- Count how many times a transition appears in a path (as consecutive elements). -/
def countTransitionInPath [DecidableEq S] (t : Transition S) (path : List S) : ℕ :=
  (path.zip path.tail).count t

/-- A path is contained in a run if the count of each transition in the path
    does not exceed its capacity in the run. -/
def Run.containsPath [DecidableEq S] (R : Run S) (path : List S) : Prop :=
  ∀ t : Transition S, countTransitionInPath t path ≤ R t

/-- A cycle is a non-empty path where the first and last states are the same,
    and the cycle is contained in the run (so it can be removed). -/
def Run.hasCycle [DecidableEq S] (R : Run S) : Prop :=
  ∃ (cycle : List S), cycle.length ≥ 2 ∧
    cycle.head? = cycle.getLast? ∧
    R.containsPath cycle

/-- A run is acyclic if it contains no cycles. -/
def Run.isAcyclic [DecidableEq S] (R : Run S) : Prop :=
  ¬R.hasCycle

/-- Remove one instance of a cycle from a run. -/
def Run.removeCycle (R : Run S) (cycle : List S) : Run S :=
  fun t => R t - countTransitionInPath t cycle

/-- A state is reachable from another via transitions in the run. -/
def Run.reachable [DecidableEq S] (R : Run S) (start finish : S) : Prop :=
  ∃ (path : List S), path.head? = some start ∧ path.getLast? = some finish ∧
    path ≠ [] ∧ R.containsPath path

/-- A leaf in the run from a given state is a reachable state with no outgoing transitions. -/
def Run.isLeaf (R : Run S) (root leaf : S) : Prop :=
  R.reachable root leaf ∧ ∀ y, R (leaf, y) = 0

-- Helper lemmas for sums

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
  have h_rest : ∑ x ∈ Finset.univ.erase a, g x ≤ ∑ x ∈ Finset.univ.erase a, f x := by
    apply Finset.sum_le_sum
    intro x _
    exact h_others_le x
  omega

-- Lemmas about valid paths and transitions

/-- A path with at least 2 elements has at least one transition. -/
lemma path_has_transition {S : Type*} [DecidableEq S] (path : List S)
    (h_len : path.length ≥ 2) :
    ∃ (t : Transition S), t ∈ path.zip path.tail := by
  cases path with
  | nil => simp at h_len
  | cons hd tl =>
    cases tl with
    | nil => simp at h_len
    | cons hd2 tl2 =>
      use (hd, hd2)
      simp [List.zip, List.tail]

omit [Fintype S] in
/-- If a path is contained in a run and uses a transition, that transition has positive capacity. -/
lemma containsPath_has_positive_transition (R : Run S) (path : List S)
    (h_contains : R.containsPath path) (t : Transition S)
    (h_in : t ∈ path.zip path.tail) :
    R t > 0 := by
  have h_count_pos : countTransitionInPath t path > 0 := by
    unfold countTransitionInPath
    exact List.count_pos_iff.mpr h_in
  have h_bound := h_contains t
  omega

/-- If a path is contained in a run, dropping elements preserves containment. -/
lemma containsPath_drop (R : Run S) (path : List S) (n : ℕ)
    (h_contains : R.containsPath path) :
    R.containsPath (path.drop n) := by
  sorry

/-- Zipping takes of two lists produces a sublist of zipping the original lists. -/
lemma zip_take_sublist (l1 l2 : List S) (n m : ℕ) :
    ((l1.take n).zip (l2.take m)).Sublist (l1.zip l2) := by
  sorry

/-- If a path is contained in a run, taking elements preserves containment. -/
lemma containsPath_take (R : Run S) (path : List S) (n : ℕ)
    (h_contains : R.containsPath path) :
    R.containsPath (path.take n) := by
  unfold Run.containsPath countTransitionInPath at h_contains ⊢
  intro t
  -- (path.take n).zip (path.take n).tail is related to path.zip path.tail
  have h_tail_take : (path.take n).tail = (path.tail).take (n - 1) := by
    cases n with
    | zero => simp
    | succ n' =>
      cases path with
      | nil => simp
      | cons hd tl =>
        simp [List.take, List.tail]
  rw [h_tail_take]
  -- Use the general lemma about zip and take
  have h_sublist := zip_take_sublist path path.tail n (n - 1)
  have h_count_le : List.count t ((path.take n).zip ((path.tail).take (n - 1))) ≤
      List.count t (path.zip path.tail) := List.Sublist.count_le t h_sublist
  have h_original := h_contains t
  omega

/-- If a run is acyclic and contains a path, the path has no duplicate vertices. -/
lemma acyclic_containsPath_nodup (R : Run S) (path : List S)
    (h_acyclic : R.isAcyclic)
    (h_contains : R.containsPath path) :
    path.Nodup := by
  -- Proof by contradiction: if path has duplicates, extract a cycle
  by_contra h_dup
  -- If path is not Nodup, there exists an element that appears twice
  rw [← List.exists_duplicate_iff_not_nodup] at h_dup
  obtain ⟨x, h_duplicate⟩ := h_dup
  -- x appears at least twice in path, at distinct positions
  rw [List.duplicate_iff_exists_distinct_get] at h_duplicate
  obtain ⟨n, m, h_n_lt_m, h_x_at_n, h_x_at_m⟩ := h_duplicate
  -- Extract the subpath from index n to index m (inclusive)
  -- This forms a cycle: path[n..m] starts and ends with x
  -- Use take and drop: drop n first, then take (m - n + 1) elements
  let cycle := (path.drop n.val).take (m.val - n.val + 1)
  -- Prove this is a cycle
  have h_n_lt_len : n.val < path.length := n.isLt
  have h_m_lt_len : m.val < path.length := m.isLt
  have h_cycle_len : cycle.length ≥ 2 := by
    simp only [cycle]
    rw [List.length_take, List.length_drop]
    have h_diff : m.val - n.val ≥ 1 := by
      have : (n : ℕ) < (m : ℕ) := h_n_lt_m
      omega
    -- We're taking min(m - n + 1, path.length - n)
    -- Since m < path.length, we have m - n < path.length - n
    -- So min(m - n + 1, path.length - n) = m - n + 1
    have : m.val - n.val + 1 ≤ path.length - n.val := by omega
    simp [Nat.min_eq_left this]
    omega
  have h_cycle_starts_ends_with_x : cycle.head? = cycle.getLast? := by
    -- cycle = (path.drop n).take (m - n + 1)
    -- head? of (path.drop n) is path[n]
    -- getLast? of cycle needs careful handling with take
    have h_head : cycle.head? = some x := by
      simp only [cycle]
      rw [List.head?_take]
      have h_take_nonzero : m.val - n.val + 1 ≠ 0 := by omega
      simp only [if_neg h_take_nonzero]
      rw [List.head?_drop]
      have h_n_in_bounds : n.val < path.length := h_n_lt_len
      simp only [List.getElem?_eq_getElem h_n_in_bounds]
      congr 1
      -- path[n] is the same as path.get n
      exact h_x_at_n.symm
    have h_last : cycle.getLast? = some x := by
      simp only [cycle]
      -- cycle.length = m - n + 1, so getLast is at index (m - n)
      -- which corresponds to path[n + (m - n)] = path[m]
      have h_cycle_length : cycle.length = m.val - n.val + 1 := by
        simp only [cycle]
        rw [List.length_take, List.length_drop]
        have : m.val - n.val + 1 ≤ path.length - n.val := by omega
        simp [Nat.min_eq_left this]
      rw [List.getLast?_eq_getElem?, h_cycle_length]
      have h_idx : m.val - n.val + 1 - 1 = m.val - n.val := by omega
      rw [h_idx]
      -- Now show cycle[m - n] = path[m]
      simp only [List.getElem?_take, List.getElem?_drop]
      have h_in_bounds : m.val - n.val < m.val - n.val + 1 := by omega
      simp [h_in_bounds]
      have : n.val + (m.val - n.val) = m.val := by omega
      simp only [this]
      have h_m_in_bounds : m.val < path.length := h_m_lt_len
      simp only [List.getElem?_eq_getElem h_m_in_bounds]
      congr 1
      exact h_x_at_m.symm
    rw [h_head, h_last]
  have h_cycle_contained : R.containsPath cycle := by
    -- cycle = (path.drop n).take (m - n + 1)
    -- First apply drop, then take
    simp only [cycle]
    have h_after_drop : R.containsPath (path.drop n.val) := by
      exact containsPath_drop R path n.val h_contains
    exact containsPath_take R (path.drop n.val) (m.val - n.val + 1) h_after_drop
  -- This contradicts acyclicity
  unfold Run.isAcyclic Run.hasCycle at h_acyclic
  push_neg at h_acyclic
  apply h_acyclic cycle h_cycle_len h_cycle_starts_ends_with_x h_cycle_contained

/-- Appending an element to a non-empty path adds exactly one transition from the last element. -/
lemma countTransitionInPath_append_singleton (path : List S) (x y : S)
    (h_nonempty : path ≠ [])
    (h_last : path.getLast? = some x)
    (h_not_in : (x, y) ∉ path.zip path.tail) :
    countTransitionInPath (x, y) (path ++ [y]) = 1 := by
  sorry

/-- Appending an element doesn't add a transition that's different from (last, new). -/
lemma countTransitionInPath_append_singleton_other (path : List S) (x y : S) (t : Transition S)
    (h_nonempty : path ≠ [])
    (h_last : path.getLast? = some x)
    (h_ne : t ≠ (x, y)) :
    countTransitionInPath t (path ++ [y]) = countTransitionInPath t path := by
  sorry

/-- If a path has no duplicates, each transition appears at most once. -/
lemma nodup_transition_count_le_one (path : List S) (h_nodup : path.Nodup)
    (t : Transition S) :
    countTransitionInPath t path ≤ 1 := by
  unfold countTransitionInPath
  -- If path has Nodup, consecutive pairs are distinct
  have h_zip_nodup : (path.zip path.tail).Nodup := by
    -- If (a,b) and (c,d) are both in path.zip path.tail and (a,b) = (c,d),
    -- then a = c and b = d
    -- Since a, b are consecutive in path and c, d are consecutive,
    -- and path is Nodup, this means they're the same pair
    sorry
  -- If list is Nodup, each element appears at most once
  by_cases h_in : t ∈ path.zip path.tail
  · have : List.count t (path.zip path.tail) = 1 := by
      exact List.count_eq_one_of_mem h_zip_nodup h_in
    omega
  · have : List.count t (path.zip path.tail) = 0 := by
      exact List.count_eq_zero.mpr h_in
    omega

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

/-- Sum of counts of specific pairs equals count of pairs with fixed first component -/
lemma sum_count_pairs_fst (xs : List (S × S)) (a : S) :
    ∑ b : S, List.count (a, b) xs = List.countP (fun p => p.1 = a) xs := by
  -- Key: each pair (a, b') in xs contributes 1 when summing over b = b'
  induction xs with
  | nil => simp
  | cons p ps ih =>
    rw [List.countP_cons]
    simp only [List.count_cons]
    -- Split the sum: ∑ b, (count in ps + ite) = ∑ b, count in ps + ∑ b, ite
    rw [Finset.sum_add_distrib]
    rw [ih]
    congr 1
    -- Now show: ∑ b, (if p == (a,b) then 1 else 0) = if p.1 = a then 1 else 0
    cases p with | mk x y =>
    simp only
    by_cases h : x = a
    · subst h
      -- ∑ b, (if (a,y) == (a,b) then 1 else 0) = 1
      -- This is 1 when b = y, 0 otherwise
      simp
    · -- x ≠ a, so all terms are 0
      simp [h]

/-- Sum of counts of specific pairs equals count of pairs with fixed second component -/
lemma sum_count_pairs_snd (xs : List (S × S)) (b : S) :
    ∑ a : S, List.count (a, b) xs = List.countP (fun p => p.2 = b) xs := by
  -- Symmetric to sum_count_pairs_fst
  induction xs with
  | nil => simp
  | cons p ps ih =>
    rw [List.countP_cons]
    simp only [List.count_cons]
    rw [Finset.sum_add_distrib]
    rw [ih]
    congr 1
    cases p with | mk x y =>
    simp only
    by_cases h : y = b
    · subst h
      simp
    · simp [h]

/-- Sum of transition counts equals count of transitions with fixed first component -/
lemma sum_countTransitionInPath_fst (cycle : List S) (x : S) :
    ∑ y : S, (countTransitionInPath (x, y) cycle : ℤ) = (countAsFirst cycle x : ℤ) := by
  unfold countAsFirst countTransitionInPath Transition
  -- Goal: ∑ y, ↑(List.count (x, y) (cycle.zip cycle.tail)) = ↑(List.countP (fun p => p.1 = x) (cycle.zip cycle.tail))
  -- First convert the sum of casts to a cast of a sum
  rw [← Nat.cast_sum]
  -- Now we need to show: (∑ y, List.count (x, y) xs) = List.countP (fun p => p.1 = x) xs
  -- This is exactly sum_count_pairs_fst, we just need to handle the BEq instance
  -- Use the fact that List.count doesn't depend on the specific BEq instance for pairs with DecidableEq
  have h := sum_count_pairs_fst (cycle.zip cycle.tail) x
  convert congr_arg Nat.cast h

/-- Sum of transition counts equals count of transitions with fixed second component -/
lemma sum_countTransitionInPath_snd (cycle : List S) (x : S) :
    ∑ y : S, (countTransitionInPath (y, x) cycle : ℤ) = (countAsSecond cycle x : ℤ) := by
  unfold countAsSecond countTransitionInPath Transition
  -- Goal: ∑ y, ↑(List.count (y, x) (cycle.zip cycle.tail)) = ↑(List.countP (fun p => p.2 = x) (cycle.zip cycle.tail))
  -- First convert the sum of casts to a cast of a sum
  rw [← Nat.cast_sum]
  -- Now we need to show: (∑ y, List.count (y, x) xs) = List.countP (fun p => p.2 = x) xs
  -- This is exactly sum_count_pairs_snd, we just need to handle the BEq instance
  -- Use the fact that List.count doesn't depend on the specific BEq instance for pairs with DecidableEq
  have h := sum_count_pairs_snd (cycle.zip cycle.tail) x
  convert congr_arg Nat.cast h

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

  -- Use the new lemmas
  rw [sum_countTransitionInPath_fst, sum_countTransitionInPath_snd]

  -- Use cycle balance: countAsFirst = countAsSecond
  have h_balance := cycle_balanced_at_node cycle x h_cycle

  -- Now goal is: ↑(countAsFirst) - ↑(countAsSecond) = 0
  unfold countAsFirst countAsSecond
  rw [h_balance]
  simp

/-- Removing a cycle preserves net flow at each state. -/
lemma netFlow_removeCycle_eq (R : Run S) (cycle : List S) (x : S)
    (h_contains : R.containsPath cycle)
    (h_cycle : cycle.head? = cycle.getLast?) :
    (R.removeCycle cycle).netFlow x = R.netFlow x := by
  -- h_contains gives us: ∀ t, countTransitionInPath t cycle ≤ R t
  have h_valid_sub := h_contains

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
    (h_contains : R.containsPath cycle)
    (_h_cycle : cycle.head? = cycle.getLast?) :
    (R.removeCycle cycle).size < R.size := by
  -- Get a transition in the path
  obtain ⟨t, h_in_zip⟩ := path_has_transition cycle h_len
  -- This transition has positive capacity
  have h_pos := containsPath_has_positive_transition R cycle h_contains t h_in_zip
  let (x, y) := t
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
  -- Apply the sum_decrease lemma
  exact sum_decrease R (fun t => R t - countTransitionInPath t cycle) (x, y) h_decrease h_others_le

/-- If a run has a cycle, it can be removed. -/
lemma exists_smaller_run_with_same_netFlow (R : Run S) (h_cycle : R.hasCycle) :
    ∃ (R' : Run S), (∀ x, R'.netFlow x = R.netFlow x) ∧ R'.size < R.size := by
  -- Extract the cycle from the hypothesis
  obtain ⟨cycle, h_len, h_cycle_prop, h_contains⟩ := h_cycle
  -- Use R.removeCycle as the witness
  use R.removeCycle cycle
  constructor
  · -- Net flow is preserved
    intro x
    apply netFlow_removeCycle_eq
    · exact h_contains
    · exact h_cycle_prop
  · -- Size decreases
    apply size_removeCycle_lt
    · exact h_len
    · exact h_contains
    · exact h_cycle_prop

/-- Helper: Starting from a current node with outgoing edges, excluding visited states,
    we can find a leaf reachable from the root. Uses strong induction on unvisited state count. -/
lemma acyclic_has_leaf_aux (R : Run S) (root current : S)
    (visited : Finset S)
    (h_acyclic : R.isAcyclic)
    (h_reachable : R.reachable root current)
    (h_current_not_visited : current ∉ visited)
    (h_has_out : ∃ y, y ∉ visited ∧ R (current, y) > 0) :
    ∃ leaf, R.isLeaf root leaf := by
  -- Get a successor not in visited
  obtain ⟨y, h_y_not_visited, h_edge⟩ := h_has_out

  -- Check if y has any outgoing edges (excluding visited ∪ {current})
  by_cases h_y_has_out : ∃ z, z ∉ visited ∧ z ≠ current ∧ R (y, z) > 0
  case neg =>
    -- y has no outgoing edges to unvisited states (except possibly current)
    -- We'll show y is actually a leaf (has NO outgoing edges at all)
    use y
    constructor
    · -- Show y is reachable from root
      obtain ⟨path, h_start, h_end, h_nonempty, h_contains⟩ := h_reachable
      -- Extend the path by adding y
      use path ++ [y]
      constructor
      · simp [h_start]
      constructor
      · simp
      constructor
      · simp [h_nonempty]
      · intro t
        unfold countTransitionInPath
        -- Key: path is Nodup (from acyclicity), so (current, y) doesn't appear in path
        have h_path_nodup : path.Nodup := by
          exact acyclic_containsPath_nodup R path h_acyclic h_contains
        -- Since path ends with current and is Nodup, (current, _) appears at most once in path.zip path.tail
        -- and specifically (current, y) doesn't appear since y ∉ path
        have h_y_not_in_path : y ∉ path := by
          -- Key: y ≠ current (proven below), and if y ∈ path with path ending at current,
          -- we can extract a cycle from y back to y via current
          by_contra h_y_in_path
          -- First prove y ≠ current
          have h_y_ne_current : y ≠ current := by
            intro h_eq
            -- If y = current, then R(current, current) > 0, which creates a self-loop cycle
            rw [h_eq] at h_edge
            unfold Run.isAcyclic Run.hasCycle at h_acyclic
            push_neg at h_acyclic
            apply h_acyclic [current, current]
            · simp
            · simp
            · intro t
              unfold countTransitionInPath
              simp [List.zip, List.tail]
              by_cases h_t : t = (current, current)
              · subst h_t
                simp [List.count]
                omega
              · have : List.count t [(current, current)] = 0 := by
                  simp only [List.count_cons, List.count_nil, beq_iff_eq]
                  split
                  · rename_i h_eq
                    cases h_eq
                    exact absurd rfl h_t
                  · rfl
                omega
          -- Since y ∈ path and path.Nodup, and path.getLast? = some current with y ≠ current,
          -- we know y appears exactly once and before current
          -- Extract the tail of path starting from y
          sorry -- Need to construct the cycle: take path from y to current, then add edge current → y
        have h_current_y_not_in_path : (current, y) ∉ path.zip path.tail := by
          -- If (current, y) ∈ path.zip path.tail, then y ∈ path.tail, so y ∈ path
          intro h_in
          -- (current, y) ∈ path.zip path.tail means there's some position where
          -- path has current followed by y
          -- From membership in zip, we can extract that y ∈ path.tail
          have h_y_in_tail : y ∈ path.tail := by
            -- If (a, b) ∈ xs.zip ys, then b ∈ ys
            have : current ∈ path ∧ y ∈ path.tail := List.of_mem_zip h_in
            exact this.2
          have h_y_in_path' : y ∈ path := List.mem_of_mem_tail h_y_in_tail
          exact h_y_not_in_path h_y_in_path'
        by_cases h_t_eq : t = (current, y)
        · -- t is the new transition (current, y)
          subst h_t_eq
          have h_new_count : countTransitionInPath (current, y) (path ++ [y]) = 1 := by
            exact countTransitionInPath_append_singleton path current y h_nonempty h_end h_current_y_not_in_path
          show countTransitionInPath (current, y) (path ++ [y]) ≤ R (current, y)
          rw [h_new_count]
          omega
        · -- t is not the new transition, so count doesn't change
          have h_count_same : countTransitionInPath t (path ++ [y]) = countTransitionInPath t path := by
            exact countTransitionInPath_append_singleton_other path current y t h_nonempty h_end h_t_eq
          unfold countTransitionInPath at h_count_same
          rw [h_count_same]
          exact h_contains t
    · -- Show y has no outgoing edges
      intro z
      by_contra h_pos
      push_neg at h_y_has_out
      -- If R(y,z) > 0, then by h_y_has_out, either z ∈ visited or z = current
      have h_z_pos : R (y, z) > 0 := by omega
      have h_z_in_visited_or_current : z ∈ visited ∨ z = current := by
        by_contra h_not
        push_neg at h_not
        specialize h_y_has_out z
        have h_contra : z ∉ visited ∧ z ≠ current ∧ R (y, z) > 0 := ⟨h_not.1, h_not.2, h_z_pos⟩
        -- This contradicts h_y_has_out which says no such z exists
        have h_le := h_y_has_out h_not.1 h_not.2
        omega

      -- Derive contradiction from cycle
      cases h_z_in_visited_or_current with
      | inl h_z_in_visited =>
        -- z ∈ visited, but we're claiming y is a leaf reachable from root
        -- This is impossible because y has an outgoing edge to z
        -- Actually, this case requires showing the path creates a cycle through visited
        -- For now, this is the harder case
        sorry
      | inr h_z_eq_current =>
        -- z = current, so we have current → y → current
        -- But current ∉ visited and the neg case allows edges back to current
        -- This case needs more thought - the case split might be wrong
        sorry

  case pos =>
    -- y has an outgoing edge to some z ∉ visited ∪ {current}
    -- Recurse with visited ∪ {current}
    obtain ⟨z, h_z_not_visited, h_z_ne_current, h_y_z_edge⟩ := h_y_has_out

    -- Show y is reachable from root
    have h_y_reachable : R.reachable root y := by
      obtain ⟨path, h_start, h_end, h_nonempty, h_contains⟩ := h_reachable
      use path ++ [y]
      constructor
      · simp [h_start]
      constructor
      · simp
      constructor
      · simp [h_nonempty]
      · intro t
        -- Similar to the neg case above - use the helper lemmas
        have h_path_nodup : path.Nodup := acyclic_containsPath_nodup R path h_acyclic h_contains
        have h_y_not_in_path : y ∉ path := by
          sorry -- y not in path (same reasoning as above)
        have h_current_y_not_in_path : (current, y) ∉ path.zip path.tail := by
          intro h_in
          have h_y_in_tail : y ∈ path.tail := (List.of_mem_zip h_in).2
          have h_y_in_path' : y ∈ path := List.mem_of_mem_tail h_y_in_tail
          exact h_y_not_in_path h_y_in_path'
        by_cases h_t_eq : t = (current, y)
        · subst h_t_eq
          have h_new_count : countTransitionInPath (current, y) (path ++ [y]) = 1 :=
            countTransitionInPath_append_singleton path current y h_nonempty h_end h_current_y_not_in_path
          rw [h_new_count]
          omega
        · have h_count_same : countTransitionInPath t (path ++ [y]) = countTransitionInPath t path :=
            countTransitionInPath_append_singleton_other path current y t h_nonempty h_end h_t_eq
          rw [h_count_same]
          exact h_contains t

    -- Recurse with visited ∪ {current}
    let new_visited := insert current visited

    have h_y_ne_current : y ≠ current := by
      -- If y = current, then R(current, current) > 0, forming a self-loop cycle
      by_contra h_y_eq_current
      -- Construct a cycle [current, current]
      unfold Run.isAcyclic Run.hasCycle at h_acyclic
      push_neg at h_acyclic
      specialize h_acyclic [current, current]
      simp at h_acyclic
      apply h_acyclic
      intro t
      unfold countTransitionInPath
      simp
      by_cases h_t_eq : t = (current, current)
      · subst h_t_eq h_y_eq_current
        simp
        omega
      · have h_count_zero : List.count t [(current, current)] = 0 := by
          simp [List.count_eq_zero]
          exact h_t_eq
        omega

    have h_y_not_in_new_visited' : y ∉ new_visited := by
      simp [new_visited, h_y_ne_current, h_y_not_visited]

    have h_new_has_out' : ∃ w, w ∉ new_visited ∧ R (y, w) > 0 := by
      use z
      simp [new_visited]
      constructor
      · constructor
        · exact h_z_ne_current
        · exact h_z_not_visited
      · exact h_y_z_edge

    exact acyclic_has_leaf_aux R root y new_visited
      h_acyclic h_y_reachable h_y_not_in_new_visited' h_new_has_out'
termination_by Fintype.card S - visited.card
decreasing_by
  simp_wf
  have h_card_increase : (insert current visited).card = visited.card + 1 := by
    apply Finset.card_insert_of_notMem
    exact h_current_not_visited
  simp [h_card_increase]
  have h_visited_subset : visited ⊂ Finset.univ := by
    rw [Finset.ssubset_univ_iff]
    intro h_eq_univ
    rw [h_eq_univ] at h_current_not_visited
    exact h_current_not_visited (Finset.mem_univ current)
  have h_card_bound : visited.card < Fintype.card S := by
    rw [← Finset.card_univ]
    exact Finset.card_lt_card h_visited_subset
  omega

/-- A finite DAG reachable from a root has at least one leaf. -/
lemma acyclic_has_leaf (R : Run S) (root : S)
    (h_acyclic : R.isAcyclic)
    (h_has_out : ∃ y, R (root, y) > 0) :
    ∃ leaf, R.isLeaf root leaf := by
  -- Start with empty visited set and root as current
  -- Root is reachable from itself via empty path
  have h_root_reachable : R.reachable root root := by
    use [root]
    constructor
    · simp
    constructor
    · simp
    constructor
    · simp
    · intro t
      simp [countTransitionInPath]

  -- Apply the auxiliary lemma
  obtain ⟨y, h_pos⟩ := h_has_out
  apply acyclic_has_leaf_aux R root root ∅ h_acyclic h_root_reachable
  · simp
  · use y
    simp [h_pos]

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
    simp only [h_no_out]
    simp
  -- The inflow is positive because there exists y with R(y, leaf) > 0
  have h_inflow_pos : ∑ z : S, (R (z, leaf) : ℤ) > 0 := by
    -- The sum includes the term for z = y, which is positive
    have h_y_in_sum : (R (y, leaf) : ℤ) ≤ ∑ z : S, (R (z, leaf) : ℤ) := by
      calc (R (y, leaf) : ℤ)
        = ∑ z ∈ ({y} : Finset S), (R (z, leaf) : ℤ) := by simp
      _ ≤ ∑ z : S, (R (z, leaf) : ℤ) := by
          apply Finset.sum_le_univ_sum_of_nonneg
          intro x
          omega
    omega
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
      path ≠ [] ∧ R.containsPath path ∧ path.Nodup := by
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
