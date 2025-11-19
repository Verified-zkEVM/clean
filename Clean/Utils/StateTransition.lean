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
