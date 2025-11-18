import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.Basic

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
  let allStates := Finset.univ.toList
  let outflow := allStates.foldl (fun acc y => acc + (R (x, y) : ℤ)) 0
  let inflow := allStates.foldl (fun acc y => acc + (R (y, x) : ℤ)) 0
  outflow - inflow

/-- The total number of transitions used in a run. -/
noncomputable def Run.size {S : Type*} [Fintype S] [DecidableEq S] (R : Run S) : ℕ :=
  let allTransitions := (Finset.univ : Finset (Transition S)).toList
  allTransitions.foldl (fun acc t => acc + R t) 0

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

/-- Helper: cons adds a pair that contributes to first count if head matches -/
lemma countAsFirst_cons (hd : S) (tl : List S) (x : S) :
    countAsFirst (hd :: tl) x = (if hd = x ∧ tl ≠ [] then 1 else 0) + countAsFirst tl x := by
  sorry

/-- Helper: cons adds a pair that contributes to second count if head of tail matches -/
lemma countAsSecond_cons (hd : S) (tl : List S) (x : S) :
    countAsSecond (hd :: tl) x = (if tl.head? = some x then 1 else 0) + countAsSecond tl x := by
  sorry

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

/-- Removing a cycle preserves net flow at each state. -/
lemma netFlow_removeCycle_eq (R : Run S) (cycle : List S) (x : S)
    (h_cycle : cycle.head? = cycle.getLast?) :
    (R.removeCycle cycle).netFlow x = R.netFlow x := by
  -- Unfold the definitions
  unfold Run.netFlow Run.removeCycle
  simp only
  -- The net flow is outflow - inflow
  -- When we remove the cycle, both outflow and inflow decrease by the same amount
  -- because cycles are balanced (in-degree = out-degree for each node)

  -- For outflow: we subtract the count of transitions (x, y) in the cycle
  -- For inflow: we subtract the count of transitions (y, x) in the cycle
  -- These counts are equal by cycle_balanced_at_node

  -- The detailed proof requires showing that the fold sums distribute correctly
  sorry

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
  -- Simplify the goal
  simp only
  -- The key is that (x,y) is in the universe of all transitions
  have h_xy_in_univ : (x, y) ∈ (Finset.univ : Finset (Transition S)).toList := by
    simp [Finset.mem_toList]
  -- We'll prove that the sum of (R t - countTransitionInPath t cycle) is less than sum of R t
  have h_decrease : (fun t => R t - countTransitionInPath t cycle) (x, y) < R (x, y) := by
    simp only
    -- R(x,y) > 0 and countTransitionInPath (x,y) cycle > 0
    -- So R(x,y) - count < R(x,y) by Nat.sub_lt
    exact Nat.sub_lt h_pos h_count_pos
  have h_others_le : ∀ t, (fun t => R t - countTransitionInPath t cycle) t ≤ R t := by
    intro t
    simp only
    exact Nat.sub_le (R t) (countTransitionInPath t cycle)
  -- Apply the general lemma about folds
  exact foldl_sum_decrease R (fun t => R t - countTransitionInPath t cycle)
    (Finset.univ : Finset (Transition S)).toList (x, y) h_xy_in_univ h_decrease h_others_le

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
    exact h_cycle_prop
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
  simp only
  -- The outflow is 0 because leaf has no outgoing transitions
  have h_outflow_zero : (Finset.univ : Finset S).toList.foldl (fun acc y => acc + (R (leaf, y) : ℤ)) 0 = 0 := by
    induction (Finset.univ : Finset S).toList with
    | nil => rfl
    | cons hd tl ih =>
      simp [List.foldl]
      rw [h_no_out hd]
      simp [ih]
  -- The inflow is positive because there exists y with R(y, leaf) > 0
  have h_inflow_pos : (Finset.univ : Finset S).toList.foldl (fun acc z => acc + (R (z, leaf) : ℤ)) 0 > 0 := by
    -- y is in Finset.univ.toList since Finset.univ contains all elements
    have y_in_univ : y ∈ (Finset.univ : Finset S).toList := by
      simp [Finset.mem_toList]
    -- The fold sums all R(z, leaf) for z ∈ univ, and all terms are ≥ 0
    -- Since R(y, leaf) > 0, the sum is > 0
    have : (Finset.univ : Finset S).toList.foldl (fun acc z => acc + (R (z, leaf) : ℤ)) 0
           ≥ (R (y, leaf) : ℤ) := by
      -- Generalize to show foldl over a list containing y gives at least R(y, leaf)
      have h_general : ∀ (xs : List S) (acc : ℤ), y ∈ xs → acc ≥ 0 →
        xs.foldl (fun a z => a + (R (z, leaf) : ℤ)) acc ≥ acc + (R (y, leaf) : ℤ) := by
        intro xs
        induction xs with
        | nil =>
          intro acc h_mem _
          simp at h_mem
        | cons hd tl ih =>
          intro acc h_mem h_acc_nonneg
          simp [List.foldl]
          by_cases h_eq : hd = y
          · -- If hd = y, we add R(y, leaf) to acc
            rw [h_eq]
            have : tl.foldl (fun a z => a + (R (z, leaf) : ℤ)) (acc + ↑(R (y, leaf)))
                   ≥ acc + ↑(R (y, leaf)) := foldl_add_nonneg_ge_acc R leaf tl _
            omega
          · -- If hd ≠ y, then y ∈ tl
            have y_in_tl : y ∈ tl := by
              cases h_mem with
              | head => contradiction
              | tail _ h => exact h
            have h_new_acc : acc + (R (hd, leaf) : ℤ) ≥ 0 := by omega
            have ih_result := ih (acc + ↑(R (hd, leaf))) y_in_tl h_new_acc
            omega
      have h_result := h_general (Finset.univ : Finset S).toList 0 y_in_univ (by omega)
      simp at h_result
      exact h_result
    omega
  -- Combine: 0 - (positive) < 0
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
