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

This file formalizes a result about state transition systems that's useful for Cairo-like
construction where a multiset of states represent an execution.

The initial state will be added once, the final state will be removed once. Otherwise,
for each step of the execution, the source is removed and the destination is added. All these
need to balance out.

The tricky aspect is how to deal with cycles like a snake eating its own tail. The idea is
that we can remove all the cycles and then find a path from the initial state to the final
state.

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

-- Helper lemmas for sums and finsets

/-- If an element is not in a finset, the finset is a strict subset of univ. -/
lemma finset_ssubset_univ_of_not_mem {α : Type*} [Fintype α] (s : Finset α) (x : α)
    (h : x ∉ s) :
    s ⊂ Finset.univ := by
  rw [Finset.ssubset_univ_iff]
  intro h_eq_univ
  have : x ∈ Finset.univ := Finset.mem_univ x
  rw [← h_eq_univ] at this
  exact h this

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

omit [DecidableEq S] [Fintype S] in
/-- Zipping drops of consecutive indices produces a sublist of zipping a list with its tail. -/
lemma zip_drop_sublist (l : List S) (n : ℕ) :
    ((l.drop n).zip (l.drop (n + 1))).Sublist (l.zip l.tail) := by
  induction n generalizing l with
  | zero =>
    simp [List.drop, List.tail]
  | succ n' ih =>
    cases l with
    | nil => simp
    | cons h t =>
      simp only [List.drop_succ_cons, List.tail_cons]
      have h_sub := ih t
      refine List.Sublist.trans h_sub ?_
      cases t with
      | nil => simp
      | cons t0 ts =>
        rw [List.tail_cons]
        simp [List.zip_cons_cons]

omit [Fintype S] in
/-- If a path is contained in a run, dropping elements preserves containment. -/
lemma containsPath_drop (R : Run S) (path : List S) (n : ℕ)
    (h_contains : R.containsPath path) :
    R.containsPath (path.drop n) := by
  unfold Run.containsPath countTransitionInPath at h_contains ⊢
  intro t
  have h_tail_drop : (path.drop n).tail = path.drop (n + 1) := List.tail_drop
  rw [h_tail_drop]
  have h_sublist := zip_drop_sublist path n
  have h_count_le : List.count t ((path.drop n).zip (path.drop (n + 1))) ≤
      List.count t (path.zip path.tail) := List.Sublist.count_le t h_sublist
  have h_original := h_contains t
  omega

omit [DecidableEq S] [Fintype S] in
/-- Zipping takes of two lists produces a sublist of zipping the original lists. -/
lemma zip_take_sublist (l1 l2 : List S) (n m : ℕ) :
    ((l1.take n).zip (l2.take m)).Sublist (l1.zip l2) := by
  cases n with
  | zero => simp
  | succ n' =>
    cases m with
    | zero => simp
    | succ m' =>
      cases l1 with
      | nil => simp
      | cons h1 t1 =>
        cases l2 with
        | nil => simp
        | cons h2 t2 =>
          simp only [List.take_succ_cons, List.zip_cons_cons]
          exact List.Sublist.cons₂ (h1, h2) (zip_take_sublist t1 t2 n' m')

omit [DecidableEq S] [Fintype S] in
/-- The tail of a take is the take of the tail (with adjusted count). -/
lemma tail_take {α : Type*} (l : List α) (n : ℕ) :
    (l.take n).tail = (l.tail).take (n - 1) := by
  cases n with
  | zero => simp
  | succ n' =>
    cases l with
    | nil => simp
    | cons hd tl =>
      simp [List.take, List.tail]

omit [Fintype S] in
/-- If a path is contained in a run, taking elements preserves containment. -/
lemma containsPath_take (R : Run S) (path : List S) (n : ℕ)
    (h_contains : R.containsPath path) :
    R.containsPath (path.take n) := by
  unfold Run.containsPath countTransitionInPath at h_contains ⊢
  intro t
  rw [tail_take]
  -- Use the general lemma about zip and take
  have h_sublist := zip_take_sublist path path.tail n (n - 1)
  have h_count_le : List.count t ((path.take n).zip ((path.tail).take (n - 1))) ≤
      List.count t (path.zip path.tail) := List.Sublist.count_le t h_sublist
  have h_original := h_contains t
  omega

omit [DecidableEq S] [Fintype S] in
/-- The sublist from index n to m (where n < m < path.length) has length at least 2. -/
lemma drop_take_length_ge_two {α : Type*} (path : List α) (n m : Fin path.length)
    (h_n_lt_m : n < m) :
    ((path.drop n.val).take (m.val - n.val + 1)).length ≥ 2 := by
  rw [List.length_take, List.length_drop]
  have h_diff : m.val - n.val ≥ 1 := by
    have : (n : ℕ) < (m : ℕ) := h_n_lt_m
    omega
  -- We're taking min(m - n + 1, path.length - n)
  -- Since m < path.length, we have m - n < path.length - n
  -- So min(m - n + 1, path.length - n) = m - n + 1
  have : m.val - n.val + 1 ≤ path.length - n.val := by omega
  simp only [Nat.min_eq_left this, ge_iff_le, Nat.reduceLeDiff]
  omega

omit [DecidableEq S] [Fintype S] in
/-- The last element of (path.drop n).take k is path[n + k - 1] when n + k - 1 < path.length. -/
lemma getLast_drop_take {α : Type*} (path : List α) (n k : ℕ)
    (h_n_lt : n < path.length)
    (h_bound : n + k ≤ path.length)
    (h_k_pos : k > 0) :
    ((path.drop n).take k).getLast? = path[n + k - 1]? := by
  have h_cycle_length : ((path.drop n).take k).length = k := by
    rw [List.length_take, List.length_drop]
    have : k ≤ path.length - n := by omega
    simp [Nat.min_eq_left this]
  rw [List.getLast?_eq_getElem?, h_cycle_length]
  have h_idx : k - 1 < k := by omega
  simp only [h_idx, ↓reduceIte, List.getElem?_take, List.getElem?_drop]
  have : n + (k - 1) = n + k - 1 := by omega
  rw [this]

omit [DecidableEq S] [Fintype S] in
/-- If path[n] = path[m] = x, then the sublist from n to m forms a cycle starting and ending with x. -/
lemma drop_take_cycle_same_endpoints (path : List S) (x : S) (n m : Fin path.length)
    (h_n_lt_m : n < m)
    (h_x_at_n : path[n] = x)
    (h_x_at_m : path[m] = x) :
    ((path.drop n.val).take (m.val - n.val + 1)).head? =
    ((path.drop n.val).take (m.val - n.val + 1)).getLast? := by
  have h_n_lt_len : n.val < path.length := n.isLt
  have h_m_lt_len : m.val < path.length := m.isLt
  have h_head : ((path.drop n.val).take (m.val - n.val + 1)).head? = some x := by
    rw [List.head?_take]
    have h_take_nonzero : m.val - n.val + 1 ≠ 0 := by omega
    simp only [if_neg h_take_nonzero]
    rw [List.head?_drop]
    have h_n_in_bounds : n.val < path.length := h_n_lt_len
    aesop
  have h_last : ((path.drop n.val).take (m.val - n.val + 1)).getLast? = some x := by
    rw [getLast_drop_take path n.val (m.val - n.val + 1) h_n_lt_len (by omega) (by omega)]
    have : n.val + (m.val - n.val + 1) - 1 = m.val := by omega
    simp only [this]
    aesop
  rw [h_head, h_last]

omit [Fintype S] in
/-- If a run contains a path, then any subpath obtained by dropping and taking is also contained. -/
lemma containsPath_drop_take (R : Run S) (path : List S) (n m : ℕ)
    (h_contains : R.containsPath path) :
    R.containsPath ((path.drop n).take m) := by
  have h_after_drop : R.containsPath (path.drop n) :=
    containsPath_drop R path n h_contains
  exact containsPath_take R (path.drop n) m h_after_drop

omit [Fintype S] in
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
  have h_cycle_len := drop_take_length_ge_two path n m h_n_lt_m
  have h_cycle_starts_ends_with_x : cycle.head? = cycle.getLast? :=
    drop_take_cycle_same_endpoints path x n m h_n_lt_m h_x_at_n.symm h_x_at_m.symm
  have h_cycle_contained : R.containsPath cycle :=
    containsPath_drop_take R path n.val (m.val - n.val + 1) h_contains
  -- This contradicts acyclicity
  unfold Run.isAcyclic Run.hasCycle at h_acyclic
  push_neg at h_acyclic
  apply h_acyclic cycle h_cycle_len h_cycle_starts_ends_with_x h_cycle_contained

omit [Fintype S] in
/-- Appending an element to a non-empty path adds exactly one transition from the last element. -/
lemma countTransitionInPath_append_singleton (path : List S) (x y : S)
    (h_nonempty : path ≠ [])
    (h_last : path.getLast? = some x)
    (h_not_in : (x, y) ∉ path.zip path.tail) :
    countTransitionInPath (x, y) (path ++ [y]) = 1 := by
  unfold countTransitionInPath
  obtain ⟨h, t', rfl⟩ := List.exists_cons_of_ne_nil h_nonempty
  rw [List.cons_append, List.tail_cons]
  induction t' generalizing h with
  | nil =>
    simp
    have : x = h := by simpa using h_last.symm
    simp [this]
  | cons h2 t2 ih =>
    simp only [List.cons_append, List.zip_cons_cons, List.count_cons, beq_iff_eq]
    by_cases h_eq : (h, h2) = (x, y)
    · aesop
    · simp [h_eq]
      -- Now apply IH for h2 :: t2
      apply ih
      · simp
      · rw [← List.getLast?_cons_cons]; exact h_last
      · rw [List.tail_cons, List.zip_cons_cons] at h_not_in
        aesop

omit [Fintype S] in
/-- Appending an element doesn't add a transition that's different from (last, new). -/
lemma countTransitionInPath_append_singleton_other (path : List S) (x y : S) (t : Transition S)
    (h_nonempty : path ≠ [])
    (h_last : path.getLast? = some x)
    (h_ne : t ≠ (x, y)) :
    countTransitionInPath t (path ++ [y]) = countTransitionInPath t path := by
  unfold countTransitionInPath
  obtain ⟨h, t', rfl⟩ := List.exists_cons_of_ne_nil h_nonempty
  rw [List.cons_append, List.tail_cons]
  induction t' generalizing h with
  | nil =>
    simp only [List.count, List.nil_append, List.zip_cons_cons, List.zip_nil_right,
      List.countP_singleton, beq_iff_eq, List.tail_cons, List.countP_nil, ite_eq_right_iff,
      one_ne_zero, imp_false]
    intro h_eq; subst h_eq; simp at h_last; subst h_last; exact h_ne rfl
  | cons h2 t2 ih =>
    rw [List.tail_cons]
    simp only [List.cons_append, List.zip_cons_cons, List.count_cons, beq_iff_eq,
      Nat.add_right_cancel_iff]
    -- Now we need to apply IH for h2 :: t2
    apply ih
    · simp
    · rw [← List.getLast?_cons_cons]; exact h_last

/-- If a pair is in a zip, its first component is in the first list. -/
lemma mem_of_mem_zip_fst {α β : Type*} (l1 : List α) (l2 : List β) (a : α) (b : β) :
    (a, b) ∈ l1.zip l2 → a ∈ l1 := by
  intro h_mem
  induction l1 generalizing l2 with
  | nil => simp at h_mem
  | cons h1 t1 ih =>
    cases l2 with
    | nil => simp at h_mem
    | cons h2 t2 =>
      simp only [List.zip_cons_cons, List.mem_cons, Prod.mk.injEq] at h_mem
      cases h_mem with
      | inl h_eq =>
        have : a = h1 := h_eq.1
        simp [this]
      | inr h_rest =>
        have : a ∈ t1 := ih t2 h_rest
        exact List.mem_cons_of_mem h1 this

omit [DecidableEq S] [Fintype S] in
/-- If a list has no duplicates, its zip with tail also has no duplicates. -/
lemma nodup_zip_tail (path : List S) (h_nodup : path.Nodup) :
    (path.zip path.tail).Nodup := by
  induction path with
  | nil => simp
  | cons h t ih =>
    cases t with
    | nil => simp
    | cons h2 t2 =>
      rw [List.tail_cons]
      simp only [List.zip_cons_cons, List.nodup_cons]
      have ⟨h_not_in, h_nodup_tail⟩ := List.nodup_cons.mp h_nodup
      constructor
      · -- Prove (h, h2) ∉ (h2 :: t2).zip t2
        intro h_contra
        -- If (h, h2) ∈ (h2 :: t2).zip t2, then h must be in h2 :: t2
        -- But we know h ∉ h2 :: t2, contradiction
        cases t2 with
        | nil =>
          simp [List.zip] at h_contra
        | cons h3 t3 =>
          simp only [List.zip_cons_cons, List.mem_cons, Prod.mk.injEq] at h_contra
          cases h_contra with
          | inl h_eq =>
            -- (h, h2) = (h2, h3), so h = h2
            have : h = h2 := h_eq.1
            subst this
            -- Now h_not_in says h2 ∉ h2 :: t3, but h2 is the head
            simp at h_not_in
          | inr h_rest =>
            -- (h, h2) ∈ (h3 :: t3).zip t3
            -- This means h ∈ h3 :: t3, so h ∈ h2 :: h3 :: t3
            have h_in_t3 : h ∈ h3 :: t3 := mem_of_mem_zip_fst (h3 :: t3) t3 h h2 h_rest
            have : h ∈ h2 :: h3 :: t3 := List.mem_cons_of_mem h2 h_in_t3
            contradiction
      · -- Prove ((h2 :: t2).zip t2).Nodup
        exact ih h_nodup_tail

omit [Fintype S] in
/-- If a path has no duplicates, each transition appears at most once. -/
lemma nodup_transition_count_le_one (path : List S) (h_nodup : path.Nodup)
    (t : Transition S) :
    countTransitionInPath t path ≤ 1 := by
  unfold countTransitionInPath
  have h_zip_nodup := nodup_zip_tail path h_nodup
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
    simp only [List.zip, List.tail, List.zipWith_cons_cons, ne_eq, reduceCtorEq, not_false_eq_true,
      and_true]
    rw [List.countP_cons]
    simp
    by_cases h : hd = x <;> simp only [h, ↓reduceIte, add_zero, zero_add]
    omega

set_option linter.unusedSectionVars false in
/-- Helper: cons adds a pair that contributes to second count if head of tail matches -/
lemma countAsSecond_cons (hd : S) (tl : List S) (x : S) :
    countAsSecond (hd :: tl) x = (if tl.head? = some x then 1 else 0) + countAsSecond tl x := by
  unfold countAsSecond
  cases tl with
  | nil => aesop
  | cons hd2 tl2 =>
    -- [hd, hd2] ++ tl2: zip creates (hd, hd2) :: rest
    simp only [List.zip, List.tail, List.zipWith_cons_cons, List.head?, Option.some.injEq]
    rw [List.countP_cons]
    simp only [decide_eq_true_eq]
    by_cases h : hd2 = x <;> simp only [h, ↓reduceIte, add_zero, zero_add]
    omega

set_option linter.unusedSectionVars false in
/-- General lemma: countAsFirst + last = countAsSecond + head -/
lemma countAsFirst_add_last_eq_countAsSecond_add_head (xs : List S) (x : S) :
    countAsFirst xs x + (if xs.getLast? = some x then 1 else 0) =
    countAsSecond xs x + (if xs.head? = some x then 1 else 0) := by
  -- Induction on list structure
  induction xs with
  | nil => aesop
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
      simp only [List.getLast?, Option.some.injEq, List.head?, ne_eq, reduceCtorEq,
        not_false_eq_true, and_true,
        List.getLast_cons] at ih ⊢
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
  aesop

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
    by_cases h : x = a <;> aesop

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
    · aesop
    · aesop

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
               ∑ y : S, (↑(R (x, y)) : ℤ) - ∑ y : S, (↑(R' (x, y)) : ℤ) := by aesop

  have h_in : ∑ y : S, (↑(R (y, x) - R' (y, x)) : ℤ) =
              ∑ y : S, (↑(R (y, x)) : ℤ) - ∑ y : S, (↑(R' (y, x)) : ℤ) := by aesop
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
  aesop

/-- Removing a cycle preserves net flow at each state. -/
lemma netFlow_removeCycle_eq (R : Run S) (cycle : List S) (x : S)
    (h_contains : R.containsPath cycle)
    (h_cycle : cycle.head? = cycle.getLast?) :
    (R.removeCycle cycle).netFlow x = R.netFlow x := by

  -- Unfold removeCycle and use netFlow_sub
  have h_eq : (R.removeCycle cycle).netFlow x = Run.netFlow (fun t => R t - countTransitionInPath t cycle) x := by aesop

  rw [h_eq, netFlow_sub R (fun t => countTransitionInPath t cycle) x h_contains]
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

omit [Fintype S] in
/-- Removing a cycle gives a smaller or equal run at each transition. -/
lemma removeCycle_le (R : Run S) (cycle : List S) (t : Transition S) :
    (R.removeCycle cycle) t ≤ R t := by
  unfold Run.removeCycle
  aesop

/-- If a run has a cycle, it can be removed. -/
lemma exists_smaller_run_with_same_netFlow (R : Run S) (h_cycle : R.hasCycle) :
    ∃ (R' : Run S), (∀ x, R'.netFlow x = R.netFlow x) ∧ R'.size < R.size ∧ (∀ t, R' t ≤ R t) := by
  -- Extract the cycle from the hypothesis
  obtain ⟨cycle, h_len, h_cycle_prop, h_contains⟩ := h_cycle
  -- Use R.removeCycle as the witness
  use R.removeCycle cycle
  constructor
  · -- Net flow is preserved
    intro x
    apply netFlow_removeCycle_eq <;> aesop
  constructor
  · -- Size decreases
    apply size_removeCycle_lt <;> aesop
  · -- Each transition capacity is ≤
    intro t
    exact removeCycle_le R cycle t

omit [Fintype S] in
/-- If a run has a self-loop, it contradicts acyclicity. -/
lemma acyclic_no_self_loop (R : Run S) (s : S) (h_acyclic : R.isAcyclic) (h_edge : R (s, s) > 0) : False := by
  unfold Run.isAcyclic Run.hasCycle at h_acyclic
  push_neg at h_acyclic
  apply h_acyclic [s, s]
  · simp
  · simp
  · intro t
    unfold countTransitionInPath
    simp only [List.zip, List.tail, List.zipWith_cons_cons, List.zipWith_nil_right]
    by_cases h_t : t = (s, s)
    · subst h_t
      simp only [List.count, BEq.rfl, List.countP_cons_of_pos, List.countP_nil, zero_add]
      omega
    · have : List.count t [(s, s)] = 0 := by
        simp only [List.count_cons, List.count_nil, beq_iff_eq]
        aesop
      omega

omit [Fintype S] in
/-- If a run has a 2-cycle between distinct vertices, it contradicts acyclicity. -/
lemma acyclic_no_two_cycle (R : Run S) (a b : S)
    (h_acyclic : R.isAcyclic) (h_ne : a ≠ b)
    (h_edge1 : R (a, b) > 0) (h_edge2 : R (b, a) > 0) : False := by
  unfold Run.isAcyclic Run.hasCycle at h_acyclic
  push_neg at h_acyclic
  apply h_acyclic [a, b, a]
  · simp
  · simp
  · intro t
    unfold countTransitionInPath
    simp only [List.zip, List.tail, List.zipWith_cons_cons, List.zipWith_nil_right]
    by_cases h1 : t = (a, b)
    · subst h1
      simp only [List.count, BEq.rfl, List.countP_cons_of_pos, List.countP_singleton, beq_iff_eq]
      have : ¬(b, a) = (a, b) := by
        intro h_eq
        have := Prod.mk_inj.mp h_eq
        exact h_ne this.1.symm
      simp only [this, ↓reduceIte, zero_add, ge_iff_le]
      omega
    · by_cases h2 : t = (b, a)
      · subst h2
        simp only [List.count]
        have : ¬(a, b) = (b, a) := by
          intro h_eq
          have := Prod.mk_inj.mp h_eq
          exact h_ne this.1
        simp only [beq_iff_eq, this, not_false_eq_true, List.countP_cons_of_neg, BEq.rfl,
          List.countP_cons_of_pos, List.countP_nil, zero_add, ge_iff_le]
        omega
      · have : List.count t [(a, b), (b, a)] = 0 := by
          simp only [List.count, List.countP_eq_zero, List.mem_cons, List.not_mem_nil, or_false,
            beq_iff_eq, forall_eq_or_imp, forall_eq]
          constructor
          · intro h_eq; cases h_eq; exact h1 rfl
          · intro h_eq; cases h_eq; exact h2 rfl
        rw [this]
        omega

omit [DecidableEq S] [Fintype S] in
/-- If getLast? of a non-empty list is some x, then x is in the list. -/
lemma getLast_mem {α : Type*} (l : List α) (x : α) (h_last : l.getLast? = some x) :
    x ∈ l := by
  have h_ne : l ≠ [] := by
    intro h_eq
    simp [h_eq] at h_last
  rw [List.getLast?_eq_getLast h_ne] at h_last
  cases h_last
  exact List.getLast_mem h_ne

/-- The last element of a nodup list cannot appear as the first component of a pair in zip with tail. -/
lemma last_not_in_zip_tail {α : Type*} [DecidableEq α] (l : List α) (x : α)
    (h_nodup : l.Nodup)
    (h_last : l.getLast? = some x) :
    ∀ y : α, (x, y) ∉ l.zip l.tail := by
  intro y h_in
  -- If (x, y) ∈ l.zip l.tail, then x appears at position i where i < length - 1
  -- But x is the last element (at position length - 1)
  -- Since l.Nodup, x appears only once, so i = length - 1, contradiction
  induction l with
  | nil =>
    simp at h_last
  | cons head tail ih =>
    cases tail with
    | nil =>
      simp at h_in
    | cons head2 tail2 =>
      simp only [List.getLast?_cons_cons] at h_last
      simp only [List.tail_cons, List.zip_cons_cons, List.mem_cons, Prod.mk.injEq] at h_in
      -- l.Nodup means head ≠ head2, head ∉ tail2, and (head2 :: tail2).Nodup
      have h_nodup_tail := List.nodup_cons.mp h_nodup
      cases h_in with
      | inl h_eq =>
        -- (x, y) = (head, head2), so x = head
        have h_x_head : x = head := h_eq.1
        subst h_x_head
        -- But getLast? (head2 :: tail2) = some x (which is head)
        -- This means x ∈ head2 :: tail2
        have h_x_in_tail := getLast_mem (head2 :: tail2) x h_last
        grind
      | inr h_in_rest => grind

omit [DecidableEq S] [Fintype S] in
/-- Dropping from a valid index i < path.length produces a non-empty list. -/
lemma drop_of_lt_length_nonempty {α : Type*} (path : List α) (i : ℕ)
    (h_i_lt : i < path.length) :
    path.drop i ≠ [] := by
  intro h_empty
  have : path.drop i = [] → i ≥ path.length := by
    have : (path.drop i).length > 0 := by
      rw [List.length_drop]
      omega
    intro h
    rw [h] at this
    simp at this
  have : i ≥ path.length := this h_empty
  omega

omit [Fintype S] in
/-- If a run contains an acyclic path and has an edge from the end back into the path,
    then the run has a cycle. -/
lemma path_with_back_edge_creates_cycle (R : Run S) (path : List S) (current y : S)
    (h_acyclic : R.isAcyclic)
    (h_end : path.getLast? = some current)
    (h_contains : R.containsPath path)
    (h_y_in_path : y ∈ path)
    (h_edge : R (current, y) > 0) :
    R.hasCycle := by
  -- Find y's position in path
  rw [List.mem_iff_getElem] at h_y_in_path
  obtain ⟨i, h_i_lt, h_y_eq⟩ := h_y_in_path
  let suffix := path.drop i
  have h_suffix_nonempty : suffix ≠ [] := drop_of_lt_length_nonempty path i h_i_lt
  have h_suffix_head : suffix.head? = some y := by aesop
  have h_suffix_last : suffix.getLast? = some current := by grind
  let cycle := suffix ++ [y]
  have h_cycle_head : cycle.head? = some y := by grind
  have h_cycle_last : cycle.getLast? = some y := by grind
  have h_cycle_len : cycle.length ≥ 2 := by grind
  use cycle
  constructor
  · exact h_cycle_len
  constructor
  · rw [h_cycle_head, h_cycle_last]
  · unfold cycle
    have h_suffix_contains : R.containsPath suffix := by
      unfold suffix
      exact containsPath_drop R path i h_contains
    intro t
    unfold countTransitionInPath at h_suffix_contains ⊢
    by_cases h_t_eq : t = (current, y)
    · subst h_t_eq
      have h_path_nodup := acyclic_containsPath_nodup R path h_acyclic h_contains
      have h_suffix_nodup : suffix.Nodup := by grind
      have h_not_in : (current, y) ∉ suffix.zip suffix.tail :=
        last_not_in_zip_tail suffix current h_suffix_nodup h_suffix_last y
      have h_count_one := countTransitionInPath_append_singleton suffix current y h_suffix_nonempty h_suffix_last h_not_in
      unfold countTransitionInPath at h_count_one
      aesop
    · have h_count_same := countTransitionInPath_append_singleton_other suffix current y t h_suffix_nonempty h_suffix_last h_t_eq
      unfold countTransitionInPath at h_count_same
      rw [h_count_same]
      exact h_suffix_contains t

omit [Fintype S] in
/-- If there's an edge from current to y, and y is in the path from root to current,
    then we can construct a cycle, contradicting acyclicity. -/
lemma acyclic_edge_not_in_path (R : Run S) (path : List S) (current y : S)
    (h_acyclic : R.isAcyclic)
    (h_end : path.getLast? = some current)
    (h_contains : R.containsPath path)
    (h_edge : R (current, y) > 0)
    (h_y_in_path : y ∈ path) :
    False := by
  -- Use helper lemma to show R has a cycle, contradicting acyclicity
  have h_hasCycle : R.hasCycle :=
    path_with_back_edge_creates_cycle R path current y h_acyclic h_end h_contains h_y_in_path h_edge
  aesop

omit [DecidableEq S] [Fintype S] in
/-- If y is not in a path, then (x, y) is not in the path's zip with its tail. -/
lemma not_mem_implies_transition_not_in_zip_tail {α : Type*} (path : List α) (x y : α)
    (h_y_not_in : y ∉ path) :
    (x, y) ∉ path.zip path.tail := by
  intro h_in
  have h_y_in_tail : y ∈ path.tail := (List.of_mem_zip h_in).2
  have h_y_in_path : y ∈ path := List.mem_of_mem_tail h_y_in_tail
  exact h_y_not_in h_y_in_path

omit [Fintype S] in
/-- Extending a path that satisfies containsPath preserves the property when there's an edge. -/
lemma containsPath_append_singleton (R : Run S) (path : List S) (x y : S)
    (h_nonempty : path ≠ [])
    (h_last : path.getLast? = some x)
    (h_contains : R.containsPath path)
    (h_y_not_in_path : y ∉ path)
    (h_edge : R (x, y) > 0) :
    R.containsPath (path ++ [y]) := by
  intro t
  have h_current_y_not_in_path := not_mem_implies_transition_not_in_zip_tail path x y h_y_not_in_path
  by_cases h_t_eq : t = (x, y)
  · subst h_t_eq
    have h_new_count : countTransitionInPath (x, y) (path ++ [y]) = 1 :=
      countTransitionInPath_append_singleton path x y h_nonempty h_last h_current_y_not_in_path
    unfold countTransitionInPath at h_new_count ⊢
    aesop
  · have h_count_same : countTransitionInPath t (path ++ [y]) = countTransitionInPath t path :=
      countTransitionInPath_append_singleton_other path x y t h_nonempty h_last h_t_eq
    unfold countTransitionInPath at h_count_same ⊢
    aesop

/-- Helper: Starting from a current node with outgoing edges, excluding visited states,
    we can find a leaf reachable from the root. Uses strong induction on unvisited state count. -/
lemma acyclic_has_leaf_aux (R : Run S) (root current : S)
    (path : List S)
    (h_acyclic : R.isAcyclic)
    (h_start : path.head? = some root)
    (h_end : path.getLast? = some current)
    (h_nonempty : path ≠ [])
    (h_contains : R.containsPath path)
    (h_has_out : ∃ y, y ∉ path ∧ R (current, y) > 0) :
    ∃ leaf, R.isLeaf root leaf := by
  -- Get a successor not in path
  obtain ⟨y, h_y_not_in_path, h_edge⟩ := h_has_out

  -- Check if y has any outgoing edges to states not in path ++ [y]
  by_cases h_y_has_out : ∃ z, z ∉ path ∧ z ≠ y ∧ R (y, z) > 0
  case neg =>
    -- y has no outgoing edges to states not in path ++ [y]
    -- We'll show y is actually a leaf (has NO outgoing edges at all)
    use y
    constructor
    · -- Show y is reachable from root
      -- Extend the path by adding y
      use path ++ [y]
      constructor
      · aesop
      constructor
      · simp
      constructor
      · aesop
      · exact containsPath_append_singleton R path current y h_nonempty h_end h_contains h_y_not_in_path h_edge
    · -- Show y has no outgoing edges
      intro z
      by_contra h_pos
      push_neg at h_y_has_out
      -- If R(y,z) > 0, then by h_y_has_out, either z ∈ path or z = y
      have h_z_pos : R (y, z) > 0 := by omega
      have h_z_in_path_or_y : z ∈ path ∨ z = y := by grind

      -- Derive contradiction from cycle
      cases h_z_in_path_or_y with
      | inl h_z_in_path =>
        -- z ∈ path, so we can construct a cycle
        -- path ends with current, current → y, y → z, and z ∈ path
        -- This creates a cycle: (suffix of path from z to current) → y → z
        have h_z_in_extended : z ∈ path ++ [y] := by aesop
        exact acyclic_edge_not_in_path R (path ++ [y]) y z h_acyclic (by simp) (containsPath_append_singleton R path current y h_nonempty h_end h_contains h_y_not_in_path h_edge) h_z_pos h_z_in_extended
      | inr h_z_eq_y =>
        -- z = y, so we have a self-loop y → y
        rw [h_z_eq_y] at h_z_pos
        exact acyclic_no_self_loop R y h_acyclic h_z_pos

  case pos =>
    -- y has an outgoing edge to some z not in path and z ≠ y
    -- Recurse with path ++ [y]
    obtain ⟨z, h_z_not_in_path, h_z_ne_y, h_y_z_edge⟩ := h_y_has_out

    -- Construct new path
    let new_path := path ++ [y]

    -- Show properties of new_path
    have h_new_start : new_path.head? = some root := by aesop
    have h_new_end : new_path.getLast? = some y := by aesop
    have h_new_nonempty : new_path ≠ [] := by aesop
    have h_new_contains : R.containsPath new_path :=
      containsPath_append_singleton R path current y h_nonempty h_end h_contains h_y_not_in_path h_edge

    have h_new_has_out : ∃ w, w ∉ new_path ∧ R (y, w) > 0 := by grind
    exact acyclic_has_leaf_aux R root y new_path h_acyclic h_new_start h_new_end h_new_nonempty h_new_contains h_new_has_out
termination_by Fintype.card S - path.toFinset.card
decreasing_by
  simp_wf
  -- new_path = path ++ [y], and y ∉ path, so toFinset increases by 1
  have h_y_not_mem : y ∉ path.toFinset := by
    simp
    exact h_y_not_in_path
  have h_card_increase : (insert y path.toFinset).card = path.toFinset.card + 1 := by
    rw [Finset.card_insert_of_notMem h_y_not_mem]
  -- path.toFinset is a strict subset of univ
  have h_path_subset := finset_ssubset_univ_of_not_mem path.toFinset y h_y_not_mem
  have h_card_bound : path.toFinset.card < Fintype.card S := by
    rw [← Finset.card_univ]
    exact Finset.card_lt_card h_path_subset
  rw [h_card_increase]
  omega

/-- A finite DAG reachable from a root has at least one leaf. -/
lemma acyclic_has_leaf (R : Run S) (root : S)
    (h_acyclic : R.isAcyclic)
    (h_has_out : ∃ y, R (root, y) > 0) :
    ∃ leaf, R.isLeaf root leaf := by
  -- Start with path = [root]
  have h_root_start : [root].head? = some root := by simp
  have h_root_end : [root].getLast? = some root := by simp
  have h_root_nonempty : [root] ≠ [] := by simp
  have h_root_contains : R.containsPath [root] := by
    intro t
    simp [countTransitionInPath]

  -- Apply the auxiliary lemma
  obtain ⟨y, h_pos⟩ := h_has_out
  apply acyclic_has_leaf_aux R root root [root] h_acyclic h_root_start h_root_end h_root_nonempty h_root_contains
  use y
  constructor
  · intro h_mem
    simp at h_mem
    rw [h_mem] at h_pos
    exact acyclic_no_self_loop R root h_acyclic h_pos
  · exact h_pos

/-- If one element of a sum is positive and all elements are nonnegative, the sum is positive. -/
lemma sum_pos_of_pos_element {α : Type*} [Fintype α] (f : α → ℤ) (a : α)
    (h_pos : f a > 0)
    (h_nonneg : ∀ x, f x ≥ 0) :
    ∑ x : α, f x > 0 := by
  have h_a_in_sum : f a ≤ ∑ x : α, f x := by
    calc f a
      = ∑ x ∈ ({a} : Finset α), f x := by simp
    _ ≤ ∑ x : α, f x := by
        apply Finset.sum_le_univ_sum_of_nonneg
        intro x
        exact h_nonneg x
  omega

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
    apply sum_pos_of_pos_element (fun z => (R (z, leaf) : ℤ)) y
    · omega
    · intro x
      have : (R (x, leaf) : ℤ) = ↑(R (x, leaf)) := rfl
      omega
  -- Combine: 0 - (positive) < 0
  rw [h_outflow_zero]
  omega

/-- If all elements of a function are zero, then the sum is zero. -/
lemma sum_zero_of_all_zero {α : Type*} [Fintype α] (f : α → ℕ) (h : ∀ x, f x = 0) :
    ∑ x : α, (f x : ℤ) = 0 := by
  simp [h]

/-- A sum of natural numbers cast to integers is nonnegative. -/
lemma sum_nat_cast_nonneg {α : Type*} [Fintype α] (f : α → ℕ) :
    0 ≤ ∑ x : α, (f x : ℤ) := by
  apply Finset.sum_nonneg
  intro x _
  omega

/-- If a state has positive net flow, it must have an outgoing edge. -/
lemma positive_netFlow_has_outgoing_edge (R : Run S) (s : S)
    (h_pos : R.netFlow s > 0) :
    ∃ y, R (s, y) > 0 := by
  -- By contradiction: if all outgoing edges are 0, then netFlow ≤ 0
  by_contra h_none
  push_neg at h_none
  -- All outgoing edges have capacity 0
  have h_outflow_zero : ∑ y : S, (R (s, y) : ℤ) = 0 := by
    apply sum_zero_of_all_zero
    intro y
    have h_le := h_none y
    omega
  -- But netFlow = outflow - inflow > 0
  unfold Run.netFlow at h_pos
  rw [h_outflow_zero] at h_pos
  -- This gives 0 - inflow > 0, so inflow < 0, impossible for ℕ
  have h_inflow_nonneg := sum_nat_cast_nonneg (fun y => R (y, s))
  omega

/-- If a list has length ≥ 2 and last element x, then there's a transition into x. -/
lemma last_has_incoming_transition {α : Type*} (l : List α) (x : α)
    (h_len : l.length ≥ 2)
    (h_last : l.getLast? = some x) :
    ∃ y, (y, x) ∈ l.zip l.tail := by
  cases l with
  | nil => simp at h_len
  | cons hd tl =>
    cases tl with
    | nil => simp at h_len
    | cons hd2 tl2 =>
      -- l = [hd, hd2] ++ tl2, so l.tail = [hd2] ++ tl2
      -- getLast of l is getLast of tail
      simp only [List.getLast?_cons_cons] at h_last
      -- If tl2 = [], then getLast? = some hd2, so x = hd2, and (hd, hd2) is in zip
      cases tl2 with
      | nil => aesop
      | cons hd3 tl3 =>
        have h_tail_len : (hd2 :: hd3 :: tl3).length ≥ 2 := by grind
        obtain ⟨y, h_y_in⟩ := last_has_incoming_transition (hd2 :: hd3 :: tl3) x h_tail_len h_last
        aesop

omit [DecidableEq S] [Fintype S] in
/-- A non-empty path with distinct head and last has length at least 2. -/
lemma path_distinct_head_last_length_ge_two {α : Type*} (path : List α) (x y : α)
    (h_nonempty : path ≠ [])
    (h_head : path.head? = some x)
    (h_last : path.getLast? = some y)
    (h_ne : x ≠ y) :
    path.length ≥ 2 := by
  by_contra h_not
  push_neg at h_not
  cases path with
  | nil => simp at h_nonempty
  | cons hd tl =>
    cases tl with
    | nil =>
      -- Singleton list [hd]
      simp only [List.head?, Option.some.injEq, List.getLast?,
        List.getLast_singleton] at h_head h_last
      have : x = y := by rw [← h_head, ← h_last]
      exact h_ne this
    | cons hd2 tl2 =>
      -- Length is at least 2
      simp only [List.length] at h_not
      omega

omit [Fintype S] in
/-- A leaf reachable from a root (with root ≠ leaf) must have an incoming edge. -/
lemma reachable_leaf_has_incoming_edge (R : Run S) (root leaf : S)
    (h_leaf : R.isLeaf root leaf)
    (h_ne : root ≠ leaf) :
    ∃ y, R (y, leaf) > 0 := by
  -- From R.isLeaf, we have R.reachable root leaf
  obtain ⟨h_reach, _⟩ := h_leaf
  -- From reachability, we have a path from root to leaf
  obtain ⟨path, h_head, h_last, h_nonempty, h_contains⟩ := h_reach
  -- Since root ≠ leaf, the path has length ≥ 2
  have h_len := path_distinct_head_last_length_ge_two path root leaf h_nonempty h_head h_last h_ne
  -- Use the helper lemma to get a transition into leaf
  obtain ⟨y, h_y_leaf_in⟩ := last_has_incoming_transition path leaf h_len h_last
  -- This transition has positive capacity in R
  use y
  exact containsPath_has_positive_transition R path h_contains (y, leaf) h_y_leaf_in

/-- If net flow is +1 at s and 0 elsewhere except d, then any state with negative net flow must be d. -/
lemma unique_negative_netFlow (R : Run S) (s d x : S)
    (h_source : R.netFlow s = 1)
    (h_others : ∀ y, y ≠ s → y ≠ d → R.netFlow y = 0)
    (h_x_neg : R.netFlow x < 0) :
    x = d := by
  by_contra h_ne
  have h_not_s : x ≠ s := by
    intro h_eq
    rw [h_eq] at h_x_neg
    rw [h_source] at h_x_neg
    omega
  have h_x_zero := h_others x h_not_s h_ne
  omega

/-- A leaf reachable from a root with outgoing edges has an incoming edge and negative net flow. -/
lemma leaf_has_incoming_and_negative_netFlow (R : Run S) (root leaf : S)
    (h_leaf : R.isLeaf root leaf)
    (h_root_out : ∃ y, R (root, y) > 0) :
    R.netFlow leaf < 0 := by
  apply leaf_has_negative_netFlow R root leaf h_leaf
  -- Need to show ∃ y, R (y, leaf) > 0
  -- This requires root ≠ leaf
  by_cases h_eq : root = leaf
  · -- If root = leaf, then root is a leaf (no outgoing edges)
    subst h_eq
    obtain ⟨_, h_no_out⟩ := h_leaf
    obtain ⟨y, h_pos⟩ := h_root_out
    have := h_no_out y
    omega
  · -- root ≠ leaf, so use the helper lemma
    exact reachable_leaf_has_incoming_edge R root leaf h_leaf h_eq

/-- Main theorem: If the net flow is +1 at source s, -1 at sink d, and 0 elsewhere,
    then there exists a cycle-free path from s to d. -/
theorem exists_path_from_source_to_sink
    (R : Run S) (s d : S)
    (h_source : R.netFlow s = 1)
    (h_sink : R.netFlow d = -1)
    (h_others : ∀ x, x ≠ s → x ≠ d → R.netFlow x = 0) :
    ∃ (path : List S), path.head? = some s ∧ path.getLast? = some d ∧
      path ≠ [] ∧ R.containsPath path ∧ path.Nodup := by
  -- Reduce to acyclic case by removing cycles
  by_cases h_cyclic : R.hasCycle
  case pos =>
    -- R has a cycle, remove it and recurse
    obtain ⟨R', h_netFlow_preserved, h_size_lt, h_R'_le_R⟩ := exists_smaller_run_with_same_netFlow R h_cyclic
    -- R' has the same net flows
    have h_source' : R'.netFlow s = 1 := by aesop
    have h_sink' : R'.netFlow d = -1 := by aesop
    have h_others' : ∀ x, x ≠ s → x ≠ d → R'.netFlow x = 0 := by aesop
    -- Recursive call with smaller run
    obtain ⟨path, h_head, h_last, h_nonempty, h_contains', h_nodup⟩ :=
      exists_path_from_source_to_sink R' s d h_source' h_sink' h_others'
    use path
    refine ⟨h_head, h_last, h_nonempty, ?_, h_nodup⟩
    -- Show R.containsPath path from R'.containsPath path
    -- R' t ≤ R t for all t (from exists_smaller_run_with_same_netFlow)
    intro t
    calc countTransitionInPath t path
      ≤ R' t := h_contains' t
    _ ≤ R t := h_R'_le_R t
  case neg =>
    -- R is acyclic
    have h_acyclic : R.isAcyclic := h_cyclic

    -- s has positive net flow, so it has an outgoing edge
    have h_s_out : ∃ y, R (s, y) > 0 := by
      apply positive_netFlow_has_outgoing_edge
      rw [h_source]
      omega

    -- Find a leaf reachable from s
    obtain ⟨leaf, h_leaf⟩ := acyclic_has_leaf R s h_acyclic h_s_out

    -- The leaf has negative net flow
    have h_leaf_neg := leaf_has_incoming_and_negative_netFlow R s leaf h_leaf h_s_out

    -- Identify leaf = d (only state with negative net flow)
    have h_leaf_eq_d := unique_negative_netFlow R s d leaf h_source h_others h_leaf_neg

    -- Extract the path from s to d
    rw [h_leaf_eq_d] at h_leaf
    obtain ⟨h_reach, _⟩ := h_leaf
    obtain ⟨path, h_head, h_last, h_nonempty, h_contains⟩ := h_reach
    use path
    refine ⟨h_head, h_last, h_nonempty, h_contains, ?_⟩
    exact acyclic_containsPath_nodup R path h_acyclic h_contains
termination_by R.size
decreasing_by
  simp_wf
  exact h_size_lt

end Utils.StateTransition
