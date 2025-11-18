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

-- Lemmas about cycle removal and net flow

/-- Removing a cycle preserves net flow at each state. -/
lemma netFlow_removeCycle_eq (R : Run S) (cycle : List S) (x : S)
    (h_cycle : cycle.head? = cycle.getLast?) :
    (R.removeCycle cycle).netFlow x = R.netFlow x := by
  sorry

/-- Removing a cycle decreases the total size of the run. -/
lemma size_removeCycle_lt (R : Run S) (cycle : List S)
    (h_nonempty : cycle ≠ [])
    (h_valid : R.validPath cycle)
    (h_cycle : cycle.head? = cycle.getLast?) :
    (R.removeCycle cycle).size < R.size := by
  sorry

/-- If a run has a cycle, it can be removed. -/
lemma exists_smaller_run_with_same_netFlow (R : Run S) (h_cycle : R.hasCycle) :
    ∃ (R' : Run S), (∀ x, R'.netFlow x = R.netFlow x) ∧ R'.size < R.size := by
  sorry

/-- A finite DAG reachable from a root has at least one leaf. -/
lemma acyclic_has_leaf (R : Run S) (root : S)
    (h_acyclic : R.isAcyclic)
    (h_has_out : ∃ y, R (root, y) > 0) :
    ∃ leaf, R.isLeaf root leaf := by
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
      sorry
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
  sorry

end Utils.StateTransition
