import Clean.Examples.FemtoCairo.Types
import Clean.Examples.FemtoCairo.Spec
import Clean.Examples.FemtoCairo.FemtoCairo
import Clean.Utils.SourceSinkPath

/-!
# NanoCairoMultiplicity

A FemtoCairo-like VM example that uses the multiplicity-based approach from `SourceSinkPath.lean`
to prove execution correctness without timestamps.

## Key Insight

Instead of using `InductiveTable` with explicit step indices, we track VM execution using
global multiset operations:
- Each transition circuit emits `add` operations on a global multiset
- For each VM step from state `s1` to state `s2`:
  - Add entry `("state", [s1.pc, s1.ap, s1.fp])` with multiplicity -1 (remove source)
  - Add entry `("state", [s2.pc, s2.ap, s2.fp])` with multiplicity +1 (add destination)
- At boundaries: initial state +1, final state -1
- Net result: all intermediate states have net multiplicity 0

The `SourceSinkPath.exists_path_from_source_to_sink` theorem then proves: if net flow is +1 at
initial, -1 at final, and 0 elsewhere, a valid execution path exists.
-/

namespace Examples.NanoCairoMultiplicity
open Examples.FemtoCairo
open Examples.FemtoCairo.Types
open Examples.FemtoCairo.Spec

variable {p : ℕ} [Fact p.Prime] [p_large_enough: Fact (p > 512)]

-- State (F p) inherits DecidableEq and Fintype from the derived/defined instances
instance : DecidableEq (State (F p)) := inferInstance
instance : Fintype (State (F p)) := inferInstance

-- ============================================================================
-- Circuit Building Blocks
-- ============================================================================

/-- Emit an add operation to the global multiset -/
@[circuit_norm]
def emitAdd (name : String) (multiplicity : ℤ) (values : List (Expression (F p))) : Circuit (F p) Unit := fun _ =>
  ((), [.add multiplicity { name, values }])

/-- The step circuit that wraps FemtoCairo's step circuit and adds multiplicity tracking -/
def stepWithMultiplicity
    {programSize : ℕ} [NeZero programSize] (program : Fin programSize → (F p)) (h_programSize : programSize < p)
    {memorySize : ℕ} [NeZero memorySize] (memory : Fin memorySize → (F p)) (h_memorySize : memorySize < p)
    (state : Var State (F p)) : Circuit (F p) (Var State (F p)) := do
  -- Emit remove of current state (multiplicity -1)
  emitAdd "state" (-1) [state.pc, state.ap, state.fp]

  -- Perform the actual step using FemtoCairo's elaborated circuit
  let nextState ← (femtoCairoStepElaboratedCircuit program h_programSize memory h_memorySize).main state

  -- Emit add of next state (multiplicity +1)
  emitAdd "state" 1 [nextState.pc, nextState.ap, nextState.fp]

  return nextState

/-- Initial state boundary circuit: adds initial state with +1 -/
def initialBoundary (initialState : Var State (F p)) : Circuit (F p) Unit :=
  emitAdd "state" 1 [initialState.pc, initialState.ap, initialState.fp]

/-- Final state boundary circuit: removes final state with -1 -/
def finalBoundary (finalState : Var State (F p)) : Circuit (F p) Unit :=
  emitAdd "state" (-1) [finalState.pc, finalState.ap, finalState.fp]

-- ============================================================================
-- Connection to SourceSinkPath
-- ============================================================================

/-- A valid execution path: each consecutive pair is a valid transition -/
def validExecutionPath
    {programSize : ℕ} [NeZero programSize] (program : Fin programSize → (F p))
    {memorySize : ℕ} [NeZero memorySize] (memory : Fin memorySize → (F p))
    (path : List (State (F p))) : Prop :=
  ∀ i (h : i + 1 < path.length),
    femtoCairoMachineTransition program memory path[i] = some path[i + 1]

-- ============================================================================
-- Verifier's View: Multiplicities Balance to Zero
-- ============================================================================

/-- A list of transitions (src, dst) claimed by the prover -/
abbrev TransitionList (F : Type) := List (State F × State F)

/-- All transitions in the list are valid according to the VM -/
def AllTransitionsValid
    {programSize : ℕ} [NeZero programSize] (program : Fin programSize → (F p))
    {memorySize : ℕ} [NeZero memorySize] (memory : Fin memorySize → (F p))
    (transitions : TransitionList (F p)) : Prop :=
  ∀ t ∈ transitions, femtoCairoMachineTransition program memory t.1 = some t.2

/-- Count how many times a state appears as source (with -1) in transitions -/
def countAsSource (transitions : TransitionList (F p)) (s : State (F p)) : ℕ :=
  transitions.countP fun (src, _) => decide (src = s)

/-- Count how many times a state appears as destination (with +1) in transitions -/
def countAsDest (transitions : TransitionList (F p)) (s : State (F p)) : ℕ :=
  transitions.countP fun (_, dst) => decide (dst = s)

/-- Net flow at a state from transitions: outflow - inflow = sources - destinations -/
def netFlowFromTransitions (transitions : TransitionList (F p)) (s : State (F p)) : ℤ :=
  (countAsSource transitions s : ℤ) - (countAsDest transitions s : ℤ)

/-- Build a Run from transitions -/
def transitionsToRun (transitions : TransitionList (F p)) : Utils.StateTransition.Run (State (F p)) :=
  fun t => transitions.countP (fun t' => decide (t' = t))

omit p_large_enough in
/-- Sum of countP over all second components equals countP on first component -/
lemma sum_countP_fst_eq
    (transitions : TransitionList (F p)) (s : State (F p)) :
    ∑ y : State (F p), (transitions.countP (fun t' => decide (t' = (s, y))) : ℤ) =
      (countAsSource transitions s : ℤ) := by
  simp only [countAsSource]
  rw [← Nat.cast_sum]
  congr 1
  -- Each transition (src, dst) contributes 1 to exactly one term in the sum (when y = dst)
  induction transitions with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.countP_cons]
    rw [Finset.sum_add_distrib, ih]
    congr 1
    -- Show that ∑ y, (if hd = (s, y) then 1 else 0) = if hd.1 = s then 1 else 0
    cases hd with | mk src dst =>
    by_cases h : src = s
    · subst h
      simp only [decide_eq_true_eq, Prod.mk.injEq, true_and]
      rw [Finset.sum_ite_eq Finset.univ dst (fun _ => (1 : ℕ))]
      simp
    · simp only [decide_eq_true_eq, Prod.mk.injEq, h, false_and, ↓reduceIte,
        Finset.sum_const_zero]

omit p_large_enough in
/-- Sum of countP over all first components equals countP on second component -/
lemma sum_countP_snd_eq
    (transitions : TransitionList (F p)) (s : State (F p)) :
    ∑ y : State (F p), (transitions.countP (fun t' => decide (t' = (y, s))) : ℤ) =
      (countAsDest transitions s : ℤ) := by
  simp only [countAsDest]
  rw [← Nat.cast_sum]
  congr 1
  -- Each transition (src, dst) contributes 1 to exactly one term in the sum (when y = src)
  induction transitions with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.countP_cons]
    rw [Finset.sum_add_distrib, ih]
    congr 1
    -- Show that ∑ y, (if hd = (y, s) then 1 else 0) = if hd.2 = s then 1 else 0
    cases hd with | mk src dst =>
    by_cases h : dst = s
    · subst h
      simp only [decide_eq_true_eq, Prod.mk.injEq, and_true]
      rw [Finset.sum_ite_eq Finset.univ src (fun _ => (1 : ℕ))]
      simp
    · simp only [decide_eq_true_eq, Prod.mk.injEq, h, and_false, ↓reduceIte,
        Finset.sum_const_zero]

omit p_large_enough in
/-- The Run.netFlow equals netFlowFromTransitions for the generated Run -/
theorem run_netFlow_eq_transitionNetFlow
    (transitions : TransitionList (F p)) (s : State (F p)) :
    Utils.StateTransition.Run.netFlow (transitionsToRun transitions) s =
      netFlowFromTransitions transitions s := by
  unfold Utils.StateTransition.Run.netFlow transitionsToRun netFlowFromTransitions
  have h1 : ∑ y : State (F p), (transitions.countP (fun t' => decide (t' = (s, y))) : ℤ) =
      (countAsSource transitions s : ℤ) := sum_countP_fst_eq transitions s
  have h2 : ∑ y : State (F p), (transitions.countP (fun t' => decide (t' = (y, s))) : ℤ) =
      (countAsDest transitions s : ℤ) := sum_countP_snd_eq transitions s
  calc _ = ∑ y, (transitions.countP (fun t' => decide (t' = (s, y))) : ℤ) -
           ∑ y, (transitions.countP (fun t' => decide (t' = (y, s))) : ℤ) := rfl
       _ = (countAsSource transitions s : ℤ) - (countAsDest transitions s : ℤ) := by rw [h1, h2]
       _ = _ := rfl

omit p_large_enough in
/-- Main soundness theorem: valid transitions with proper flow imply valid execution path exists.

    This is what the verifier can derive:
    - The prover provides a list of transitions
    - Each transition is valid (circuit soundness)
    - The multiplicities balance properly (source has +1, sink has -1, others 0)
    - Therefore a valid execution path from source to sink exists
-/
theorem multiplicity_soundness
    {programSize : ℕ} [NeZero programSize] (program : Fin programSize → (F p))
    {memorySize : ℕ} [NeZero memorySize] (memory : Fin memorySize → (F p))
    (transitions : TransitionList (F p))
    (initialState finalState : State (F p))
    -- All claimed transitions are valid (from circuit soundness)
    (h_valid : AllTransitionsValid program memory transitions)
    -- Net flow conditions (from multiplicity balance check)
    (h_source : netFlowFromTransitions transitions initialState = 1)
    (h_conserved : ∀ s, s ≠ initialState → s ≠ finalState → netFlowFromTransitions transitions s = 0)
    : ∃ path : List (State (F p)),
        path.head? = some initialState ∧
        path.getLast? = some finalState ∧
        path ≠ [] ∧
        validExecutionPath program memory path := by
  -- Use transitionsToRun to get a Run, then apply exists_path_from_source_to_sink
  let R := transitionsToRun transitions
  -- Show R.netFlow matches our conditions
  have h_R_source : R.netFlow initialState = 1 := by
    rw [run_netFlow_eq_transitionNetFlow]
    exact h_source
  have h_R_conserved : ∀ s, s ≠ initialState → s ≠ finalState → R.netFlow s = 0 := by
    intro s hs1 hs2
    rw [run_netFlow_eq_transitionNetFlow]
    exact h_conserved s hs1 hs2
  -- Apply SourceSinkPath theorem
  obtain ⟨path, h_head, h_last, h_nonempty, h_contains, _⟩ :=
    Utils.StateTransition.exists_path_from_source_to_sink R initialState finalState h_R_source h_R_conserved
  use path
  refine ⟨h_head, h_last, h_nonempty, ?_⟩
  -- Show each transition in path is valid
  intro i hi
  -- The transition (path[i], path[i+1]) appears in the path at index i
  let t := (path[i], path[i + 1])
  -- countTransitionInPath counts occurrences of t in (path.zip path.tail)
  -- Since (path[i], path[i+1]) is at index i in (path.zip path.tail), count ≥ 1
  have h_count_in_path : Utils.StateTransition.countTransitionInPath t path ≥ 1 := by
    simp only [Utils.StateTransition.countTransitionInPath]
    have h_zip_len : i < (path.zip path.tail).length := by
      simp only [List.length_zip, List.length_tail]
      omega
    have h_mem : t ∈ path.zip path.tail := by
      rw [List.mem_iff_getElem]
      use i, h_zip_len
      simp only [List.getElem_zip, List.getElem_tail]
      rfl
    exact List.count_pos_iff.mpr h_mem
  -- h_contains says: for each t, countInPath t ≤ R t
  have h_in_run : R t ≥ 1 := Nat.le_trans h_count_in_path (h_contains t)
  -- Since R t = transitions.countP (· = t) ≥ 1, t is in transitions
  have h_in_transitions : t ∈ transitions := by
    have h_count_pos : 0 < transitions.countP (fun t' => decide (t' = t)) := h_in_run
    rw [List.countP_pos_iff] at h_count_pos
    obtain ⟨t', h_mem, h_eq⟩ := h_count_pos
    simp only [decide_eq_true_eq] at h_eq
    rw [← h_eq]
    exact h_mem
  -- Therefore it's valid
  exact h_valid _ h_in_transitions

end Examples.NanoCairoMultiplicity
