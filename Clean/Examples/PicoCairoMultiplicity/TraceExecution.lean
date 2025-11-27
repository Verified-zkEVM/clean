/-
PicoCairoMultiplicity Trace Execution
Proves that the ExecutionBundle spec implies existence of a valid FemtoCairo execution.
-/

import Clean.Circuit.Basic
import Clean.Circuit.Subcircuit
import Clean.Utils.SourceSinkPath
import Clean.Examples.PicoCairoMultiplicity.Types
import Clean.Examples.PicoCairoMultiplicity.ExecutionBundle
import Clean.Examples.PicoCairoMultiplicity.AddInstruction
import Clean.Examples.PicoCairoMultiplicity.MulInstruction
import Clean.Examples.PicoCairoMultiplicity.StoreStateInstruction
import Clean.Examples.PicoCairoMultiplicity.LoadStateInstruction
import Clean.Examples.FemtoCairo.Types
import Clean.Examples.FemtoCairo.Spec

namespace Examples.PicoCairoMultiplicity.TraceExecution

open Examples.FemtoCairo
open Examples.FemtoCairo.Types
open Examples.FemtoCairo.Spec
open Examples.PicoCairoMultiplicity.Types
open Examples.PicoCairoMultiplicity.ExecutionBundle

variable {p : ℕ} [Fact p.Prime] [p_large_enough: Fact (p > 512)]

/-! ## Helper: State to NamedList conversion -/

/-- Convert a State to the corresponding "state" NamedList -/
def stateToNamedList (s : State (F p)) : NamedList (F p) :=
  ⟨"state", [s.pc, s.ap, s.fp]⟩

/-- The inverse: extract a State from a "state" NamedList -/
def namedListToState (nl : NamedList (F p)) : Option (State (F p)) :=
  if nl.name = "state" then
    match nl.values with
    | [pc, ap, fp] => some { pc, ap, fp }
    | _ => none
  else none

theorem stateToNamedList_injective : Function.Injective (stateToNamedList (p := p)) := by
  intro s1 s2 h
  simp only [stateToNamedList] at h
  injection h with _ h_values
  have h_pc : s1.pc = s2.pc := by
    have := congrArg (fun l => l.head?) h_values
    simp at this; exact this
  have h_ap : s1.ap = s2.ap := by
    have := congrArg (fun l => l.tail?.bind List.head?) h_values
    simp at this; exact this
  have h_fp : s1.fp = s2.fp := by
    have := congrArg (fun l => l.tail?.bind (·.tail?.bind List.head?)) h_values
    simp at this; exact this
  cases s1; cases s2
  simp at h_pc h_ap h_fp
  simp [h_pc, h_ap, h_fp]

theorem namedListToState_stateToNamedList (s : State (F p)) :
    namedListToState (stateToNamedList s) = some s := by
  simp [namedListToState, stateToNamedList]

/-! ## Individual instruction specs imply valid transitions -/

/-- ADD instruction spec (when enabled) implies valid femtoCairo transition -/
theorem AddInstruction_Spec_implies_transition
    {programSize : ℕ} [NeZero programSize] (program : Fin programSize → F p)
    {memorySize : ℕ} [NeZero memorySize] (memory : Fin memorySize → F p)
    (input : InstructionStepInput (F p)) (adds : InteractionDelta (F p))
    (h_spec : AddInstruction.Spec program memory input adds)
    (h_enabled : input.enabled = 1) :
    ∃ (postState : State (F p)),
      femtoCairoMachineTransition program memory input.preState = some postState ∧
      adds = InteractionDelta.single (stateToNamedList input.preState) (-1) +
             InteractionDelta.single (stateToNamedList postState) 1 := by
  simp only [AddInstruction.Spec, h_enabled, ite_true] at h_spec
  -- Split on fetchInstruction result
  split at h_spec
  case h_2 => exact h_spec.elim
  case h_1 rawInstr h_fetch =>
    -- Split on decodeInstruction result
    split at h_spec
    case h_2 => exact h_spec.elim
    case h_1 instrType mode1 mode2 mode3 h_decode =>
      -- Check instrType = 0
      split at h_spec
      case isTrue h_add =>
        -- Split on memory accesses
        split at h_spec
        case h_1 v1 v2 v3 h_mem1 h_mem2 h_mem3 =>
          obtain ⟨h_add_eq, h_adds_eq⟩ := h_spec
          -- Construct the post state
          use { pc := input.preState.pc + 4, ap := input.preState.ap, fp := input.preState.fp }
          constructor
          · -- Show femtoCairoMachineTransition returns postState
            simp only [femtoCairoMachineTransition, h_fetch, h_decode, h_mem1, h_mem2, h_mem3,
              computeNextState, h_add, h_add_eq, ite_true, Option.bind_eq_bind, Option.bind_some]
          · -- Show adds equality
            simp only [stateToNamedList]
            exact h_adds_eq
        all_goals exact h_spec.elim
      case isFalse => exact h_spec.elim

/-- MUL instruction spec (when enabled) implies valid femtoCairo transition -/
theorem MulInstruction_Spec_implies_transition
    {programSize : ℕ} [NeZero programSize] (program : Fin programSize → F p)
    {memorySize : ℕ} [NeZero memorySize] (memory : Fin memorySize → F p)
    (input : InstructionStepInput (F p)) (adds : InteractionDelta (F p))
    (h_spec : MulInstruction.Spec program memory input adds)
    (h_enabled : input.enabled = 1) :
    ∃ (postState : State (F p)),
      femtoCairoMachineTransition program memory input.preState = some postState ∧
      adds = InteractionDelta.single (stateToNamedList input.preState) (-1) +
             InteractionDelta.single (stateToNamedList postState) 1 := by
  simp only [MulInstruction.Spec, h_enabled, ite_true] at h_spec
  -- Split on fetchInstruction result
  split at h_spec
  case h_2 => exact h_spec.elim
  case h_1 rawInstr h_fetch =>
    -- Split on decodeInstruction result
    split at h_spec
    case h_2 => exact h_spec.elim
    case h_1 instrType mode1 mode2 mode3 h_decode =>
      -- Check instrType = 1
      split at h_spec
      case isTrue h_mul =>
        -- Split on memory accesses
        split at h_spec
        case h_1 v1 v2 v3 h_mem1 h_mem2 h_mem3 =>
          obtain ⟨h_mul_eq, h_adds_eq⟩ := h_spec
          -- Construct the post state
          use { pc := input.preState.pc + 4, ap := input.preState.ap, fp := input.preState.fp }
          constructor
          · -- Show femtoCairoMachineTransition returns postState
            simp only [femtoCairoMachineTransition, h_fetch, h_decode, h_mem1, h_mem2, h_mem3,
              computeNextState, h_mul, h_mul_eq, ite_true, Option.bind_eq_bind, Option.bind_some]
          · -- Show adds equality
            simp only [stateToNamedList]
            exact h_adds_eq
        all_goals exact h_spec.elim
      case isFalse => exact h_spec.elim

/-- StoreState instruction spec (when enabled) implies valid femtoCairo transition -/
theorem StoreStateInstruction_Spec_implies_transition
    {programSize : ℕ} [NeZero programSize] (program : Fin programSize → F p)
    {memorySize : ℕ} [NeZero memorySize] (memory : Fin memorySize → F p)
    (input : InstructionStepInput (F p)) (adds : InteractionDelta (F p))
    (h_spec : StoreStateInstruction.Spec program memory input adds)
    (h_enabled : input.enabled = 1) :
    ∃ (postState : State (F p)),
      femtoCairoMachineTransition program memory input.preState = some postState ∧
      adds = InteractionDelta.single (stateToNamedList input.preState) (-1) +
             InteractionDelta.single (stateToNamedList postState) 1 := by
  simp only [StoreStateInstruction.Spec, h_enabled, ite_true] at h_spec
  -- Split on fetchInstruction result
  split at h_spec
  case h_2 => exact h_spec.elim
  case h_1 rawInstr h_fetch =>
    -- Split on decodeInstruction result
    split at h_spec
    case h_2 => exact h_spec.elim
    case h_1 instrType mode1 mode2 mode3 h_decode =>
      -- Check instrType = 2
      split at h_spec
      case isTrue h_store =>
        -- Split on memory accesses
        split at h_spec
        case h_1 v1 v2 v3 h_mem1 h_mem2 h_mem3 =>
          obtain ⟨h_v1_pc, h_v2_ap, h_v3_fp, h_adds_eq⟩ := h_spec
          -- Construct the post state
          use { pc := input.preState.pc + 4, ap := input.preState.ap, fp := input.preState.fp }
          constructor
          · -- Show femtoCairoMachineTransition returns postState
            simp only [femtoCairoMachineTransition, h_fetch, h_decode, h_mem1, h_mem2, h_mem3,
              computeNextState, h_store, h_v1_pc, h_v2_ap, h_v3_fp, and_self, ite_true,
              Option.bind_eq_bind, Option.bind_some]
          · -- Show adds equality
            simp only [stateToNamedList]
            exact h_adds_eq
        all_goals exact h_spec.elim
      case isFalse => exact h_spec.elim

/-- LoadState instruction spec (when enabled) implies valid femtoCairo transition -/
theorem LoadStateInstruction_Spec_implies_transition
    {programSize : ℕ} [NeZero programSize] (program : Fin programSize → F p)
    {memorySize : ℕ} [NeZero memorySize] (memory : Fin memorySize → F p)
    (input : InstructionStepInput (F p)) (adds : InteractionDelta (F p))
    (h_spec : LoadStateInstruction.Spec program memory input adds)
    (h_enabled : input.enabled = 1) :
    ∃ (postState : State (F p)),
      femtoCairoMachineTransition program memory input.preState = some postState ∧
      adds = InteractionDelta.single (stateToNamedList input.preState) (-1) +
             InteractionDelta.single (stateToNamedList postState) 1 := by
  simp only [LoadStateInstruction.Spec, h_enabled, ite_true] at h_spec
  -- Split on fetchInstruction result
  split at h_spec
  case h_2 => exact h_spec.elim
  case h_1 rawInstr h_fetch =>
    -- Split on decodeInstruction result
    split at h_spec
    case h_2 => exact h_spec.elim
    case h_1 instrType mode1 mode2 mode3 h_decode =>
      -- Check instrType = 3
      split at h_spec
      case isTrue h_load =>
        -- Split on memory accesses
        split at h_spec
        case h_1 v1 v2 v3 h_mem1 h_mem2 h_mem3 =>
          -- For LOAD_STATE, h_spec is just the adds equality (no extra conditions)
          -- Construct the post state (for LOAD_STATE, it's v1, v2, v3)
          use { pc := v1, ap := v2, fp := v3 }
          constructor
          · -- Show femtoCairoMachineTransition returns postState
            simp only [femtoCairoMachineTransition, h_fetch, h_decode, h_mem1, h_mem2, h_mem3,
              computeNextState, h_load, Option.bind_eq_bind, Option.bind_some]
          · -- Show adds equality
            simp only [stateToNamedList]
            exact h_spec
        all_goals exact h_spec.elim
      case isFalse => exact h_spec.elim

/-! ## Main theorem: Spec implies execution existence -/

open Utils.StateTransition in
/-- A transition from s1 to s2 is valid if femtoCairoMachineTransition returns s2 -/
def IsValidTransition
    {programSize : ℕ} [NeZero programSize] (program : Fin programSize → F p)
    {memorySize : ℕ} [NeZero memorySize] (memory : Fin memorySize → F p)
    (s1 s2 : State (F p)) : Prop :=
  femtoCairoMachineTransition program memory s1 = some s2

open Utils.StateTransition in
/-- A run is valid if every transition with positive count is a valid FemtoCairo transition -/
def IsValidRun
    {programSize : ℕ} [NeZero programSize] (program : Fin programSize → F p)
    {memorySize : ℕ} [NeZero memorySize] (memory : Fin memorySize → F p)
    (R : Run (State (F p))) : Prop :=
  ∀ s1 s2, R (s1, s2) > 0 → IsValidTransition program memory s1 s2

/-- Convert a path of states to a bounded execution count (path length - 1) -/
def pathToExecutionSteps (path : List (State (F p))) : ℕ :=
  path.length - 1

open Utils.StateTransition in
/-- Helper: First transition in a path with at least 2 elements is valid -/
lemma first_transition_valid
    {programSize : ℕ} [NeZero programSize] (program : Fin programSize → F p)
    {memorySize : ℕ} [NeZero memorySize] (memory : Fin memorySize → F p)
    (R : Run (State (F p)))
    (s0 s1 : State (F p)) (rest : List (State (F p)))
    (h_valid_run : IsValidRun program memory R)
    (h_contains : R.containsPath (s0 :: s1 :: rest)) :
    femtoCairoMachineTransition program memory s0 = some s1 := by
  have h_count_pos : countTransitionInPath (s0, s1) (s0 :: s1 :: rest) > 0 := by
    unfold countTransitionInPath
    simp only [List.zip, List.tail, List.zipWith_cons_cons]
    simp only [List.count_cons, beq_self_eq_true, ↓reduceIte]
    omega
  have h_R_pos : R (s0, s1) > 0 := by
    have h_bound := h_contains (s0, s1)
    omega
  exact h_valid_run s0 s1 h_R_pos

open Utils.StateTransition in
/-- Helper: containsPath is preserved when dropping the first element -/
lemma containsPath_tail
    (R : Run (State (F p)))
    (hd : State (F p)) (tl : List (State (F p)))
    (h_contains : R.containsPath (hd :: tl)) :
    R.containsPath tl := by
  intro t
  have h_bound := h_contains t
  unfold countTransitionInPath at h_bound ⊢
  cases tl with
  | nil => simp
  | cons hd2 tl2 =>
    simp only [List.zip, List.tail, List.zipWith_cons_cons] at h_bound
    simp only [List.count_cons] at h_bound
    by_cases h_t : t = (hd, hd2)
    · -- t = (hd, hd2), so we need to show count t in tail ≤ R t
      -- h_bound: count (hd, hd2) in rest + 1 ≤ R (hd, hd2)
      -- Since t = (hd, hd2), count t in (tl.zip tl.tail) = count t in (hd2::tl2).zip tl2
      -- This is ≤ count in full path - 1 ≤ R t - 1 + 1 = R t
      subst h_t
      simp only [beq_self_eq_true, ↓reduceIte] at h_bound
      simp only [List.tail_cons, List.zip]
      -- Need: List.count (hd, hd2) (List.zipWith Prod.mk (hd2 :: tl2) tl2) ≤ R (hd, hd2)
      -- h_bound says: List.count (hd, hd2) (List.zipWith Prod.mk (hd2 :: tl2) tl2) + 1 ≤ R (hd, hd2)
      -- So count ≤ R - 1 ≤ R
      omega
    · -- t ≠ (hd, hd2), so the ite in h_bound evaluates to 0
      have h_ne : (hd, hd2) ≠ t := fun h => h_t h.symm
      have h_beq_false : ((hd, hd2) == t) = false := beq_eq_false_iff_ne.mpr h_ne
      -- Show that the if condition is False
      have h_cond_false : ((hd, hd2) == t) = true ↔ False := by simp [h_beq_false]
      simp only [List.tail_cons, List.zip]
      -- Simplify h_bound using the fact that the condition is false
      have h_simplified : List.count t (List.zipWith Prod.mk (hd2 :: tl2) tl2) + 0 ≤ R t := by
        have : (if ((hd, hd2) == t) = true then 1 else 0) = 0 := by
          simp only [h_beq_false, ↓reduceIte]
          decide
        omega
      omega

/-- Helper: bounded execution followed by one step equals bounded execution with one more step -/
lemma boundedExecution_succ
    {programSize : ℕ} [NeZero programSize] (program : Fin programSize → F p)
    {memorySize : ℕ} [NeZero memorySize] (memory : Fin memorySize → F p)
    (s : State (F p)) (n : ℕ) :
    femtoCairoMachineBoundedExecution program memory (some s) (n + 1) =
    (femtoCairoMachineBoundedExecution program memory (some s) n).bind
      (femtoCairoMachineTransition program memory) := by
  rfl

/-- Helper: bounded execution from some s with transition step prepended -/
lemma boundedExecution_step_prepend
    {programSize : ℕ} [NeZero programSize] (program : Fin programSize → F p)
    {memorySize : ℕ} [NeZero memorySize] (memory : Fin memorySize → F p)
    (s1 s2 : State (F p)) (n : ℕ)
    (h_trans : femtoCairoMachineTransition program memory s1 = some s2) :
    femtoCairoMachineBoundedExecution program memory (some s1) (n + 1) =
    femtoCairoMachineBoundedExecution program memory (some s2) n := by
  induction n generalizing s1 s2 with
  | zero =>
    simp only [femtoCairoMachineBoundedExecution, Option.bind_eq_bind, Option.some_bind, h_trans]
  | succ m ih =>
    -- Goal: bounded (m+2) from s1 = bounded (m+1) from s2
    -- Use the definition: bounded (k+1) = bounded k >>= trans
    -- So LHS = bounded (m+1) from s1 >>= trans
    -- And RHS = bounded m from s2 >>= trans
    -- By IH: bounded (m+1) from s1 = bounded m from s2
    -- Therefore LHS = RHS
    calc femtoCairoMachineBoundedExecution program memory (some s1) (m + 2)
      = (femtoCairoMachineBoundedExecution program memory (some s1) (m + 1)).bind
          (femtoCairoMachineTransition program memory) := rfl
    _ = (femtoCairoMachineBoundedExecution program memory (some s2) m).bind
          (femtoCairoMachineTransition program memory) := by rw [ih s1 s2 h_trans]
    _ = femtoCairoMachineBoundedExecution program memory (some s2) (m + 1) := rfl

open Utils.StateTransition in
/-- If a path is valid (contained in a valid run), then it corresponds to a valid execution -/
theorem valid_path_implies_bounded_execution
    {programSize : ℕ} [NeZero programSize] (program : Fin programSize → F p)
    {memorySize : ℕ} [NeZero memorySize] (memory : Fin memorySize → F p)
    (path : List (State (F p)))
    (s d : State (F p))
    (R : Run (State (F p)))
    (h_valid_run : IsValidRun program memory R)
    (h_contains : R.containsPath path)
    (h_nonempty : path ≠ [])
    (h_head : path.head? = some s)
    (h_last : path.getLast? = some d) :
    femtoCairoMachineBoundedExecution program memory (some s) (pathToExecutionSteps path) = some d := by
  -- Induction on path structure
  induction path generalizing s with
  | nil => simp at h_nonempty
  | cons hd tl ih =>
    -- Extract s = hd from h_head
    simp only [List.head?] at h_head
    cases h_head
    cases tl with
    | nil =>
      -- Single element path: s = d, steps = 0
      simp only [List.getLast?] at h_last
      cases h_last
      simp [pathToExecutionSteps, femtoCairoMachineBoundedExecution]
    | cons hd2 tl2 =>
      -- Path [hd, hd2, ...tl2] has at least 2 elements
      -- Note: hd = s by the cases h_head above
      -- steps = length - 1 = 1 + tl2.length
      simp only [pathToExecutionSteps, List.length_cons, Nat.add_sub_cancel]
      -- Get the first transition (using hd which equals s)
      have h_first_step := first_transition_valid program memory R hd hd2 tl2 h_valid_run h_contains
      -- Use the prepend lemma to shift to starting from hd2
      rw [boundedExecution_step_prepend program memory hd hd2 (tl2.length) h_first_step]
      -- Apply IH to tail path [hd2, ...tl2]
      have h_tail_contains := containsPath_tail R hd (hd2 :: tl2) h_contains
      have h_tail_last : (hd2 :: tl2).getLast? = some d := by
        simp only [List.getLast?] at h_last ⊢
        exact h_last
      have h_ih := ih hd2 h_tail_contains (by simp) rfl h_tail_last
      simp only [pathToExecutionSteps, List.length_cons, Nat.add_sub_cancel] at h_ih
      exact h_ih

/-
## Main Theorem: Spec implies execution

The main theorem states that if ExecutionBundle.Spec holds and the interaction delta is balanced
(sums to zero), then there exists a valid FemtoCairo execution from initialState to finalState.

The proof structure:
1. From Spec, extract that each enabled instruction contributes a valid transition
2. Construct a Run from these transitions
3. Show the Run has the right net flow (source = +1 at initial, sink = -1 at final)
4. Apply exists_path_from_source_to_sink to get a path
5. Convert the path to femtoCairoMachineBoundedExecution
-/

/-!
## Transition extraction from InteractionDelta

The key insight is that when `adds.toFinsupp = 0`, we have:
- initial state: +1 (source)
- final state: -1 (sink)
- each enabled instruction: preState -1, postState +1

This creates a balanced flow graph where we can find a path from initial to final.
-/

/-- A transition record from an instruction -/
structure InstructionTransition (F : Type) where
  preState : State F
  postState : State F

/-- Build a Run from a list of transitions -/
def transitionsToRun {S : Type*} [DecidableEq S] (transitions : List (S × S)) : Utils.StateTransition.Run S :=
  fun t => transitions.count t

/-- The main theorem: If ExecutionBundle.Spec holds with balanced adds, there exists a valid execution.

This is a complex theorem that requires:
1. Extracting all enabled instruction transitions from the spec
2. Building a Run from these transitions
3. Showing the Run has netFlow = +1 at initial, -1 at final, 0 elsewhere
4. Applying exists_path_from_source_to_sink to get a path
5. Converting the path to femtoCairoMachineBoundedExecution

The key insight is that the balanced InteractionDelta (adds.toFinsupp = 0) encodes
a valid execution trace through the source-sink flow property.
-/
theorem Spec_implies_execution
    (capacities : InstructionCapacities)
    {programSize : ℕ} [NeZero programSize] (program : Fin programSize → F p) (h_programSize : programSize < p)
    {memorySize : ℕ} [NeZero memorySize] (memory : Fin memorySize → F p) (h_memorySize : memorySize < p)
    (inputs : ExecutionCircuitInput capacities (F p))
    (adds : InteractionDelta (F p))
    (h_spec : ExecutionBundle.Spec capacities program memory inputs adds)
    (h_balanced : adds.toFinsupp = 0) :
    ∃ (steps : ℕ),
      femtoCairoMachineBoundedExecution program memory (some inputs.initialState) steps =
        some inputs.finalState := by
  -- The proof requires several steps:
  -- 1. From h_spec, extract the individual bundle specs
  obtain ⟨addAdds, mulAdds, storeStateAdds, loadStateAdds, h_add_spec, h_mul_spec, h_store_spec, h_load_spec, h_adds_eq⟩ := h_spec

  -- 2. The balanced condition h_balanced combined with h_adds_eq tells us the flow is balanced
  -- This is a complex proof involving:
  -- - Extracting all enabled instructions
  -- - Building the Run
  -- - Proving net flow properties
  -- - Applying exists_path_from_source_to_sink

  -- For now, we leave this as sorry and note that the proof requires:
  -- - Fintype instance for State (F p) (may need finiteness assumptions)
  -- - Careful accounting of all instruction transitions
  -- - Connection between InteractionDelta multiplicities and Run counts
  sorry

/-!
## Weaker Spec: Execution Existence

The weaker spec states that when the interaction delta is balanced (adds = 0),
there exists a valid execution from initialState to finalState.

This captures the main security property: if the circuit constraints are satisfied
and the multiset of states is balanced, then there is a valid execution trace.
-/

/-- The weaker spec that directly states execution existence when balanced -/
def ExecutionExistenceSpec
    (capacities : InstructionCapacities)
    {programSize : ℕ} [NeZero programSize] (program : Fin programSize → (F p))
    {memorySize : ℕ} [NeZero memorySize] (memory : Fin memorySize → (F p))
    (inputs : ExecutionCircuitInput capacities (F p))
    (adds : InteractionDelta (F p)) : Prop :=
  adds.toFinsupp = 0 →
    ∃ (steps : ℕ),
      femtoCairoMachineBoundedExecution program memory (some inputs.initialState) steps =
        some inputs.finalState

/-- The stronger spec implies the weaker execution existence spec -/
theorem Spec_implies_ExecutionExistenceSpec
    (capacities : InstructionCapacities)
    {programSize : ℕ} [NeZero programSize] (program : Fin programSize → F p) (h_programSize : programSize < p)
    {memorySize : ℕ} [NeZero memorySize] (memory : Fin memorySize → F p) (h_memorySize : memorySize < p)
    (inputs : ExecutionCircuitInput capacities (F p))
    (adds : InteractionDelta (F p))
    (h_spec : ExecutionBundle.Spec capacities program memory inputs adds) :
    ExecutionExistenceSpec capacities program memory inputs adds := by
  intro h_balanced
  exact Spec_implies_execution capacities program h_programSize memory h_memorySize inputs adds h_spec h_balanced

/-
The circuit with the weaker execution existence spec.

This construction uses the fact that the original ExecutionBundle.Spec implies
ExecutionExistenceSpec when the adds are balanced.

Note: To complete this construction, we would need a FormalAssertionChangingMultiset.weakenSpec
lemma analogous to FormalCircuit.weakenSpec.
-/

end Examples.PicoCairoMultiplicity.TraceExecution
