/-
PicoCairoMultiplicity Trace Execution
Proves that the ExecutionBundle spec implies existence of a valid FemtoCairo execution.
-/

import Clean.Circuit.Basic
import Clean.Circuit.Subcircuit
import Clean.Circuit.StructuralLemmas
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

omit [Fact (Nat.Prime p)] p_large_enough in
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

omit [Fact (Nat.Prime p)] p_large_enough in
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

omit p_large_enough in
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

omit p_large_enough in
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

omit p_large_enough in
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
/-- The first transition in a path has count > 0 -/
lemma countTransitionInPath_first_pos {α : Type*} [DecidableEq α] (s0 s1 : α) (rest : List α) :
    countTransitionInPath (s0, s1) (s0 :: s1 :: rest) > 0 := by
  unfold countTransitionInPath
  simp only [List.zip, List.tail, List.zipWith_cons_cons]
  simp only [List.count_cons, beq_self_eq_true, ↓reduceIte]
  omega

omit p_large_enough in
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
  have h_R_pos : R (s0, s1) > 0 := by
    have h_bound := h_contains (s0, s1)
    have h_count_pos := countTransitionInPath_first_pos s0 s1 rest
    omega
  exact h_valid_run s0 s1 h_R_pos

omit [Fact (Nat.Prime p)] p_large_enough in
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
          simp only [h_beq_false]
          decide
        omega
      omega

omit p_large_enough in
/-- Helper: bounded execution followed by one step equals bounded execution with one more step -/
lemma boundedExecution_succ
    {programSize : ℕ} [NeZero programSize] (program : Fin programSize → F p)
    {memorySize : ℕ} [NeZero memorySize] (memory : Fin memorySize → F p)
    (s : State (F p)) (n : ℕ) :
    femtoCairoMachineBoundedExecution program memory (some s) (n + 1) =
    (femtoCairoMachineBoundedExecution program memory (some s) n).bind
      (femtoCairoMachineTransition program memory) := by
  rfl

omit p_large_enough in
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
    simp only [femtoCairoMachineBoundedExecution, Option.bind_eq_bind, Option.bind_some, h_trans]
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

omit p_large_enough in
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

/-! ## Helper lemmas for extracting transitions from bundle specs -/

/-- Extract the post state from an ADD instruction when enabled -/
def addPostState (preState : State (F p)) : State (F p) :=
  { pc := preState.pc + 4, ap := preState.ap, fp := preState.fp }

/-- Extract the post state from a MUL instruction when enabled -/
def mulPostState (preState : State (F p)) : State (F p) :=
  { pc := preState.pc + 4, ap := preState.ap, fp := preState.fp }

/-- Extract the post state from a StoreState instruction when enabled -/
def storeStatePostState (preState : State (F p)) : State (F p) :=
  { pc := preState.pc + 4, ap := preState.ap, fp := preState.fp }

/-- For a single enabled ADD instruction, extract the transition -/
def extractAddTransition (input : InstructionStepInput (F p)) (_h_enabled : input.enabled = 1) :
    State (F p) × State (F p) :=
  (input.preState, addPostState input.preState)

/-- For a single enabled MUL instruction, extract the transition -/
def extractMulTransition (input : InstructionStepInput (F p)) (_h_enabled : input.enabled = 1) :
    State (F p) × State (F p) :=
  (input.preState, mulPostState input.preState)

/-- For a single enabled StoreState instruction, extract the transition -/
def extractStoreStateTransition (input : InstructionStepInput (F p)) (_h_enabled : input.enabled = 1) :
    State (F p) × State (F p) :=
  (input.preState, storeStatePostState input.preState)

/-- Extract all enabled transitions from a vector of inputs -/
def extractEnabledTransitions {n : ℕ}
    (inputs : Vector (InstructionStepInput (F p)) n)
    (postStateFn : State (F p) → State (F p)) :
    List (State (F p) × State (F p)) :=
  inputs.toList.filterMap fun input =>
    if input.enabled = 1 then
      some (input.preState, postStateFn input.preState)
    else
      none

/-- Extract the post state from a LoadState instruction when enabled.

For LOAD_STATE, the post state is `{ pc := v1, ap := v2, fp := v3 }` where v1, v2, v3
are read from memory based on the instruction's addressing modes. This requires
access to the program (to fetch/decode the instruction) and memory (to read values).

We use `femtoCairoMachineTransition` to compute the actual post state, returning
a default if the transition fails (which shouldn't happen for valid enabled instructions).
-/
def loadStatePostState
    {programSize : ℕ} [NeZero programSize] (program : Fin programSize → F p)
    {memorySize : ℕ} [NeZero memorySize] (memory : Fin memorySize → F p)
    (preState : State (F p)) : State (F p) :=
  match femtoCairoMachineTransition program memory preState with
  | some postState => postState
  | none => preState  -- fallback, shouldn't happen for valid enabled instructions

/-! ## Helper lemmas: Spec implies transition to specific postState -/

omit p_large_enough in
/-- ADD instruction spec implies transition to addPostState -/
theorem AddInstruction_Spec_transition_postState
    {programSize : ℕ} [NeZero programSize] (program : Fin programSize → F p)
    {memorySize : ℕ} [NeZero memorySize] (memory : Fin memorySize → F p)
    (input : InstructionStepInput (F p)) (adds : InteractionDelta (F p))
    (h_spec : AddInstruction.Spec program memory input adds)
    (h_enabled : input.enabled = 1) :
    femtoCairoMachineTransition program memory input.preState = some (addPostState input.preState) := by
  simp only [AddInstruction.Spec, h_enabled, ite_true] at h_spec
  split at h_spec
  case h_2 => exact h_spec.elim
  case h_1 rawInstr h_fetch =>
    split at h_spec
    case h_2 => exact h_spec.elim
    case h_1 instrType mode1 mode2 mode3 h_decode =>
      split at h_spec
      case isTrue h_add =>
        split at h_spec
        case h_1 v1 v2 v3 h_mem1 h_mem2 h_mem3 =>
          simp only [femtoCairoMachineTransition, h_fetch, h_decode, h_mem1, h_mem2, h_mem3,
            computeNextState, h_add, h_spec.1, ite_true, Option.bind_eq_bind, Option.bind_some, addPostState]
        all_goals exact h_spec.elim
      case isFalse => exact h_spec.elim

omit p_large_enough in
/-- MUL instruction spec implies transition to mulPostState -/
theorem MulInstruction_Spec_transition_postState
    {programSize : ℕ} [NeZero programSize] (program : Fin programSize → F p)
    {memorySize : ℕ} [NeZero memorySize] (memory : Fin memorySize → F p)
    (input : InstructionStepInput (F p)) (adds : InteractionDelta (F p))
    (h_spec : MulInstruction.Spec program memory input adds)
    (h_enabled : input.enabled = 1) :
    femtoCairoMachineTransition program memory input.preState = some (mulPostState input.preState) := by
  simp only [MulInstruction.Spec, h_enabled, ite_true] at h_spec
  split at h_spec
  case h_2 => exact h_spec.elim
  case h_1 rawInstr h_fetch =>
    split at h_spec
    case h_2 => exact h_spec.elim
    case h_1 instrType mode1 mode2 mode3 h_decode =>
      split at h_spec
      case isTrue h_mul =>
        split at h_spec
        case h_1 v1 v2 v3 h_mem1 h_mem2 h_mem3 =>
          simp only [femtoCairoMachineTransition, h_fetch, h_decode, h_mem1, h_mem2, h_mem3,
            computeNextState, h_mul, h_spec.1, ite_true, Option.bind_eq_bind, Option.bind_some, mulPostState]
        all_goals exact h_spec.elim
      case isFalse => exact h_spec.elim

omit p_large_enough in
/-- StoreState instruction spec implies transition to storeStatePostState -/
theorem StoreStateInstruction_Spec_transition_postState
    {programSize : ℕ} [NeZero programSize] (program : Fin programSize → F p)
    {memorySize : ℕ} [NeZero memorySize] (memory : Fin memorySize → F p)
    (input : InstructionStepInput (F p)) (adds : InteractionDelta (F p))
    (h_spec : StoreStateInstruction.Spec program memory input adds)
    (h_enabled : input.enabled = 1) :
    femtoCairoMachineTransition program memory input.preState = some (storeStatePostState input.preState) := by
  simp only [StoreStateInstruction.Spec, h_enabled, ite_true] at h_spec
  split at h_spec
  case h_2 => exact h_spec.elim
  case h_1 rawInstr h_fetch =>
    split at h_spec
    case h_2 => exact h_spec.elim
    case h_1 instrType mode1 mode2 mode3 h_decode =>
      split at h_spec
      case isTrue h_store =>
        split at h_spec
        case h_1 v1 v2 v3 h_mem1 h_mem2 h_mem3 =>
          obtain ⟨h_v1_pc, h_v2_ap, h_v3_fp, _⟩ := h_spec
          simp only [femtoCairoMachineTransition, h_fetch, h_decode, h_mem1, h_mem2, h_mem3,
            computeNextState, h_store, h_v1_pc, h_v2_ap, h_v3_fp, and_self, ite_true,
            Option.bind_eq_bind, Option.bind_some, storeStatePostState]
        all_goals exact h_spec.elim
      case isFalse => exact h_spec.elim

omit p_large_enough in
/-- LoadState instruction spec implies transition to loadStatePostState -/
theorem LoadStateInstruction_Spec_transition_postState
    {programSize : ℕ} [NeZero programSize] (program : Fin programSize → F p)
    {memorySize : ℕ} [NeZero memorySize] (memory : Fin memorySize → F p)
    (input : InstructionStepInput (F p)) (adds : InteractionDelta (F p))
    (h_spec : LoadStateInstruction.Spec program memory input adds)
    (h_enabled : input.enabled = 1) :
    femtoCairoMachineTransition program memory input.preState = some (loadStatePostState program memory input.preState) := by
  simp only [LoadStateInstruction.Spec, h_enabled, ite_true] at h_spec
  split at h_spec
  case h_2 => exact h_spec.elim
  case h_1 rawInstr h_fetch =>
    split at h_spec
    case h_2 => exact h_spec.elim
    case h_1 instrType mode1 mode2 mode3 h_decode =>
      split at h_spec
      case isTrue h_load =>
        split at h_spec
        case h_1 v1 v2 v3 h_mem1 h_mem2 h_mem3 =>
          simp only [femtoCairoMachineTransition, h_fetch, h_decode, h_mem1, h_mem2, h_mem3,
            computeNextState, h_load, Option.bind_eq_bind, Option.bind_some, loadStatePostState]
        all_goals exact h_spec.elim
      case isFalse => exact h_spec.elim

/-! ## Building the Run from instruction inputs -/

/-- The edge contribution of a single instruction: 1 if enabled and matches the transition, 0 otherwise -/
def instructionEdgeContribution
    (input : InstructionStepInput (F p))
    (postStateFn : State (F p) → State (F p))
    (t : State (F p) × State (F p)) : ℕ :=
  if input.enabled = 1 ∧ t.1 = input.preState ∧ t.2 = postStateFn input.preState
  then 1 else 0

/-- Count edges from a vector of instructions for a specific transition -/
def bundleEdgeCount {n : ℕ}
    (inputs : Vector (InstructionStepInput (F p)) n)
    (postStateFn : State (F p) → State (F p))
    (t : State (F p) × State (F p)) : ℕ :=
  (inputs.toList.map (fun i => instructionEdgeContribution i postStateFn t)).sum

/-- Build Run directly from all instruction inputs across all bundles -/
def buildRunFromInputs
    {programSize : ℕ} [NeZero programSize] (program : Fin programSize → F p)
    {memorySize : ℕ} [NeZero memorySize] (memory : Fin memorySize → F p)
    {addCap mulCap storeCap loadCap : ℕ}
    (addInputs : Vector (InstructionStepInput (F p)) addCap)
    (mulInputs : Vector (InstructionStepInput (F p)) mulCap)
    (storeInputs : Vector (InstructionStepInput (F p)) storeCap)
    (loadInputs : Vector (InstructionStepInput (F p)) loadCap) :
    Utils.StateTransition.Run (State (F p)) :=
  fun t =>
    bundleEdgeCount addInputs addPostState t +
    bundleEdgeCount mulInputs mulPostState t +
    bundleEdgeCount storeInputs storeStatePostState t +
    bundleEdgeCount loadInputs (loadStatePostState program memory) t

/-- Alternative: count edges directly using filter -/
def buildRunFromInputs'
    {programSize : ℕ} [NeZero programSize] (program : Fin programSize → F p)
    {memorySize : ℕ} [NeZero memorySize] (memory : Fin memorySize → F p)
    {addCap mulCap storeCap loadCap : ℕ}
    (addInputs : Vector (InstructionStepInput (F p)) addCap)
    (mulInputs : Vector (InstructionStepInput (F p)) mulCap)
    (storeInputs : Vector (InstructionStepInput (F p)) storeCap)
    (loadInputs : Vector (InstructionStepInput (F p)) loadCap) :
    Utils.StateTransition.Run (State (F p)) :=
  fun (s1, s2) =>
    (addInputs.toList.filter (fun i => i.enabled = 1 ∧ i.preState = s1 ∧ addPostState i.preState = s2)).length +
    (mulInputs.toList.filter (fun i => i.enabled = 1 ∧ i.preState = s1 ∧ mulPostState i.preState = s2)).length +
    (storeInputs.toList.filter (fun i => i.enabled = 1 ∧ i.preState = s1 ∧ storeStatePostState i.preState = s2)).length +
    (loadInputs.toList.filter (fun i => i.enabled = 1 ∧ i.preState = s1 ∧ (loadStatePostState program memory) i.preState = s2)).length

/-! ## Key theorem connecting balanced InteractionDelta to Run.netFlow -/

/-
The key theorem we need to prove:

When `adds.toFinsupp = 0` (balanced in field arithmetic), the Run built from
enabled instructions has the expected netFlow properties:
- netFlow(initialState) = 1 (source)
- netFlow(finalState) = -1 (sink)
- netFlow(x) = 0 for all other states

This connects the field-element multiplicities in InteractionDelta to the
integer netFlow in the Run.

Key insight: Each enabled instruction contributes one edge (preState → postState).
In InteractionDelta terms: preState gets -1, postState gets +1.
In Run.netFlow terms: outflow from preState += 1, inflow to postState += 1.

The mapping is:
- Run edge (s1, s2) with count n ↔ InteractionDelta has s1 with -n, s2 with +n
- Initial state emission: +1 in InteractionDelta ↔ +1 to netFlow (no edge, pure source)
- Final state emission: -1 in InteractionDelta ↔ -1 to netFlow (no edge, pure sink)

The balanced condition adds.toFinsupp = 0 means:
  For each state s, sum of multiplicities = 0 in F

This translates to (when multiplicities are small enough to avoid wraparound):
  For each state s, (outflow from s) - (inflow to s) + (emission at s) = 0

Which gives us the netFlow properties.
-/

/-! ## Helper definitions for netFlow proof -/

/-- Count how many enabled inputs have preState = s -/
def countOutgoing {n : ℕ} (inputs : Vector (InstructionStepInput (F p)) n)
    (s : State (F p)) : ℕ :=
  (inputs.toList.filter (fun i => i.enabled = 1 ∧ i.preState = s)).length

/-- Count how many enabled inputs have postState = s -/
def countIncoming {n : ℕ} (inputs : Vector (InstructionStepInput (F p)) n)
    (postStateFn : State (F p) → State (F p)) (s : State (F p)) : ℕ :=
  (inputs.toList.filter (fun i => i.enabled = 1 ∧ postStateFn i.preState = s)).length

/-- The total outgoing edge count for state s in the Run -/
def totalOutgoing
    {addCap mulCap storeCap loadCap : ℕ}
    (addInputs : Vector (InstructionStepInput (F p)) addCap)
    (mulInputs : Vector (InstructionStepInput (F p)) mulCap)
    (storeInputs : Vector (InstructionStepInput (F p)) storeCap)
    (loadInputs : Vector (InstructionStepInput (F p)) loadCap)
    (s : State (F p)) : ℕ :=
  countOutgoing addInputs s +
  countOutgoing mulInputs s +
  countOutgoing storeInputs s +
  countOutgoing loadInputs s

/-- The total incoming edge count for state s in the Run -/
def totalIncoming
    {programSize : ℕ} [NeZero programSize] (program : Fin programSize → F p)
    {memorySize : ℕ} [NeZero memorySize] (memory : Fin memorySize → F p)
    {addCap mulCap storeCap loadCap : ℕ}
    (addInputs : Vector (InstructionStepInput (F p)) addCap)
    (mulInputs : Vector (InstructionStepInput (F p)) mulCap)
    (storeInputs : Vector (InstructionStepInput (F p)) storeCap)
    (loadInputs : Vector (InstructionStepInput (F p)) loadCap)
    (s : State (F p)) : ℕ :=
  countIncoming addInputs addPostState s +
  countIncoming mulInputs mulPostState s +
  countIncoming storeInputs storeStatePostState s +
  countIncoming loadInputs (loadStatePostState program memory) s

/-- For a single instruction, sum over all targets equals 1 if enabled and preState=s, else 0 -/
lemma sum_instructionEdgeContribution_over_targets
    (input : InstructionStepInput (F p))
    (postStateFn : State (F p) → State (F p))
    (s : State (F p)) :
    ∑ t : State (F p), instructionEdgeContribution input postStateFn (s, t) =
    if input.enabled = 1 ∧ input.preState = s then 1 else 0 := by
  simp only [instructionEdgeContribution]
  -- When enabled ∧ preState = s, there is exactly one t where the condition holds
  -- namely t = postStateFn input.preState = postStateFn s
  by_cases h : input.enabled = 1 ∧ input.preState = s
  · -- Case: enabled and preState = s
    simp only [h, and_true, if_true]
    -- The sum has exactly one non-zero term at t = postStateFn s
    rw [Finset.sum_eq_single (postStateFn s)]
    · -- At t = postStateFn s, the term is 1
      simp only [and_self, ↓reduceIte]
    · -- For other t ≠ postStateFn s, the term is 0
      intro t _ h_ne
      simp only [true_and, if_neg h_ne]
    · -- postStateFn s is in Finset.univ
      intro h_not_mem
      exact absurd (Finset.mem_univ _) h_not_mem
  · -- Case: not (enabled and preState = s)
    simp only [h, ↓reduceIte]
    -- Every term is 0
    apply Finset.sum_eq_zero
    intro t _
    push_neg at h
    by_cases he : input.enabled = 1
    · -- enabled but preState ≠ s
      have h_ne := h he
      simp only [he, true_and]
      simp only [show ¬(s = input.preState ∧ t = postStateFn input.preState) by
        intro ⟨h1, _⟩; exact h_ne h1.symm, ↓reduceIte]
    · -- not enabled
      simp only [he, false_and, ↓reduceIte]

/-- Helper: Finset.sum over list.map.sum equals list.map of Finset.sum -/
lemma sum_list_map_sum_eq_list_map_sum {α β : Type*} [Fintype α] [AddCommMonoid β]
    (L : List (InstructionStepInput (F p))) (f : InstructionStepInput (F p) → α → β) :
    ∑ t : α, (L.map (fun i => f i t)).sum = (L.map (fun i => ∑ t : α, f i t)).sum := by
  induction L with
  | nil => simp
  | cons head tail ih => simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib, ih]

/-- Helper lemma: sum over all target states equals total outgoing from source -/
lemma sum_bundleEdgeCount_eq_countOutgoing {n : ℕ}
    (inputs : Vector (InstructionStepInput (F p)) n)
    (postStateFn : State (F p) → State (F p))
    (s : State (F p)) :
    ∑ t : State (F p), bundleEdgeCount inputs postStateFn (s, t) =
    countOutgoing inputs s := by
  simp only [bundleEdgeCount, countOutgoing]
  rw [sum_list_map_sum_eq_list_map_sum]
  simp_rw [sum_instructionEdgeContribution_over_targets]
  rw [← List.countP_eq_length_filter]
  -- Convert sum of ite 1 0 to countP
  induction inputs.toList with
  | nil => simp
  | cons head tail ih =>
    simp only [List.map_cons, List.sum_cons, List.countP_cons, ih]
    by_cases h : head.enabled = 1 ∧ head.preState = s <;> simp [h, add_comm]

/-- For a single instruction, sum over all sources equals 1 if enabled and postStateFn preState=s, else 0 -/
lemma sum_instructionEdgeContribution_over_sources
    (input : InstructionStepInput (F p))
    (postStateFn : State (F p) → State (F p))
    (s : State (F p)) :
    ∑ t : State (F p), instructionEdgeContribution input postStateFn (t, s) =
    if input.enabled = 1 ∧ postStateFn input.preState = s then 1 else 0 := by
  simp only [instructionEdgeContribution]
  by_cases h : input.enabled = 1 ∧ postStateFn input.preState = s
  · -- Case: enabled and postStateFn preState = s
    simp only [h, and_true, if_true]
    -- The sum has exactly one non-zero term at t = input.preState
    rw [Finset.sum_eq_single input.preState]
    · -- At t = preState, the term is 1
      simp only [and_true, ↓reduceIte]
    · -- For other t ≠ preState, the term is 0
      intro t _ h_ne
      simp only [true_and, if_neg h_ne]
    · -- preState is in Finset.univ
      intro h_not_mem
      exact absurd (Finset.mem_univ _) h_not_mem
  · -- Case: not (enabled and postStateFn preState = s)
    simp only [h, ↓reduceIte]
    -- Every term is 0
    apply Finset.sum_eq_zero
    intro t _
    push_neg at h
    by_cases he : input.enabled = 1
    · -- enabled but postStateFn preState ≠ s
      have h_ne := h he
      simp only [he, true_and]
      by_cases hps : t = input.preState ∧ s = postStateFn input.preState
      · exact absurd hps.2.symm h_ne
      · simp only [hps, ↓reduceIte]
    · -- not enabled
      simp only [he, false_and, ↓reduceIte]

/-- Helper lemma: sum over all source states equals total incoming to target -/
lemma sum_bundleEdgeCount_eq_countIncoming {n : ℕ}
    (inputs : Vector (InstructionStepInput (F p)) n)
    (postStateFn : State (F p) → State (F p))
    (s : State (F p)) :
    ∑ t : State (F p), bundleEdgeCount inputs postStateFn (t, s) =
    countIncoming inputs postStateFn s := by
  simp only [bundleEdgeCount, countIncoming]
  rw [sum_list_map_sum_eq_list_map_sum]
  simp_rw [sum_instructionEdgeContribution_over_sources]
  rw [← List.countP_eq_length_filter]
  -- Convert sum of ite 1 0 to countP
  induction inputs.toList with
  | nil => simp
  | cons head tail ih =>
    simp only [List.map_cons, List.sum_cons, List.countP_cons, ih]
    by_cases h : head.enabled = 1 ∧ postStateFn head.preState = s <;> simp [h, add_comm]

/-! ## Field-integer lifting lemmas -/

/-- If two natural numbers have equal field representations and are small, they are equal -/
lemma nat_eq_of_field_eq (a b : ℕ) (h_small_a : a < p) (h_small_b : b < p)
    (h_eq : (a : F p) = (b : F p)) : a = b := by
  have ha : ZMod.val (a : F p) = a := ZMod.val_natCast_of_lt h_small_a
  have hb : ZMod.val (b : F p) = b := ZMod.val_natCast_of_lt h_small_b
  rw [h_eq] at ha
  omega

/-- Field subtraction equals integer subtraction when values are small -/
lemma field_sub_eq_int_sub (a b : ℕ) (h_small : a + b < p) :
    (↑a - ↑b : F p) = ((a : ℤ) - (b : ℤ) : F p) := by
  simp only [Int.cast_natCast]

/-- When a - b = 0 in field and values are small, a = b as naturals -/
lemma nat_eq_of_field_sub_eq_zero (a b : ℕ) (h_small : a + b < p)
    (h_eq : (↑a - ↑b : F p) = 0) : a = b := by
  have h_field : (↑a : F p) = (↑b : F p) := by
    have := sub_eq_zero.mp h_eq
    exact this
  exact nat_eq_of_field_eq a b (by omega) (by omega) h_field

/-- When a - b = 1 in field and values are small, a = b + 1 -/
lemma nat_succ_of_field_sub_eq_one (a b : ℕ) (h_small : a + b + 1 < p)
    (h_eq : (↑a - ↑b : F p) = 1) : a = b + 1 := by
  have h1 : (↑(b + 1) : F p) = ↑b + 1 := by simp
  have h_field : (↑a : F p) = (↑(b + 1) : F p) := by
    have := sub_eq_iff_eq_add.mp h_eq
    rw [h1, add_comm]
    exact this
  have h_small_a : a < p := by omega
  have h_small_b1 : b + 1 < p := by omega
  exact nat_eq_of_field_eq a (b + 1) h_small_a h_small_b1 h_field

/-- When b - a = 1 in field and values are small, b = a + 1 -/
lemma nat_succ_of_field_sub_eq_one' (a b : ℕ) (h_small : a + b + 1 < p)
    (h_eq : (↑b - ↑a : F p) = 1) : b = a + 1 := by
  have h_small' : b + a + 1 < p := by omega
  exact nat_succ_of_field_sub_eq_one b a h_small' h_eq

/-- Lift field equation a - b = 1 to integer equation (a : ℤ) - b = 1 -/
lemma int_sub_eq_one_of_field_sub_eq_one (a b : ℕ) (h_small : a + b + 1 < p)
    (h_eq : (↑a - ↑b : F p) = 1) : (a : ℤ) - (b : ℤ) = 1 := by
  have h_nat := nat_succ_of_field_sub_eq_one a b h_small h_eq
  omega

/-- In a field, a - b = -1 implies b - a = 1 -/
lemma field_sub_eq_neg_one_implies_swap_eq_one {F : Type*} [Field F]
    (a b : F) (h : a - b = -1) : b - a = 1 := by
  have h1 : a - b + 1 = 0 := by simp [h]
  calc b - a = -(a - b) := by ring
    _ = -(a - b) + ((a - b) + 1) := by rw [h1]; ring
    _ = 1 := by ring

/-- Lift field equation a - b = -1 to integer equation (a : ℤ) - b = -1 -/
lemma int_sub_eq_neg_one_of_field_sub_eq_neg_one (a b : ℕ) (h_small : a + b + 1 < p)
    (h_eq : (↑a - ↑b : F p) = -1) : (a : ℤ) - (b : ℤ) = -1 := by
  have h_eq' : (↑b - ↑a : F p) = 1 := field_sub_eq_neg_one_implies_swap_eq_one _ _ h_eq
  have h_nat := nat_succ_of_field_sub_eq_one b a (by omega) h_eq'
  omega

/-- Lift field equation a - b = 0 to integer equation (a : ℤ) - b = 0 -/
lemma int_sub_eq_zero_of_field_sub_eq_zero (a b : ℕ) (h_small : a + b < p)
    (h_eq : (↑a - ↑b : F p) = 0) : (a : ℤ) - (b : ℤ) = 0 := by
  have h_nat := nat_eq_of_field_sub_eq_zero a b h_small h_eq
  omega

/-- Total capacity bound for all instruction bundles -/
def totalCapacity (capacities : InstructionCapacities) : ℕ :=
  capacities.addCapacity + capacities.mulCapacity +
  capacities.storeStateCapacity + capacities.loadStateCapacity

/-! ## Key structural lemma: multiplicity equals emission + flow -/

/-- Fold raw NamedList back to stateToNamedList. -/
lemma stateToNamedList_eq (s : State (F p)) :
    (⟨"state", [s.pc, s.ap, s.fp]⟩ : NamedList (F p)) = stateToNamedList s := rfl

/-- Helper: If two states are different, their NamedList representations are different. -/
lemma stateToNamedList_ne_of_ne {s1 s2 : State (F p)} (h : s1 ≠ s2) :
    stateToNamedList s1 ≠ stateToNamedList s2 := fun heq => h (stateToNamedList_injective heq)

/-- Helper: Finsupp.single at a different state evaluates to zero. -/
lemma finsupp_single_ne_state {s1 s2 : State (F p)} {v : F p} (h : s1 ≠ s2) :
    Finsupp.single (stateToNamedList s1) v (stateToNamedList s2) = 0 :=
  Finsupp.single_eq_of_ne (stateToNamedList_ne_of_ne h).symm

/--
For a single instruction with spec, its contribution to multiplicity at state s is:
- -1 if enabled and preState = s
- +1 if enabled and postState = s
- 0 otherwise
-/
lemma single_instruction_multiplicity_contribution
    {programSize : ℕ} [NeZero programSize] (program : Fin programSize → F p)
    {memorySize : ℕ} [NeZero memorySize] (memory : Fin memorySize → F p)
    (input : InstructionStepInput (F p))
    (adds : InteractionDelta (F p))
    (postStateFn : State (F p) → State (F p))
    (h_spec : adds = if input.enabled = 1 then
                       InteractionDelta.single (stateToNamedList input.preState) (-1) +
                       InteractionDelta.single (stateToNamedList (postStateFn input.preState)) 1
                     else 0)
    (s : State (F p)) :
    adds.toFinsupp (stateToNamedList s) =
      (if input.enabled = 1 ∧ postStateFn input.preState = s then 1 else 0) -
      (if input.enabled = 1 ∧ input.preState = s then 1 else 0) := by
  rw [h_spec]
  by_cases h_enabled : input.enabled = 1
  · simp only [h_enabled, ↓reduceIte, InteractionDelta.toFinsupp_add, Finsupp.add_apply,
        InteractionDelta.toFinsupp_single]
    by_cases h_pre : input.preState = s
    · subst h_pre; by_cases h_post : postStateFn input.preState = input.preState
      · simp only [h_post, Finsupp.single_eq_same]; ring
      · simp [h_post, Finsupp.single_eq_same, finsupp_single_ne_state h_post]
    · by_cases h_post : postStateFn input.preState = s
      · simp [h_post, h_pre, Finsupp.single_eq_same, finsupp_single_ne_state h_pre]
      · simp [h_pre, h_post, finsupp_single_ne_state h_post, finsupp_single_ne_state h_pre]
  · simp only [h_enabled, ↓reduceIte, false_and, InteractionDelta.toFinsupp_zero,
      Finsupp.zero_apply, sub_zero]

/--
Helper: Sum of ite 1 0 over a list equals countP.
-/
lemma list_sum_ite_eq_countP {α : Type*} (l : List α) (p : α → Prop) [DecidablePred p]
    {F : Type*} [Semiring F] :
    (l.map (fun x => if p x then (1 : F) else 0)).sum = ↑(l.countP (fun x => decide (p x))) := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.map_cons, List.sum_cons, List.countP_cons, ih]
    by_cases hp : p hd
    · simp [hp, add_comm]
    · simp [hp]

/-- Mapping a function over finRange with indexed access equals mapping over toList -/
lemma finRange_map_getElem_eq_toList_map {α β : Type*} {n : ℕ} (v : Vector α n) (f : α → β) :
    (List.finRange n).map (fun i => f v[i]) = v.toList.map f := by
  apply List.ext_getElem
  · simp only [List.length_map, List.length_finRange, Vector.length_toList]
  · intro k h1 h2
    simp only [List.getElem_map, List.getElem_finRange, Vector.getElem_toList]
    rfl

/--
Helper: Sum of ite 1 0 over finRange equals countP over vector's toList.
-/
lemma sum_ite_eq_countP {α : Type*} {n : ℕ} (v : Vector α n) (p : α → Prop) [DecidablePred p]
    {F : Type*} [Semiring F] :
    ((List.finRange n).map (fun i => if p v[i] then (1 : F) else 0)).sum =
      ↑(v.toList.countP (fun x => decide (p x))) := by
  rw [finRange_map_getElem_eq_toList_map v (fun x => if p x then (1 : F) else 0)]
  exact list_sum_ite_eq_countP v.toList p

/--
Helper: foldl add over finRange for InteractionDelta equals list sum of map.
-/
lemma foldl_add_eq_map_sum {n : ℕ} (f : Fin n → InteractionDelta (F p)) :
    (List.finRange n).foldl (fun acc i => acc + f i) 0 =
    ((List.finRange n).map f).sum := by
  -- LHS folds over finRange applying f, RHS is sum of map f
  -- Use List.foldl_map to relate them
  have h : (List.finRange n).foldl (fun acc i => acc + f i) 0 =
           ((List.finRange n).map f).foldl (fun acc x => acc + x) 0 := by
    rw [List.foldl_map]
  rw [h]
  -- Now use List.sum_eq_foldl
  rw [← List.sum_eq_foldl]

/--
Helper: toFinsupp of list sum equals sum of map toFinsupp.
-/
lemma toFinsupp_list_sum (l : List (InteractionDelta (F p))) :
    l.sum.toFinsupp = (l.map InteractionDelta.toFinsupp).sum := by
  induction l with
  | nil => simp only [List.sum_nil, InteractionDelta.toFinsupp_zero, List.map_nil]
  | cons hd tl ih =>
    simp only [List.sum_cons, InteractionDelta.toFinsupp_add, List.map_cons, ih]

/--
Helper: toFinsupp distributes over foldl addition.
-/
lemma toFinsupp_foldl_add {n : ℕ} (f : Fin n → InteractionDelta (F p)) :
    ((List.finRange n).foldl (fun acc i => acc + f i) 0).toFinsupp = ∑ i : Fin n, (f i).toFinsupp := by
  rw [foldl_add_eq_map_sum, toFinsupp_list_sum]
  -- LHS: ((finRange n).map f).map toFinsupp).sum : Finsupp
  -- RHS: ∑ i : Fin n, (f i).toFinsupp
  rw [List.map_map]
  -- Now: ((finRange n).map (toFinsupp ∘ f)).sum = ∑ i : Fin n, (f i).toFinsupp
  rw [Fin.sum_univ_def]
  -- RHS becomes: ((finRange n).map (fun i => (f i).toFinsupp)).sum
  rfl

/--
For a bundle of instructions satisfying Bundle.Spec, the total multiplicity contribution
at state s equals countIncoming - countOutgoing.
-/
lemma bundle_multiplicity_contribution
    {n : ℕ}
    {programSize : ℕ} [NeZero programSize] (program : Fin programSize → F p)
    {memorySize : ℕ} [NeZero memorySize] (memory : Fin memorySize → F p)
    (inputs : Vector (InstructionStepInput (F p)) n)
    (adds : InteractionDelta (F p))
    (postStateFn : State (F p) → State (F p))
    (h_adds : adds.toFinsupp = ∑ i : Fin n,
        (if inputs[i].enabled = 1 then
           InteractionDelta.single (stateToNamedList inputs[i].preState) (-1) +
           InteractionDelta.single (stateToNamedList (postStateFn inputs[i].preState)) 1
         else 0).toFinsupp)
    (s : State (F p)) :
    adds.toFinsupp (stateToNamedList s) =
      (↑(countIncoming inputs postStateFn s) : F p) - ↑(countOutgoing inputs s) := by
  rw [h_adds]
  simp only [Finsupp.finset_sum_apply]
  -- Each instruction's contribution
  have h_each : ∀ i : Fin n,
      (if inputs[i].enabled = 1 then
         InteractionDelta.single (stateToNamedList inputs[i].preState) (-1) +
         InteractionDelta.single (stateToNamedList (postStateFn inputs[i].preState)) 1
       else 0).toFinsupp (stateToNamedList s) =
      (if inputs[i].enabled = 1 ∧ postStateFn inputs[i].preState = s then 1 else 0) -
      (if inputs[i].enabled = 1 ∧ inputs[i].preState = s then 1 else 0) := by
    intro i
    exact single_instruction_multiplicity_contribution program memory inputs[i] _ postStateFn rfl s
  simp_rw [h_each]
  -- Now we have: ∑ i, (incoming_i - outgoing_i) = countIncoming - countOutgoing
  -- Rewrite as: (∑ i, incoming_i) - (∑ i, outgoing_i)
  rw [Finset.sum_sub_distrib]
  -- Now we need: ∑ i, (if enabled ∧ post=s then 1 else 0) = countIncoming
  --          and: ∑ i, (if enabled ∧ pre=s then 1 else 0) = countOutgoing
  -- We use that ∑ of ite 1 0 = countP and countP = filter.length
  simp only [countIncoming, countOutgoing]
  rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
  -- Convert sum to list operations
  -- Use Fin.sum_univ_def: ∑ i, f i = (List.finRange n).map f).sum
  rw [Fin.sum_univ_def, Fin.sum_univ_def]
  -- Relate finRange to toList via getElem
  congr 1
  · -- (List.finRange n).map (λ i => if enabled ∧ post=s then 1 else 0)).sum = countP
    exact sum_ite_eq_countP inputs (fun i => i.enabled = 1 ∧ postStateFn i.preState = s)
  · -- Similar for outgoing
    exact sum_ite_eq_countP inputs (fun i => i.enabled = 1 ∧ i.preState = s)

/-! ## Spec_toFinsupp_ite lemmas

For each instruction type, we prove that the Spec implies the toFinsupp has the ite form.
This bridges between the Spec (which uses equality or zero) and the sum form needed
for bundle_multiplicity_contribution.
-/

/--
For AddInstruction.Spec, the toFinsupp equals the expected ite form.
When enabled: single(pre,-1) + single(post,+1)
When disabled: 0
-/
lemma AddInstruction_Spec_toFinsupp_ite
    {programSize : ℕ} [NeZero programSize] (program : Fin programSize → F p)
    {memorySize : ℕ} [NeZero memorySize] (memory : Fin memorySize → F p)
    (input : InstructionStepInput (F p))
    (adds : InteractionDelta (F p))
    (h_spec : AddInstruction.Spec program memory input adds) :
    adds.toFinsupp = (if input.enabled = 1 then
                        InteractionDelta.single (stateToNamedList input.preState) (-1) +
                        InteractionDelta.single (stateToNamedList (addPostState input.preState)) 1
                      else 0).toFinsupp := by
  by_cases h_enabled : input.enabled = 1
  · -- Case: enabled = 1
    simp only [h_enabled, ↓reduceIte]
    -- From h_spec, when enabled, we get adds = single(...) + single(...)
    simp only [AddInstruction.Spec, h_enabled, ite_true] at h_spec
    -- Navigate through the nested match statements
    split at h_spec
    case h_2 => exact h_spec.elim
    case h_1 rawInstr h_fetch =>
      split at h_spec
      case h_2 => exact h_spec.elim
      case h_1 instrType mode1 mode2 mode3 h_decode =>
        split at h_spec
        case isTrue h_add =>
          split at h_spec
          case h_1 v1 v2 v3 h_mem1 h_mem2 h_mem3 =>
            obtain ⟨_, h_adds_eq⟩ := h_spec
            -- h_adds_eq : adds = single(pre,-1) + single(post,+1)
            rw [h_adds_eq]
            simp only [stateToNamedList, addPostState]
          all_goals exact h_spec.elim
        case isFalse => exact h_spec.elim
  · -- Case: enabled ≠ 1
    simp only [h_enabled, ↓reduceIte, InteractionDelta.toFinsupp_zero]
    -- From h_spec, when not enabled, adds.toFinsupp = 0
    simp only [AddInstruction.Spec, h_enabled, ite_false] at h_spec
    exact h_spec

/--
For MulInstruction.Spec, the toFinsupp equals the expected ite form.
-/
lemma MulInstruction_Spec_toFinsupp_ite
    {programSize : ℕ} [NeZero programSize] (program : Fin programSize → F p)
    {memorySize : ℕ} [NeZero memorySize] (memory : Fin memorySize → F p)
    (input : InstructionStepInput (F p))
    (adds : InteractionDelta (F p))
    (h_spec : MulInstruction.Spec program memory input adds) :
    adds.toFinsupp = (if input.enabled = 1 then
                        InteractionDelta.single (stateToNamedList input.preState) (-1) +
                        InteractionDelta.single (stateToNamedList (mulPostState input.preState)) 1
                      else 0).toFinsupp := by
  by_cases h_enabled : input.enabled = 1
  · simp only [h_enabled, ↓reduceIte]
    simp only [MulInstruction.Spec, h_enabled, ite_true] at h_spec
    split at h_spec
    case h_2 => exact h_spec.elim
    case h_1 rawInstr h_fetch =>
      split at h_spec
      case h_2 => exact h_spec.elim
      case h_1 instrType mode1 mode2 mode3 h_decode =>
        split at h_spec
        case isTrue h_mul =>
          split at h_spec
          case h_1 v1 v2 v3 h_mem1 h_mem2 h_mem3 =>
            obtain ⟨_, h_adds_eq⟩ := h_spec
            rw [h_adds_eq]
            simp only [stateToNamedList, mulPostState]
          all_goals exact h_spec.elim
        case isFalse => exact h_spec.elim
  · simp only [h_enabled, ↓reduceIte, InteractionDelta.toFinsupp_zero]
    simp only [MulInstruction.Spec, h_enabled, ite_false] at h_spec
    exact h_spec

/--
For StoreStateInstruction.Spec, the toFinsupp equals the expected ite form.
-/
lemma StoreStateInstruction_Spec_toFinsupp_ite
    {programSize : ℕ} [NeZero programSize] (program : Fin programSize → F p)
    {memorySize : ℕ} [NeZero memorySize] (memory : Fin memorySize → F p)
    (input : InstructionStepInput (F p))
    (adds : InteractionDelta (F p))
    (h_spec : StoreStateInstruction.Spec program memory input adds) :
    adds.toFinsupp = (if input.enabled = 1 then
                        InteractionDelta.single (stateToNamedList input.preState) (-1) +
                        InteractionDelta.single (stateToNamedList (storeStatePostState input.preState)) 1
                      else 0).toFinsupp := by
  by_cases h_enabled : input.enabled = 1
  · simp only [h_enabled, ↓reduceIte]
    simp only [StoreStateInstruction.Spec, h_enabled, ite_true] at h_spec
    split at h_spec
    case h_2 => exact h_spec.elim
    case h_1 rawInstr h_fetch =>
      split at h_spec
      case h_2 => exact h_spec.elim
      case h_1 instrType mode1 mode2 mode3 h_decode =>
        split at h_spec
        case isTrue h_store =>
          split at h_spec
          case h_1 v1 v2 v3 h_mem1 h_mem2 h_mem3 =>
            obtain ⟨_, _, _, h_adds_eq⟩ := h_spec
            rw [h_adds_eq]
            simp only [stateToNamedList, storeStatePostState]
          all_goals exact h_spec.elim
        case isFalse => exact h_spec.elim
  · simp only [h_enabled, ↓reduceIte, InteractionDelta.toFinsupp_zero]
    simp only [StoreStateInstruction.Spec, h_enabled, ite_false] at h_spec
    exact h_spec

/--
For LoadStateInstruction.Spec, the toFinsupp equals the expected ite form.
Note: loadStatePostState uses femtoCairoMachineTransition to compute the post state,
which for LOAD_STATE reads (v1, v2, v3) from memory. When the transition fails (shouldn't
happen for valid enabled instructions), it falls back to preState.
-/
lemma LoadStateInstruction_Spec_toFinsupp_ite
    {programSize : ℕ} [NeZero programSize] (program : Fin programSize → F p)
    {memorySize : ℕ} [NeZero memorySize] (memory : Fin memorySize → F p)
    (input : InstructionStepInput (F p))
    (adds : InteractionDelta (F p))
    (h_spec : LoadStateInstruction.Spec program memory input adds) :
    adds.toFinsupp = (if input.enabled = 1 then
                        InteractionDelta.single (stateToNamedList input.preState) (-1) +
                        InteractionDelta.single (stateToNamedList (loadStatePostState program memory input.preState)) 1
                      else 0).toFinsupp := by
  by_cases h_enabled : input.enabled = 1
  · simp only [h_enabled, ↓reduceIte]
    simp only [LoadStateInstruction.Spec, h_enabled, ite_true] at h_spec
    split at h_spec
    case h_2 => exact h_spec.elim
    case h_1 rawInstr h_fetch =>
      split at h_spec
      case h_2 => exact h_spec.elim
      case h_1 instrType mode1 mode2 mode3 h_decode =>
        split at h_spec
        case isTrue h_load =>
          split at h_spec
          case h_1 v1 v2 v3 h_mem1 h_mem2 h_mem3 =>
            -- h_spec gives us the adds equation for LOAD_STATE
            rw [h_spec]
            simp only [stateToNamedList, loadStatePostState]
            -- Need to show femtoCairoMachineTransition returns the expected postState
            simp only [femtoCairoMachineTransition, h_fetch, h_decode, h_mem1, h_mem2, h_mem3,
              computeNextState, h_load, Option.bind_eq_bind, Option.bind_some]
          all_goals exact h_spec.elim
        case isFalse => exact h_spec.elim
  · simp only [h_enabled, ↓reduceIte, InteractionDelta.toFinsupp_zero]
    simp only [LoadStateInstruction.Spec, h_enabled, ite_false] at h_spec
    exact h_spec

/-! ## Bundle.Spec_toFinsupp_sum lemmas

For each instruction type, convert Bundle.Spec's foldl to the sum form needed
for bundle_multiplicity_contribution.
-/

/--
For AddInstruction.Bundle.Spec, the toFinsupp equals a sum over individual instruction contributions.
This bridges the foldl form in Bundle.Spec to the Finset.sum form.
-/
lemma AddInstruction_Bundle_Spec_toFinsupp_sum
    (capacity : ℕ) [NeZero capacity]
    {programSize : ℕ} [NeZero programSize] (program : Fin programSize → F p)
    {memorySize : ℕ} [NeZero memorySize] (memory : Fin memorySize → F p)
    (inputs : Vector (InstructionStepInput (F p)) capacity)
    (adds : InteractionDelta (F p))
    (h_spec : AddInstruction.Bundle.Spec capacity program memory inputs adds) :
    adds.toFinsupp = ∑ i : Fin capacity,
      (if inputs[i].enabled = 1 then
         InteractionDelta.single (stateToNamedList inputs[i].preState) (-1) +
         InteractionDelta.single (stateToNamedList (addPostState inputs[i].preState)) 1
       else 0).toFinsupp := by
  -- Extract stepAdds from h_spec
  obtain ⟨stepAdds, h_step_specs, h_adds_eq⟩ := h_spec
  -- Rewrite adds to foldl form
  rw [h_adds_eq]
  -- Use toFinsupp_foldl_add to convert foldl to sum
  rw [toFinsupp_foldl_add]
  -- Now show each term equals the expected form
  apply Finset.sum_congr rfl
  intro i _
  exact AddInstruction_Spec_toFinsupp_ite program memory inputs[i] (stepAdds i) (h_step_specs i)

/--
For MulInstruction.Bundle.Spec, the toFinsupp equals a sum over individual instruction contributions.
-/
lemma MulInstruction_Bundle_Spec_toFinsupp_sum
    (capacity : ℕ) [NeZero capacity]
    {programSize : ℕ} [NeZero programSize] (program : Fin programSize → F p)
    {memorySize : ℕ} [NeZero memorySize] (memory : Fin memorySize → F p)
    (inputs : Vector (InstructionStepInput (F p)) capacity)
    (adds : InteractionDelta (F p))
    (h_spec : MulInstruction.Bundle.Spec capacity program memory inputs adds) :
    adds.toFinsupp = ∑ i : Fin capacity,
      (if inputs[i].enabled = 1 then
         InteractionDelta.single (stateToNamedList inputs[i].preState) (-1) +
         InteractionDelta.single (stateToNamedList (mulPostState inputs[i].preState)) 1
       else 0).toFinsupp := by
  obtain ⟨stepAdds, h_step_specs, h_adds_eq⟩ := h_spec
  rw [h_adds_eq, toFinsupp_foldl_add]
  apply Finset.sum_congr rfl
  intro i _
  exact MulInstruction_Spec_toFinsupp_ite program memory inputs[i] (stepAdds i) (h_step_specs i)

/--
For StoreStateInstruction.Bundle.Spec, the toFinsupp equals a sum over individual instruction contributions.
-/
lemma StoreStateInstruction_Bundle_Spec_toFinsupp_sum
    (capacity : ℕ) [NeZero capacity]
    {programSize : ℕ} [NeZero programSize] (program : Fin programSize → F p)
    {memorySize : ℕ} [NeZero memorySize] (memory : Fin memorySize → F p)
    (inputs : Vector (InstructionStepInput (F p)) capacity)
    (adds : InteractionDelta (F p))
    (h_spec : StoreStateInstruction.Bundle.Spec capacity program memory inputs adds) :
    adds.toFinsupp = ∑ i : Fin capacity,
      (if inputs[i].enabled = 1 then
         InteractionDelta.single (stateToNamedList inputs[i].preState) (-1) +
         InteractionDelta.single (stateToNamedList (storeStatePostState inputs[i].preState)) 1
       else 0).toFinsupp := by
  obtain ⟨stepAdds, h_step_specs, h_adds_eq⟩ := h_spec
  rw [h_adds_eq, toFinsupp_foldl_add]
  apply Finset.sum_congr rfl
  intro i _
  exact StoreStateInstruction_Spec_toFinsupp_ite program memory inputs[i] (stepAdds i) (h_step_specs i)

/--
For LoadStateInstruction.Bundle.Spec, the toFinsupp equals a sum over individual instruction contributions.
-/
lemma LoadStateInstruction_Bundle_Spec_toFinsupp_sum
    (capacity : ℕ) [NeZero capacity]
    {programSize : ℕ} [NeZero programSize] (program : Fin programSize → F p)
    {memorySize : ℕ} [NeZero memorySize] (memory : Fin memorySize → F p)
    (inputs : Vector (InstructionStepInput (F p)) capacity)
    (adds : InteractionDelta (F p))
    (h_spec : LoadStateInstruction.Bundle.Spec capacity program memory inputs adds) :
    adds.toFinsupp = ∑ i : Fin capacity,
      (if inputs[i].enabled = 1 then
         InteractionDelta.single (stateToNamedList inputs[i].preState) (-1) +
         InteractionDelta.single (stateToNamedList (loadStatePostState program memory inputs[i].preState)) 1
       else 0).toFinsupp := by
  obtain ⟨stepAdds, h_step_specs, h_adds_eq⟩ := h_spec
  rw [h_adds_eq, toFinsupp_foldl_add]
  apply Finset.sum_congr rfl
  intro i _
  exact LoadStateInstruction_Spec_toFinsupp_ite program memory inputs[i] (stepAdds i) (h_step_specs i)

/--
For any state s, the multiplicity in adds.toFinsupp equals:
  emission(s) + incoming_edges(s) - outgoing_edges(s)

where emission(s) = 1 if s = initialState, -1 if s = finalState, 0 otherwise.

This is the central lemma connecting InteractionDelta to the Run structure.
-/
lemma multiplicity_eq_emission_plus_flow
    (capacities : InstructionCapacities)
    {programSize : ℕ} [NeZero programSize] (program : Fin programSize → F p)
    {memorySize : ℕ} [NeZero memorySize] (memory : Fin memorySize → F p)
    (inputs : ExecutionCircuitInput capacities (F p))
    (adds : InteractionDelta (F p))
    (h_spec : ExecutionBundle.Spec capacities program memory inputs adds)
    (s : State (F p)) :
    adds.toFinsupp (stateToNamedList s) =
      (if s = inputs.initialState then 1 else 0) +
      (↑(totalIncoming program memory
           inputs.bundledInputs.addInputs inputs.bundledInputs.mulInputs
           inputs.bundledInputs.storeStateInputs inputs.bundledInputs.loadStateInputs s) : F p) -
      (↑(totalOutgoing
           inputs.bundledInputs.addInputs inputs.bundledInputs.mulInputs
           inputs.bundledInputs.storeStateInputs inputs.bundledInputs.loadStateInputs s) : F p) +
      (if s = inputs.finalState then -1 else 0) := by
  -- Extract components from h_spec
  obtain ⟨addAdds, mulAdds, storeStateAdds, loadStateAdds, h_add_spec, h_mul_spec, h_store_spec, h_load_spec, h_adds_eq⟩ := h_spec

  -- Rewrite adds in terms of components
  rw [h_adds_eq]

  -- Convert to toFinsupp and evaluate at stateToNamedList s
  simp only [InteractionDelta.toFinsupp_add, Finsupp.add_apply, InteractionDelta.toFinsupp_single]

  -- The goal now has structure:
  -- single(init, 1)(s) + addAdds(s) + mulAdds(s) + storeAdds(s) + loadAdds(s) + single(final, -1)(s)
  --   = (if s=init then 1 else 0) + totalIncoming - totalOutgoing + (if s=final then -1 else 0)
  --
  -- The emission terms single(init, 1)(s) and single(final, -1)(s) directly match the if-then-else.
  -- The bundle contributions need to sum to totalIncoming - totalOutgoing.
  --
  -- To complete this proof:
  -- 1. Use toFinsupp_foldl_add to convert each bundle's foldl to Finset.sum
  -- 2. Extract from each Bundle.Spec that stepAdds[i].toFinsupp has the expected form:
  --    - When enabled: single(pre, -1) + single(post, +1)
  --    - When disabled: 0
  -- 3. Apply bundle_multiplicity_contribution to each bundle
  -- 4. Combine the four bundles' contributions to get totalIncoming - totalOutgoing
  --
  -- Key helper needed: For each instruction type's Spec, extract that when enabled,
  -- adds = single(preState, -1) + single(postStateFn preState, +1), and when disabled,
  -- adds.toFinsupp = 0.

  -- Get bundle contributions in the sum form using Bundle_Spec_toFinsupp_sum
  have h_add_sum := AddInstruction_Bundle_Spec_toFinsupp_sum capacities.addCapacity
    program memory inputs.bundledInputs.addInputs addAdds h_add_spec
  have h_mul_sum := MulInstruction_Bundle_Spec_toFinsupp_sum capacities.mulCapacity
    program memory inputs.bundledInputs.mulInputs mulAdds h_mul_spec
  have h_store_sum := StoreStateInstruction_Bundle_Spec_toFinsupp_sum capacities.storeStateCapacity
    program memory inputs.bundledInputs.storeStateInputs storeStateAdds h_store_spec
  have h_load_sum := LoadStateInstruction_Bundle_Spec_toFinsupp_sum capacities.loadStateCapacity
    program memory inputs.bundledInputs.loadStateInputs loadStateAdds h_load_spec

  -- Apply bundle_multiplicity_contribution to each bundle to get countIncoming - countOutgoing
  have h_add_contrib := bundle_multiplicity_contribution program memory
    inputs.bundledInputs.addInputs addAdds addPostState h_add_sum s
  have h_mul_contrib := bundle_multiplicity_contribution program memory
    inputs.bundledInputs.mulInputs mulAdds mulPostState h_mul_sum s
  have h_store_contrib := bundle_multiplicity_contribution program memory
    inputs.bundledInputs.storeStateInputs storeStateAdds storeStatePostState h_store_sum s
  have h_load_contrib := bundle_multiplicity_contribution program memory
    inputs.bundledInputs.loadStateInputs loadStateAdds (loadStatePostState program memory) h_load_sum s

  -- Handle the emission terms - split into 4 cases based on whether s equals initial/final state
  by_cases h_init : s = inputs.initialState
  · -- s = initialState
    by_cases h_final : s = inputs.finalState
    · -- Case 1: s = initialState AND s = finalState
      subst h_init
      simp only [stateToNamedList_eq, h_final, Finsupp.single_eq_same, ↓reduceIte] at h_add_contrib h_mul_contrib h_store_contrib h_load_contrib ⊢
      rw [h_add_contrib, h_mul_contrib, h_store_contrib, h_load_contrib]
      simp only [totalIncoming, totalOutgoing]; push_cast; ring
    · -- Case 2: s = initialState AND s ≠ finalState
      subst h_init
      have h_init_ne_final : inputs.initialState ≠ inputs.finalState := h_final
      simp only [stateToNamedList_eq, Finsupp.single_eq_same, ↓reduceIte, h_init_ne_final,
        Finsupp.single_eq_of_ne (stateToNamedList_ne_of_ne h_init_ne_final)]
      rw [h_add_contrib, h_mul_contrib, h_store_contrib, h_load_contrib]
      simp only [totalIncoming, totalOutgoing]; push_cast; ring
  · -- s ≠ initialState
    by_cases h_final : s = inputs.finalState
    · -- Case 3: s ≠ initialState AND s = finalState
      subst h_final
      have h_final_ne_init : inputs.finalState ≠ inputs.initialState := h_init
      simp only [stateToNamedList_eq, Finsupp.single_eq_same, ↓reduceIte, h_final_ne_init,
        Finsupp.single_eq_of_ne (stateToNamedList_ne_of_ne h_final_ne_init)]
      rw [h_add_contrib, h_mul_contrib, h_store_contrib, h_load_contrib]
      simp only [totalIncoming, totalOutgoing]; push_cast; ring
    · -- Case 4: s ≠ initialState AND s ≠ finalState
      simp only [stateToNamedList_eq, ↓reduceIte, h_init, h_final,
        Finsupp.single_eq_of_ne (stateToNamedList_ne_of_ne h_init),
        Finsupp.single_eq_of_ne (stateToNamedList_ne_of_ne h_final)]
      rw [h_add_contrib, h_mul_contrib, h_store_contrib, h_load_contrib]
      simp only [totalIncoming, totalOutgoing]; push_cast; ring

/--
Key consequence: when adds.toFinsupp = 0, the emission equals outgoing - incoming.
-/
lemma emission_eq_flow_diff
    (capacities : InstructionCapacities)
    {programSize : ℕ} [NeZero programSize] (program : Fin programSize → F p)
    {memorySize : ℕ} [NeZero memorySize] (memory : Fin memorySize → F p)
    (inputs : ExecutionCircuitInput capacities (F p))
    (adds : InteractionDelta (F p))
    (h_spec : ExecutionBundle.Spec capacities program memory inputs adds)
    (h_balanced : adds.toFinsupp = 0)
    (s : State (F p)) :
    let out := totalOutgoing
                 inputs.bundledInputs.addInputs inputs.bundledInputs.mulInputs
                 inputs.bundledInputs.storeStateInputs inputs.bundledInputs.loadStateInputs s
    let inc := totalIncoming program memory
                 inputs.bundledInputs.addInputs inputs.bundledInputs.mulInputs
                 inputs.bundledInputs.storeStateInputs inputs.bundledInputs.loadStateInputs s
    (↑out - ↑inc : F p) =
      (if s = inputs.initialState then 1 else 0) + (if s = inputs.finalState then -1 else 0) := by
  -- From multiplicity_eq_emission_plus_flow and h_balanced:
  --   0 = emission_init + incoming - outgoing + emission_final
  -- Rearranging: outgoing - incoming = emission_init + emission_final
  have h_mult := multiplicity_eq_emission_plus_flow capacities program memory inputs adds h_spec s
  have h_zero : adds.toFinsupp (stateToNamedList s) = 0 := by
    rw [h_balanced]
    simp only [Finsupp.coe_zero, Pi.zero_apply]
  rw [h_zero] at h_mult
  -- h_mult : 0 = emit_init + ↑inc - ↑out + emit_final
  -- Goal: ↑out - ↑inc = emit_init + emit_final
  -- This is pure algebra in a commutative ring

  -- Define local abbreviations for readability
  set init_emit : F p := if s = inputs.initialState then 1 else 0 with h_init_def
  set final_emit : F p := if s = inputs.finalState then -1 else 0 with h_final_def
  set out_field : F p := ↑(totalOutgoing inputs.bundledInputs.addInputs
      inputs.bundledInputs.mulInputs inputs.bundledInputs.storeStateInputs
      inputs.bundledInputs.loadStateInputs s) with h_out_def
  set inc_field : F p := ↑(totalIncoming program memory inputs.bundledInputs.addInputs
      inputs.bundledInputs.mulInputs inputs.bundledInputs.storeStateInputs
      inputs.bundledInputs.loadStateInputs s) with h_inc_def

  -- h_mult: 0 = init_emit + inc_field - out_field + final_emit
  have h_eq : (0 : F p) = init_emit + inc_field - out_field + final_emit := h_mult
  -- Goal: out_field - inc_field = init_emit + final_emit
  -- From 0 = a + b - c + d, derive c - b = a + d by ring manipulation
  calc out_field - inc_field
    = out_field - inc_field + 0 := by ring
  _ = out_field - inc_field + (init_emit + inc_field - out_field + final_emit) := by rw [← h_eq]
  _ = init_emit + final_emit := by ring

/-- The total number of enabled instructions is bounded by total capacity -/
lemma enabled_count_bounded
    (capacities : InstructionCapacities)
    (inputs : ExecutionCircuitInput capacities (F p)) :
    (inputs.bundledInputs.addInputs.toList.filter (·.enabled = 1)).length +
    (inputs.bundledInputs.mulInputs.toList.filter (·.enabled = 1)).length +
    (inputs.bundledInputs.storeStateInputs.toList.filter (·.enabled = 1)).length +
    (inputs.bundledInputs.loadStateInputs.toList.filter (·.enabled = 1)).length ≤
    totalCapacity capacities := by
  simp only [totalCapacity]
  have h1 : (inputs.bundledInputs.addInputs.toList.filter (·.enabled = 1)).length ≤
            inputs.bundledInputs.addInputs.toList.length :=
    List.length_filter_le _ _
  have h2 : (inputs.bundledInputs.mulInputs.toList.filter (·.enabled = 1)).length ≤
            inputs.bundledInputs.mulInputs.toList.length :=
    List.length_filter_le _ _
  have h3 : (inputs.bundledInputs.storeStateInputs.toList.filter (·.enabled = 1)).length ≤
            inputs.bundledInputs.storeStateInputs.toList.length :=
    List.length_filter_le _ _
  have h4 : (inputs.bundledInputs.loadStateInputs.toList.filter (·.enabled = 1)).length ≤
            inputs.bundledInputs.loadStateInputs.toList.length :=
    List.length_filter_le _ _
  simp only [Vector.length_toList] at h1 h2 h3 h4
  omega

/-! ## Connecting Run.netFlow to totalOutgoing/totalIncoming -/

/--
The netFlow computed from buildRunFromInputs equals totalOutgoing - totalIncoming.
This connects the Run structure to our counting functions.
-/
lemma netFlow_eq_totalOutgoing_sub_totalIncoming
    {programSize : ℕ} [NeZero programSize] (program : Fin programSize → F p)
    {memorySize : ℕ} [NeZero memorySize] (memory : Fin memorySize → F p)
    {addCap mulCap storeCap loadCap : ℕ}
    (addInputs : Vector (InstructionStepInput (F p)) addCap)
    (mulInputs : Vector (InstructionStepInput (F p)) mulCap)
    (storeInputs : Vector (InstructionStepInput (F p)) storeCap)
    (loadInputs : Vector (InstructionStepInput (F p)) loadCap)
    (s : State (F p)) :
    let R := buildRunFromInputs program memory addInputs mulInputs storeInputs loadInputs
    R.netFlow s = (totalOutgoing addInputs mulInputs storeInputs loadInputs s : ℤ) -
                  (totalIncoming program memory addInputs mulInputs storeInputs loadInputs s : ℤ) := by
  -- netFlow s = (∑ t, R(s,t)) - (∑ t, R(t,s))
  -- R is buildRunFromInputs, so R(s,t) = sum of bundleEdgeCounts for each instruction type
  simp only [Utils.StateTransition.Run.netFlow, buildRunFromInputs]
  -- Now we need: (∑ t, ↑(bundleEdgeCounts for (s,t))) - (∑ t, ↑(bundleEdgeCounts for (t,s)))
  --            = totalOutgoing - totalIncoming

  -- Distribute the sum
  simp only [Nat.cast_add]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]

  -- Use helper lemmas to simplify sums
  have h_add_out := sum_bundleEdgeCount_eq_countOutgoing addInputs addPostState s
  have h_mul_out := sum_bundleEdgeCount_eq_countOutgoing mulInputs mulPostState s
  have h_store_out := sum_bundleEdgeCount_eq_countOutgoing storeInputs storeStatePostState s
  have h_load_out := sum_bundleEdgeCount_eq_countOutgoing loadInputs (loadStatePostState program memory) s

  have h_add_in := sum_bundleEdgeCount_eq_countIncoming addInputs addPostState s
  have h_mul_in := sum_bundleEdgeCount_eq_countIncoming mulInputs mulPostState s
  have h_store_in := sum_bundleEdgeCount_eq_countIncoming storeInputs storeStatePostState s
  have h_load_in := sum_bundleEdgeCount_eq_countIncoming loadInputs (loadStatePostState program memory) s

  -- Convert sums to countOutgoing/countIncoming
  -- Don't unfold here to avoid the complex filter expressions
  -- simp only [totalOutgoing, totalIncoming, countOutgoing, countIncoming]

  -- Convert ∑ x, ↑(f x) to ↑(∑ x, f x) using Nat.cast_sum
  simp only [← Nat.cast_sum]

  -- Now use the helper lemmas
  rw [h_add_out, h_mul_out, h_store_out, h_load_out,
      h_add_in, h_mul_in, h_store_in, h_load_in]

  -- Unfold the totalOutgoing/totalIncoming definitions
  simp only [totalOutgoing, totalIncoming, Int.ofNat_add]

/-- countOutgoing is bounded by the vector length (filter length ≤ list length) -/
lemma countOutgoing_le_length {n : ℕ} (inputs : Vector (InstructionStepInput (F p)) n)
    (s : State (F p)) :
    countOutgoing inputs s ≤ n := by
  simp only [countOutgoing]
  have h1 := List.length_filter_le (fun i => decide (i.enabled = 1 ∧ i.preState = s)) inputs.toList
  simp only [Vector.length_toList] at h1
  exact h1

/-- countIncoming is bounded by the vector length (filter length ≤ list length) -/
lemma countIncoming_le_length {n : ℕ} (inputs : Vector (InstructionStepInput (F p)) n)
    (postStateFn : State (F p) → State (F p)) (s : State (F p)) :
    countIncoming inputs postStateFn s ≤ n := by
  simp only [countIncoming]
  have h1 := List.length_filter_le (fun i => decide (i.enabled = 1 ∧ postStateFn i.preState = s)) inputs.toList
  simp only [Vector.length_toList] at h1
  exact h1

/-- totalOutgoing is bounded by totalCapacity -/
lemma totalOutgoing_le_totalCapacity
    (capacities : InstructionCapacities)
    {programSize : ℕ} [NeZero programSize] (program : Fin programSize → F p)
    {memorySize : ℕ} [NeZero memorySize] (memory : Fin memorySize → F p)
    (addInputs : Vector (InstructionStepInput (F p)) capacities.addCapacity)
    (mulInputs : Vector (InstructionStepInput (F p)) capacities.mulCapacity)
    (storeInputs : Vector (InstructionStepInput (F p)) capacities.storeStateCapacity)
    (loadInputs : Vector (InstructionStepInput (F p)) capacities.loadStateCapacity)
    (s : State (F p)) :
    totalOutgoing addInputs mulInputs storeInputs loadInputs s ≤
    totalCapacity capacities := by
  simp only [totalOutgoing, totalCapacity]
  have h1 := countOutgoing_le_length addInputs s
  have h2 := countOutgoing_le_length mulInputs s
  have h3 := countOutgoing_le_length storeInputs s
  have h4 := countOutgoing_le_length loadInputs s
  omega

/-- totalIncoming is bounded by totalCapacity -/
lemma totalIncoming_le_totalCapacity
    (capacities : InstructionCapacities)
    {programSize : ℕ} [NeZero programSize] (program : Fin programSize → F p)
    {memorySize : ℕ} [NeZero memorySize] (memory : Fin memorySize → F p)
    (addInputs : Vector (InstructionStepInput (F p)) capacities.addCapacity)
    (mulInputs : Vector (InstructionStepInput (F p)) capacities.mulCapacity)
    (storeInputs : Vector (InstructionStepInput (F p)) capacities.storeStateCapacity)
    (loadInputs : Vector (InstructionStepInput (F p)) capacities.loadStateCapacity)
    (s : State (F p)) :
    totalIncoming program memory addInputs mulInputs storeInputs loadInputs s ≤
    totalCapacity capacities := by
  simp only [totalIncoming, totalCapacity]
  have h1 := countIncoming_le_length addInputs addPostState s
  have h2 := countIncoming_le_length mulInputs mulPostState s
  have h3 := countIncoming_le_length storeInputs storeStatePostState s
  have h4 := countIncoming_le_length loadInputs (loadStatePostState program memory) s
  omega

/-- Combined bound: totalOutgoing + totalIncoming + 1 < p when 2 * totalCapacity + 1 < p -/
lemma totalFlow_bound
    (capacities : InstructionCapacities)
    {programSize : ℕ} [NeZero programSize] (program : Fin programSize → F p)
    {memorySize : ℕ} [NeZero memorySize] (memory : Fin memorySize → F p)
    (addInputs : Vector (InstructionStepInput (F p)) capacities.addCapacity)
    (mulInputs : Vector (InstructionStepInput (F p)) capacities.mulCapacity)
    (storeInputs : Vector (InstructionStepInput (F p)) capacities.storeStateCapacity)
    (loadInputs : Vector (InstructionStepInput (F p)) capacities.loadStateCapacity)
    (h_capacity : 2 * totalCapacity capacities + 1 < p)
    (s : State (F p)) :
    totalOutgoing addInputs mulInputs storeInputs loadInputs s +
    totalIncoming program memory addInputs mulInputs storeInputs loadInputs s + 1 < p := by
  have h_out := totalOutgoing_le_totalCapacity capacities program memory
    addInputs mulInputs storeInputs loadInputs s
  have h_in := totalIncoming_le_totalCapacity capacities program memory
    addInputs mulInputs storeInputs loadInputs s
  omega

/--
When the ExecutionBundle.Spec holds with balanced adds (toFinsupp = 0),
the Run built from enabled instructions has the expected netFlow properties.

This is the key lemma connecting InteractionDelta to Run.netFlow.
-/
theorem balanced_adds_implies_netFlow
    (capacities : InstructionCapacities)
    {programSize : ℕ} [NeZero programSize] (program : Fin programSize → F p)
    {memorySize : ℕ} [NeZero memorySize] (memory : Fin memorySize → F p)
    (inputs : ExecutionCircuitInput capacities (F p))
    (adds : InteractionDelta (F p))
    (h_spec : ExecutionBundle.Spec capacities program memory inputs adds)
    (h_balanced : adds.toFinsupp = 0)
    (h_ne : inputs.initialState ≠ inputs.finalState)
    (h_capacity : 2 * totalCapacity capacities + 1 < p) :
    let R := buildRunFromInputs program memory
               inputs.bundledInputs.addInputs
               inputs.bundledInputs.mulInputs
               inputs.bundledInputs.storeStateInputs
               inputs.bundledInputs.loadStateInputs
    R.netFlow inputs.initialState = 1 ∧
    R.netFlow inputs.finalState = -1 ∧
    ∀ s, s ≠ inputs.initialState → s ≠ inputs.finalState → R.netFlow s = 0 := by

  /-
  Proof outline:

  From h_spec, we have:
    adds = InteractionDelta.single initialState 1 +
           addAdds + mulAdds + storeStateAdds + loadStateAdds +
           InteractionDelta.single finalState (-1)

  For any state s, the multiplicity in adds.toFinsupp is:
    adds.toFinsupp (stateToNamedList s) =
      (if s = initialState then 1 else 0) +    -- from initial emission
      (-outgoing_edges_from_s + incoming_edges_to_s) +  -- from instruction bundles
      (if s = finalState then -1 else 0)       -- from final emission

  where outgoing_edges_from_s = number of enabled instructions with preState = s
        incoming_edges_to_s = number of enabled instructions with postState = s

  This is because each enabled instruction contributes:
    - preState with multiplicity -1 (outgoing edge)
    - postState with multiplicity +1 (incoming edge)

  From h_balanced (adds.toFinsupp = 0), for all s:
    emission(s) + incoming - outgoing = 0  (in F p)

  where emission(s) = 1 if s = initial, -1 if s = final, 0 otherwise.

  Rearranging: outgoing - incoming = emission(s) (in F p)

  Since p > 512 and edge counts are bounded by totalCapacity (which is << p),
  field arithmetic equals integer arithmetic for these values.

  Therefore:
    netFlow(s) = outgoing - incoming = emission(s) as integers

  Which gives the three cases we need.
  -/

  -- Define abbreviations for the inputs
  let addInputs := inputs.bundledInputs.addInputs
  let mulInputs := inputs.bundledInputs.mulInputs
  let storeInputs := inputs.bundledInputs.storeStateInputs
  let loadInputs := inputs.bundledInputs.loadStateInputs

  -- Define the Run
  let R := buildRunFromInputs program memory addInputs mulInputs storeInputs loadInputs

  -- Helper: get the field equation for a state s
  have h_field_eq : ∀ s,
      (↑(totalOutgoing addInputs mulInputs storeInputs loadInputs s) -
       ↑(totalIncoming program memory addInputs mulInputs storeInputs loadInputs s) : F p) =
      (if s = inputs.initialState then 1 else 0) + (if s = inputs.finalState then -1 else 0) :=
    emission_eq_flow_diff capacities program memory inputs adds h_spec h_balanced

  -- Helper: netFlow equals totalOutgoing - totalIncoming (as integers)
  have h_netFlow : ∀ s, R.netFlow s =
      (totalOutgoing addInputs mulInputs storeInputs loadInputs s : ℤ) -
      (totalIncoming program memory addInputs mulInputs storeInputs loadInputs s : ℤ) :=
    netFlow_eq_totalOutgoing_sub_totalIncoming program memory addInputs mulInputs storeInputs loadInputs

  -- Use extracted bound lemmas
  have h_bounds := totalFlow_bound capacities program memory
    addInputs mulInputs storeInputs loadInputs h_capacity

  constructor
  · -- Case: R.netFlow initialState = 1
    rw [h_netFlow]
    have h_eq := h_field_eq inputs.initialState
    simp only [if_true, if_neg h_ne, add_zero] at h_eq
    exact int_sub_eq_one_of_field_sub_eq_one _ _ (h_bounds inputs.initialState) h_eq
  constructor
  · -- Case: R.netFlow finalState = -1
    rw [h_netFlow]
    have h_eq := h_field_eq inputs.finalState
    simp only [if_neg (Ne.symm h_ne), if_true, zero_add] at h_eq
    exact int_sub_eq_neg_one_of_field_sub_eq_neg_one _ _ (h_bounds inputs.finalState) h_eq
  · -- Case: R.netFlow s = 0 for s ≠ initial, s ≠ final
    intro s h_not_init h_not_final
    rw [h_netFlow]
    have h_eq := h_field_eq s
    simp only [if_neg h_not_init, if_neg h_not_final, add_zero] at h_eq
    have h_small : totalOutgoing addInputs mulInputs storeInputs loadInputs s +
                   totalIncoming program memory addInputs mulInputs storeInputs loadInputs s < p := by
      have := h_bounds s; omega
    exact int_sub_eq_zero_of_field_sub_eq_zero _ _ h_small h_eq

/-- Helper: if bundleEdgeCount > 0, there exists an enabled input matching the transition -/
lemma bundleEdgeCount_pos_implies_exists {n : ℕ}
    (inputs : Vector (InstructionStepInput (F p)) n)
    (postStateFn : State (F p) → State (F p))
    (t : State (F p) × State (F p))
    (h : bundleEdgeCount inputs postStateFn t > 0) :
    ∃ i : Fin n, inputs[i].enabled = 1 ∧ inputs[i].preState = t.1 ∧ postStateFn inputs[i].preState = t.2 := by
  simp only [bundleEdgeCount] at h
  -- Sum is positive, so it's nonzero
  have h_ne : (inputs.toList.map (fun i => instructionEdgeContribution i postStateFn t)).sum ≠ 0 := by omega
  -- Use List.exists_mem_ne_zero_of_sum_ne_zero
  obtain ⟨x, h_mem, h_ne_zero⟩ := List.exists_mem_ne_zero_of_sum_ne_zero h_ne
  -- x is in the mapped list, so there's some input that produced it
  simp only [List.mem_map] at h_mem
  obtain ⟨input, h_in_list, h_eq⟩ := h_mem
  -- The contribution is nonzero, so the condition is true (contribution is 0 or 1)
  simp only [instructionEdgeContribution] at h_eq
  split at h_eq
  case isTrue h_cond =>
    -- input is in inputs.toList, so we can get an index
    have h_mem_toList : input ∈ inputs.toList := h_in_list
    rw [Vector.mem_toList_iff, Vector.mem_iff_getElem] at h_mem_toList
    obtain ⟨i, hi_lt, hi⟩ := h_mem_toList
    let idx : Fin n := ⟨i, hi_lt⟩
    use idx
    -- h_cond uses input, hi shows inputs[i] = input
    -- inputs[idx] = input by hi (both are inputs[i]'hi_lt definitionally)
    have h_eq_input : inputs[idx] = input := hi
    rw [h_eq_input]
    -- h_cond has t.1 = input.preState, but goal needs input.preState = t.1
    -- Similarly for t.2 and postStateFn
    obtain ⟨h1, h2, h3⟩ := h_cond
    exact ⟨h1, h2.symm, h3.symm⟩
  case isFalse =>
    -- h_eq : 0 = x and x ≠ 0 leads to contradiction
    rw [← h_eq] at h_ne_zero
    exact absurd rfl h_ne_zero

/--
The Run built from enabled instructions is valid: every edge corresponds to
a valid femtoCairoMachineTransition.
-/
theorem buildRunFromInputs_valid
    (capacities : InstructionCapacities)
    {programSize : ℕ} [NeZero programSize] (program : Fin programSize → F p)
    {memorySize : ℕ} [NeZero memorySize] (memory : Fin memorySize → F p)
    (inputs : ExecutionCircuitInput capacities (F p))
    (adds : InteractionDelta (F p))
    (h_spec : ExecutionBundle.Spec capacities program memory inputs adds) :
    let R := buildRunFromInputs program memory
               inputs.bundledInputs.addInputs
               inputs.bundledInputs.mulInputs
               inputs.bundledInputs.storeStateInputs
               inputs.bundledInputs.loadStateInputs
    IsValidRun program memory R := by
  -- Each edge in R comes from an enabled instruction.
  -- The instruction's Spec (via the bundle spec) implies a valid transition.
  -- We have theorems like AddInstruction_Spec_implies_transition that give us this.

  -- Introduce the let binding
  intro R

  intro s1 s2 h_edge
  -- h_edge : R (s1, s2) > 0
  -- Need to show: femtoCairoMachineTransition program memory s1 = some s2

  -- Extract the bundle specs from h_spec
  obtain ⟨addAdds, mulAdds, storeStateAdds, loadStateAdds,
          h_add_bundle, h_mul_bundle, h_store_bundle, h_load_bundle, _⟩ := h_spec

  -- R is defined as buildRunFromInputs ..., so h_edge is definitionally equal to the expanded form
  -- We use change to make this explicit
  change bundleEdgeCount inputs.bundledInputs.addInputs addPostState (s1, s2) +
         bundleEdgeCount inputs.bundledInputs.mulInputs mulPostState (s1, s2) +
         bundleEdgeCount inputs.bundledInputs.storeStateInputs storeStatePostState (s1, s2) +
         bundleEdgeCount inputs.bundledInputs.loadStateInputs (loadStatePostState program memory) (s1, s2) > 0 at h_edge

  -- The edge count is the sum of edge counts from each bundle.
  -- If the total is > 0, at least one bundle contributed.
  -- Use Nat.add_pos_iff_pos_or_pos to find which bundle contributed
  rcases Nat.add_pos_iff_pos_or_pos.mp h_edge with h_add_mul_store | h_load
  · rcases Nat.add_pos_iff_pos_or_pos.mp h_add_mul_store with h_add_mul | h_store
    · rcases Nat.add_pos_iff_pos_or_pos.mp h_add_mul with h_add | h_mul
      · -- ADD bundle contributed
        obtain ⟨i, h_enabled, h_pre, h_post⟩ := bundleEdgeCount_pos_implies_exists
          inputs.bundledInputs.addInputs addPostState (s1, s2) h_add
        obtain ⟨stepAdds, h_step_specs, _⟩ := h_add_bundle
        simp only [IsValidTransition] at *
        rw [← h_pre, ← h_post]
        exact AddInstruction_Spec_transition_postState program memory _ _ (h_step_specs i) h_enabled
      · -- MUL bundle contributed
        obtain ⟨i, h_enabled, h_pre, h_post⟩ := bundleEdgeCount_pos_implies_exists
          inputs.bundledInputs.mulInputs mulPostState (s1, s2) h_mul
        obtain ⟨stepAdds, h_step_specs, _⟩ := h_mul_bundle
        simp only [IsValidTransition] at *
        rw [← h_pre, ← h_post]
        exact MulInstruction_Spec_transition_postState program memory _ _ (h_step_specs i) h_enabled
    · -- StoreState bundle contributed
      obtain ⟨i, h_enabled, h_pre, h_post⟩ := bundleEdgeCount_pos_implies_exists
        inputs.bundledInputs.storeStateInputs storeStatePostState (s1, s2) h_store
      obtain ⟨stepAdds, h_step_specs, _⟩ := h_store_bundle
      simp only [IsValidTransition] at *
      rw [← h_pre, ← h_post]
      exact StoreStateInstruction_Spec_transition_postState program memory _ _ (h_step_specs i) h_enabled
  · -- LoadState bundle contributed
    obtain ⟨i, h_enabled, h_pre, h_post⟩ := bundleEdgeCount_pos_implies_exists
      inputs.bundledInputs.loadStateInputs (loadStatePostState program memory) (s1, s2) h_load
    obtain ⟨stepAdds, h_step_specs, _⟩ := h_load_bundle
    simp only [IsValidTransition] at *
    rw [← h_pre, ← h_post]
    exact LoadStateInstruction_Spec_transition_postState program memory _ _ (h_step_specs i) h_enabled

/--
The main theorem: If ExecutionBundle.Spec holds with balanced adds, there exists a valid execution.

This is a complex theorem that requires:
1. Extracting all enabled instruction transitions from the spec
2. Building a Run from these transitions
3. Showing the Run has netFlow = +1 at initial, -1 at final, 0 elsewhere
4. Applying exists_path_from_source_to_sink to get a path
5. Converting the path to femtoCairoMachineBoundedExecution

The key insight is that the balanced InteractionDelta (adds.toFinsupp = 0) encodes
a valid execution trace through the source-sink flow property.

### Key difficulty

The main challenge is bridging between two different representations:

1. **InteractionDelta (F p)**: A list of `(NamedList F × F)` pairs where:
   - `NamedList` contains `("state", [pc, ap, fp])`
   - Multiplicity is a field element (so -1 is actually p-1)
   - Balance means `toFinsupp = 0` as field elements

2. **Utils.StateTransition.Run S**: A function `(S × S) → ℕ` where:
   - Transitions are between actual states
   - Counts are natural numbers
   - `netFlow` computes outflow - inflow as integers

To bridge these, we would need:
- Convert `NamedList F` ↔ `State F` (we have `stateToNamedList` and `namedListToState`)
- Convert field multiplicities to integers carefully (accounting for -1 = p-1 in F)
- Extract transitions from the bundle specs (each enabled instruction gives one transition)
- Build a Run and prove netFlow properties

The Fintype instance for `State (F p)` exists (since F p is finite), allowing use of
`exists_path_from_source_to_sink`. However, the multiset arithmetic to prove netFlow
properties from the balanced `InteractionDelta` is complex.
-/
theorem Spec_implies_execution
    (capacities : InstructionCapacities)
    {programSize : ℕ} [NeZero programSize] (program : Fin programSize → F p) (h_programSize : programSize < p)
    {memorySize : ℕ} [NeZero memorySize] (memory : Fin memorySize → F p) (h_memorySize : memorySize < p)
    (inputs : ExecutionCircuitInput capacities (F p))
    (adds : InteractionDelta (F p))
    (h_spec : ExecutionBundle.Spec capacities program memory inputs adds)
    (h_balanced : adds.toFinsupp = 0)
    (h_capacity : 2 * totalCapacity capacities + 1 < p) :
    ∃ (steps : ℕ),
      femtoCairoMachineBoundedExecution program memory (some inputs.initialState) steps =
        some inputs.finalState := by
  -- The proof outline:
  -- 1. From h_adds_eq, the total adds are:
  --    initialState(+1) + all_instruction_adds + finalState(-1)
  --
  -- 2. Each enabled instruction contributes: preState(-1) + postState(+1)
  --    and each disabled instruction contributes 0
  --
  -- 3. From h_balanced (adds.toFinsupp = 0), the multiset is balanced:
  --    - initialState has net +1 (source)
  --    - finalState has net -1 (sink)
  --    - all intermediate states have net 0 (each consumed once, produced once)
  --
  -- 4. This matches the preconditions of exists_path_from_source_to_sink
  --
  -- 5. That theorem gives us a path, which we convert to bounded execution

  -- Build the Run from enabled instruction transitions
  let R := buildRunFromInputs program memory
             inputs.bundledInputs.addInputs
             inputs.bundledInputs.mulInputs
             inputs.bundledInputs.storeStateInputs
             inputs.bundledInputs.loadStateInputs

  -- Special case: if initialState = finalState, we're done with 0 steps
  by_cases h_eq : inputs.initialState = inputs.finalState
  case pos =>
    use 0
    simp [femtoCairoMachineBoundedExecution, h_eq]
  case neg =>
    -- General case: initialState ≠ finalState
    -- Use the key lemmas to prove netFlow properties and Run validity

    -- Step 1: Get netFlow properties from balanced_adds_implies_netFlow
    have h_netFlow := balanced_adds_implies_netFlow capacities program memory
                       inputs adds h_spec h_balanced h_eq h_capacity
    obtain ⟨h_netFlow_source, h_netFlow_sink, h_netFlow_others⟩ := h_netFlow

    -- Step 2: Get Run validity from buildRunFromInputs_valid
    have h_valid : IsValidRun program memory R :=
      buildRunFromInputs_valid capacities program memory inputs adds h_spec

    -- Step 3: Apply exists_path_from_source_to_sink
    -- This requires Fintype (State (F p)) which we have from FemtoCairo.Types
    have h_path := Utils.StateTransition.exists_path_from_source_to_sink R
                     inputs.initialState inputs.finalState
                     h_netFlow_source
                     (fun x hx1 hx2 => h_netFlow_others x hx1 hx2)

    -- Step 4: Extract path and convert to bounded execution
    obtain ⟨path, h_head, h_last, h_nonempty, h_contains, h_nodup⟩ := h_path

    -- Step 5: Use valid_path_implies_bounded_execution to get the result
    use pathToExecutionSteps path
    exact valid_path_implies_bounded_execution program memory path
            inputs.initialState inputs.finalState R h_valid h_contains
            h_nonempty h_head h_last

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
    (h_spec : ExecutionBundle.Spec capacities program memory inputs adds)
    (h_capacity : 2 * totalCapacity capacities + 1 < p) :
    ExecutionExistenceSpec capacities program memory inputs adds := by
  intro h_balanced
  exact Spec_implies_execution capacities program h_programSize memory h_memorySize inputs adds h_spec h_balanced h_capacity

/--
The circuit with the weaker execution existence spec.

This uses `GeneralFormalCircuitChangingMultiset.weakenSpec` to weaken the spec from
`ExecutionBundle.Spec` to `ExecutionExistenceSpec`.
-/
def circuitWithExecutionExistenceSpec
    (capacities : InstructionCapacities)
    {programSize : ℕ} [NeZero programSize] (program : Fin programSize → F p) (h_programSize : programSize < p)
    {memorySize : ℕ} [NeZero memorySize] (memory : Fin memorySize → F p) (h_memorySize : memorySize < p)
    (h_capacity : 2 * totalCapacity capacities + 1 < p) :
    GeneralFormalCircuitChangingMultiset (F p) (ExecutionCircuitInput capacities) unit :=
  (ExecutionBundle.circuit capacities program h_programSize memory h_memorySize).weakenSpec
    (fun input _ adds => ExecutionBundle.Assumptions capacities (programSize := programSize) input →
      ExecutionExistenceSpec capacities program memory input adds)
    (fun input _ adds h_spec h_assumptions =>
      Spec_implies_ExecutionExistenceSpec capacities program h_programSize memory h_memorySize
        input adds (h_spec h_assumptions) h_capacity)

end Examples.PicoCairoMultiplicity.TraceExecution
