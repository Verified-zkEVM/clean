/-
PicoCairoMultiplicity Trace Execution (Whole Chip)
Executes a bounded sequence of instruction steps, each using the ExecutionBundle.
Uses multiplicity-based argument for state transitions.
-/

import Clean.Circuit.Basic
import Clean.Circuit.Subcircuit
import Clean.Circuit.Loops
import Clean.Examples.PicoCairoMultiplicity.Types
import Clean.Examples.PicoCairoMultiplicity.Helpers
import Clean.Examples.PicoCairoMultiplicity.ExecutionBundle
import Clean.Examples.FemtoCairo.FemtoCairo
import Clean.Examples.FemtoCairo.Types
import Clean.Examples.FemtoCairo.Spec
import Clean.Gadgets.Boolean
import Batteries.Data.Vector.Lemmas

namespace Examples.PicoCairoMultiplicity.TraceExecution

open Examples.FemtoCairo
open Examples.FemtoCairo.Types
open Examples.FemtoCairo.Spec
open Examples.PicoCairoMultiplicity.Types
open Examples.PicoCairoMultiplicity.Helpers
open Examples.PicoCairoMultiplicity.ExecutionBundle

variable {p : ℕ} [Fact p.Prime] [p_large_enough: Fact (p > 512)]

/--
Input for the trace execution: initial state and number of steps.
-/
structure TraceInput (F : Type) where
  initialState : State F
  -- The actual steps are encoded in the witness

instance : ProvableStruct TraceInput where
  components := [State]
  toComponents := fun { initialState } => .cons initialState .nil
  fromComponents := fun (.cons initialState .nil) => { initialState }

/--
Main circuit for executing a bounded trace.
For n steps, we execute n ExecutionBundles in sequence.
The multiset argument ensures that:
1. Initial state is added with +1
2. Each step removes pre-state with -1 and adds post-state with +1
3. Final state is removed with -1
Net effect: initial state consumed, final state produced.
-/
def main (n : ℕ)
    {programSize : ℕ} [NeZero programSize] (program : Fin programSize → (F p)) (h_programSize : programSize < p)
    {memorySize : ℕ} [NeZero memorySize] (memory : Fin memorySize → (F p)) (h_memorySize : memorySize < p)
    (input : Var TraceInput (F p)) : Circuit (F p) Unit := do

  -- Emit +1 for initial state (it will be consumed by the first step)
  emitAdd 1 ⟨"state", [input.initialState.pc, input.initialState.ap, input.initialState.fp]⟩

  -- Execute n steps (each step is an ExecutionBundle)
  -- The pre-state for each step is determined by the witness
  for _ in [0:n] do
    -- Witness the pre-state for this step
    let preState : Var State (F p) ← ProvableType.witness fun _ => {
      pc := 0, ap := 0, fp := 0  -- Will be filled by witness
    }

    -- Witness which instruction type to execute
    let enableAdd : Expression (F p) ← witnessField fun _ => 0
    let enableMul : Expression (F p) ← witnessField fun _ => 0
    let enableStoreState : Expression (F p) ← witnessField fun _ => 0
    let enableLoadState : Expression (F p) ← witnessField fun _ => 0

    -- Execute the bundle
    ExecutionBundle.main program h_programSize memory h_memorySize {
      preState := preState,
      enableAdd := enableAdd,
      enableMul := enableMul,
      enableStoreState := enableStoreState,
      enableLoadState := enableLoadState
    }

/--
Specification for trace execution.
After n steps from initialState, we should have:
- Initial state consumed (multiplicity -1)
- Final state produced (multiplicity +1)
(The intermediate states cancel out via the multiset argument)
-/
def Spec (n : ℕ)
    {programSize : ℕ} [NeZero programSize] (program : Fin programSize → (F p))
    {memorySize : ℕ} [NeZero memorySize] (memory : Fin memorySize → (F p))
    (input : TraceInput (F p)) (adds : InteractionDelta (F p)) : Prop :=
  -- The trace execution is valid if there exists a final state such that:
  -- The net multiset change is exactly: remove initial + add final
  ∃ finalState : State (F p),
    -- n steps of valid execution from initialState reaches finalState
    Spec.femtoCairoMachineBoundedExecution program memory n input.initialState = some finalState ∧
    adds = InteractionDelta.single ⟨"state", [input.initialState.pc, input.initialState.ap, input.initialState.fp]⟩ (-1) +
           InteractionDelta.single ⟨"state", [finalState.pc, finalState.ap, finalState.fp]⟩ 1

/--
The whole PicoCairo chip using multiplicity arguments.
-/
noncomputable def chip (n : ℕ)
    {programSize : ℕ} [NeZero programSize] (program : Fin programSize → (F p)) (h_programSize : programSize < p)
    {memorySize : ℕ} [NeZero memorySize] (memory : Fin memorySize → (F p)) (h_memorySize : memorySize < p) :
    FormalAssertionChangingMultiset (F p) TraceInput where
  main := fun input => main n program h_programSize memory h_memorySize input
  localLength _ := sorry  -- TODO: Calculate based on n
  localLength_eq := by sorry
  output _ _ := ()
  localAdds _ _ _ := sorry  -- TODO: Aggregate localAdds from all steps
  localAdds_eq := by sorry
  subcircuitsConsistent := by sorry
  Assumptions := fun _ => True  -- TODO: Add proper assumptions
  Spec := Spec n program memory
  soundness := by sorry
  completeness := by sorry

end Examples.PicoCairoMultiplicity.TraceExecution
