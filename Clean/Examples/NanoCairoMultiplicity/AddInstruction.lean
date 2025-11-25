/-
NanoCairoMultiplicity ADD Instruction Circuit
Following PR 286 PicoCairo pattern but using multiplicities instead of timestamps.
-/

import Clean.Circuit.Basic
import Clean.Circuit.Subcircuit
import Clean.Circuit.Loops
import Clean.Examples.NanoCairoMultiplicity.Types
import Clean.Examples.NanoCairoMultiplicity.Helpers
import Clean.Examples.FemtoCairo.FemtoCairo
import Clean.Examples.FemtoCairo.Types
import Clean.Examples.FemtoCairo.Spec
import Clean.Gadgets.Boolean
import Batteries.Data.Vector.Lemmas

namespace Examples.NanoCairoMultiplicity.AddInstruction

open Examples.FemtoCairo
open Examples.FemtoCairo.Types
open Examples.FemtoCairo.Spec
open Examples.NanoCairoMultiplicity.Types
open Examples.NanoCairoMultiplicity.Helpers

variable {p : ℕ} [Fact p.Prime] [p_large_enough: Fact (p > 512)]

/--
Main circuit for ADD instruction step.
Takes enabled flag and pre-state.
If enabled, executes the FemtoCairo step and emits multiplicity operations.
-/
def main
    {programSize : ℕ} [NeZero programSize] (program : Fin programSize → (F p)) (h_programSize : programSize < p)
    {memorySize : ℕ} [NeZero memorySize] (memory : Fin memorySize → (F p)) (h_memorySize : memorySize < p)
    (input : Var InstructionStepInput (F p)) : Circuit (F p) Unit := do

  let enabled := input.enabled
  let preState := input.preState

  -- Step 1: Assert enabled is boolean (0 or 1)
  assertBool enabled

  -- Step 2: Conditionally emit -1 for pre-state (consuming)
  emitStateWhen enabled (-1) preState

  -- Step 3: Execute the FemtoCairo step circuit
  let nextState ← (femtoCairoStepCircuit program h_programSize memory h_memorySize).main preState

  -- Step 4: Conditionally emit +1 for post-state (producing)
  emitStateWhen enabled 1 nextState

/--
ElaboratedCircuit for the ADD instruction step.
-/
def elaborated
    {programSize : ℕ} [NeZero programSize] (program : Fin programSize → (F p)) (h_programSize : programSize < p)
    {memorySize : ℕ} [NeZero memorySize] (memory : Fin memorySize → (F p)) (h_memorySize : memorySize < p) :
    ElaboratedCircuit (F p) InstructionStepInput unit where
  main := main program h_programSize memory h_memorySize
  -- assertBool(0) + emitStateWhen(0) + femtoCairoStep(30) + emitStateWhen(0) = 30
  localLength _ := 30
  output _ _ := ()
  localAdds input env offset :=
    let preState := eval env input.preState
    let nextState := eval env ((femtoCairoStepCircuit program h_programSize memory h_memorySize).output input.preState offset)
    let enabled := input.enabled.eval env
    [(⟨"state", [preState.pc, preState.ap, preState.fp]⟩, enabled * (-1)),
     (⟨"state", [nextState.pc, nextState.ap, nextState.fp]⟩, enabled * 1)]
  localAdds_eq := by
    intro input env offset
    simp only [main, circuit_norm, emitStateWhen, emitAdd, femtoCairoStepCircuit]
    sorry

/--
Assumptions for the ADD instruction step.
-/
def Assumptions
    {programSize : ℕ} [NeZero programSize]
    (input : InstructionStepInput (F p)) : Prop :=
  IsBool input.enabled ∧
  ZMod.val input.preState.pc + 3 < programSize

/--
Specification for the ADD instruction step.
If enabled, the transition must be valid and the adds must reflect the state change.
-/
def Spec
    {programSize : ℕ} [NeZero programSize] (program : Fin programSize → (F p))
    {memorySize : ℕ} [NeZero memorySize] (memory : Fin memorySize → (F p))
    (input : InstructionStepInput (F p)) (adds : List (NamedList (F p) × F p)) : Prop :=
  if input.enabled = 1 then
    ∃ nextState : State (F p),
      femtoCairoMachineTransition program memory input.preState = some nextState ∧
      adds = [(⟨"state", [input.preState.pc, input.preState.ap, input.preState.fp]⟩, -1),
              (⟨"state", [nextState.pc, nextState.ap, nextState.fp]⟩, 1)]
  else
    adds = [(⟨"state", [input.preState.pc, input.preState.ap, input.preState.fp]⟩, 0),
            (⟨"state", [0, 0, 0]⟩, 0)]  -- dummy adds with zero multiplicity

/--
FormalAssertionChangingMultiset for the ADD instruction step.
-/
def circuit
    {programSize : ℕ} [NeZero programSize] (program : Fin programSize → (F p)) (h_programSize : programSize < p)
    {memorySize : ℕ} [NeZero memorySize] (memory : Fin memorySize → (F p)) (h_memorySize : memorySize < p) :
    FormalAssertionChangingMultiset (F p) InstructionStepInput where
  elaborated := elaborated program h_programSize memory h_memorySize
  Assumptions := Assumptions (programSize := programSize)
  Spec := Spec program memory
  soundness := by
    intro offset env input_var input h_input h_assumptions h_constraints
    simp only [Spec]
    sorry
  completeness := by
    intro offset env input_var h_uses input h_input h_assumptions h_spec
    sorry

end Examples.NanoCairoMultiplicity.AddInstruction
