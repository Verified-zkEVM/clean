/-
PicoCairoMultiplicity Execution Bundle
Combines all four instruction circuits (ADD, MUL, LoadState, StoreState).
For a single execution step, exactly one instruction is enabled.
-/

import Clean.Circuit.Basic
import Clean.Circuit.Subcircuit
import Clean.Circuit.Loops
import Clean.Examples.PicoCairoMultiplicity.Types
import Clean.Examples.PicoCairoMultiplicity.Helpers
import Clean.Examples.PicoCairoMultiplicity.AddInstruction
import Clean.Examples.PicoCairoMultiplicity.MulInstruction
import Clean.Examples.PicoCairoMultiplicity.LoadStateInstruction
import Clean.Examples.PicoCairoMultiplicity.StoreStateInstruction
import Clean.Examples.FemtoCairo.FemtoCairo
import Clean.Examples.FemtoCairo.Types
import Clean.Examples.FemtoCairo.Spec
import Clean.Gadgets.Boolean
import Batteries.Data.Vector.Lemmas

namespace Examples.PicoCairoMultiplicity.ExecutionBundle

open Examples.FemtoCairo
open Examples.FemtoCairo.Types
open Examples.FemtoCairo.Spec
open Examples.PicoCairoMultiplicity.Types
open Examples.PicoCairoMultiplicity.Helpers

variable {p : ℕ} [Fact p.Prime] [p_large_enough: Fact (p > 512)]

/--
Input for the execution bundle: pre-state and 4 enabled flags for each instruction type.
Exactly one enabled flag should be 1.
-/
structure ExecutionBundleInput (F : Type) where
  preState : State F
  enableAdd : F
  enableMul : F
  enableStoreState : F
  enableLoadState : F

instance : ProvableStruct ExecutionBundleInput where
  components := [State, field, field, field, field]
  toComponents := fun { preState, enableAdd, enableMul, enableStoreState, enableLoadState } =>
    .cons preState (.cons enableAdd (.cons enableMul (.cons enableStoreState (.cons enableLoadState .nil))))
  fromComponents := fun (.cons preState (.cons enableAdd (.cons enableMul (.cons enableStoreState (.cons enableLoadState .nil))))) => {
    preState, enableAdd, enableMul, enableStoreState, enableLoadState
  }

/--
Main circuit for the execution bundle.
Executes each instruction circuit with its enabled flag.
Asserts that exactly one instruction is enabled.
-/
def main
    {programSize : ℕ} [NeZero programSize] (program : Fin programSize → (F p)) (h_programSize : programSize < p)
    {memorySize : ℕ} [NeZero memorySize] (memory : Fin memorySize → (F p)) (h_memorySize : memorySize < p)
    (input : Var ExecutionBundleInput (F p)) : Circuit (F p) Unit := do

  -- Assert all enabled flags are boolean
  assertBool input.enableAdd
  assertBool input.enableMul
  assertBool input.enableStoreState
  assertBool input.enableLoadState

  -- Assert exactly one is enabled: sum = 1
  assertZero (input.enableAdd + input.enableMul + input.enableStoreState + input.enableLoadState - 1)

  -- Execute each instruction circuit with its enabled flag
  -- Use .circuit.elaborated.main for compositional reuse
  (AddInstruction.circuit program h_programSize memory h_memorySize).elaborated.main {
    enabled := input.enableAdd,
    preState := input.preState
  }

  (MulInstruction.circuit program h_programSize memory h_memorySize).elaborated.main {
    enabled := input.enableMul,
    preState := input.preState
  }

  (StoreStateInstruction.circuit program h_programSize memory h_memorySize).elaborated.main {
    enabled := input.enableStoreState,
    preState := input.preState
  }

  (LoadStateInstruction.circuit program h_programSize memory h_memorySize).elaborated.main {
    enabled := input.enableLoadState,
    preState := input.preState
  }

/--
ElaboratedCircuit for the execution bundle.
-/
def elaborated
    {programSize : ℕ} [NeZero programSize] (program : Fin programSize → (F p)) (h_programSize : programSize < p)
    {memorySize : ℕ} [NeZero memorySize] (memory : Fin memorySize → (F p)) (h_memorySize : memorySize < p) :
    ElaboratedCircuit (F p) ExecutionBundleInput unit where
  main := main program h_programSize memory h_memorySize
  -- 4×assertBool(0) + assertZero(0) + 4×instruction(27) = 108
  localLength _ := 108
  localLength_eq := by
    intro input offset
    sorry
  output _ _ := ()
  localAdds input env offset :=
    let preState := eval env input.preState
    let enableAdd := input.enableAdd.eval env
    let enableMul := input.enableMul.eval env
    let enableStoreState := input.enableStoreState.eval env
    let enableLoadState := input.enableLoadState.eval env

    -- ADD instruction delta
    let addPostState : State (F p) := { pc := preState.pc + 4, ap := preState.ap, fp := preState.fp }
    let addDelta := InteractionDelta.single ⟨"state", [preState.pc, preState.ap, preState.fp]⟩ (enableAdd * (-1)) +
                    InteractionDelta.single ⟨"state", [addPostState.pc, addPostState.ap, addPostState.fp]⟩ (enableAdd * 1)

    -- MUL instruction delta
    let mulPostState : State (F p) := { pc := preState.pc + 4, ap := preState.ap, fp := preState.fp }
    let mulDelta := InteractionDelta.single ⟨"state", [preState.pc, preState.ap, preState.fp]⟩ (enableMul * (-1)) +
                    InteractionDelta.single ⟨"state", [mulPostState.pc, mulPostState.ap, mulPostState.fp]⟩ (enableMul * 1)

    -- StoreState instruction delta
    let storePostState : State (F p) := { pc := preState.pc + 4, ap := preState.ap, fp := preState.fp }
    let storeDelta := InteractionDelta.single ⟨"state", [preState.pc, preState.ap, preState.fp]⟩ (enableStoreState * (-1)) +
                      InteractionDelta.single ⟨"state", [storePostState.pc, storePostState.ap, storePostState.fp]⟩ (enableStoreState * 1)

    -- LoadState instruction delta (post-state uses memory values)
    let loadV1 := env.get (offset + 27 + 27 + 27 + 4 + 8 + 4)
    let loadV2 := env.get (offset + 27 + 27 + 27 + 4 + 8 + 5 + 4)
    let loadV3 := env.get (offset + 27 + 27 + 27 + 4 + 8 + 5 + 5 + 4)
    let loadPostState : State (F p) := { pc := loadV1, ap := loadV2, fp := loadV3 }
    let loadDelta := InteractionDelta.single ⟨"state", [preState.pc, preState.ap, preState.fp]⟩ (enableLoadState * (-1)) +
                     InteractionDelta.single ⟨"state", [loadPostState.pc, loadPostState.ap, loadPostState.fp]⟩ (enableLoadState * 1)

    addDelta + mulDelta + storeDelta + loadDelta
  localAdds_eq := by
    intro input env offset
    sorry
  subcircuitsConsistent := by
    intro input offset
    sorry

/--
Assumptions for the execution bundle.
All enabled flags are boolean and exactly one is 1.
-/
def Assumptions
    {programSize : ℕ} [NeZero programSize]
    (input : ExecutionBundleInput (F p)) : Prop :=
  IsBool input.enableAdd ∧
  IsBool input.enableMul ∧
  IsBool input.enableStoreState ∧
  IsBool input.enableLoadState ∧
  input.enableAdd + input.enableMul + input.enableStoreState + input.enableLoadState = 1 ∧
  ZMod.val input.preState.pc + 3 < programSize

/--
Specification for the execution bundle.
The bundle correctly executes whichever instruction is enabled.
-/
def Spec
    {programSize : ℕ} [NeZero programSize] (program : Fin programSize → (F p))
    {memorySize : ℕ} [NeZero memorySize] (memory : Fin memorySize → (F p))
    (input : ExecutionBundleInput (F p)) (adds : InteractionDelta (F p)) : Prop :=
  -- Delegate to the appropriate instruction's spec based on which one is enabled
  if input.enableAdd = 1 then
    AddInstruction.Spec program memory { enabled := 1, preState := input.preState } adds
  else if input.enableMul = 1 then
    MulInstruction.Spec program memory { enabled := 1, preState := input.preState } adds
  else if input.enableStoreState = 1 then
    StoreStateInstruction.Spec program memory { enabled := 1, preState := input.preState } adds
  else if input.enableLoadState = 1 then
    LoadStateInstruction.Spec program memory { enabled := 1, preState := input.preState } adds
  else
    False  -- At least one should be enabled

/--
FormalAssertionChangingMultiset for the execution bundle.
-/
def circuit
    {programSize : ℕ} [NeZero programSize] (program : Fin programSize → (F p)) (h_programSize : programSize < p)
    {memorySize : ℕ} [NeZero memorySize] (memory : Fin memorySize → (F p)) (h_memorySize : memorySize < p) :
    FormalAssertionChangingMultiset (F p) ExecutionBundleInput where
  elaborated := elaborated program h_programSize memory h_memorySize
  Assumptions := Assumptions (programSize := programSize)
  Spec := Spec program memory
  soundness := by
    sorry
  completeness := by
    sorry

end Examples.PicoCairoMultiplicity.ExecutionBundle
