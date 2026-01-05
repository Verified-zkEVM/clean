import Clean.Circuit.Provable
import Clean.Examples.FemtoCairo.Types

/-!
# PicoCairoMultiplicity Types

Type definitions for the multiplicity-based VM execution tracking.
Following the PR 286 PicoCairo pattern but using multiplicities instead of timestamps.
-/

namespace Examples.PicoCairoMultiplicity.Types
open Examples.FemtoCairo.Types

variable {p : ℕ} [Fact p.Prime] [p_large_enough: Fact (p > 512)]

/-- Input for a single instruction step -/
structure InstructionStepInput (F : Type) where
  enabled : F        -- 0 = skip, 1 = execute
  preState : State F -- state before this instruction

/-- ProvableStruct instance for InstructionStepInput -/
instance : ProvableStruct InstructionStepInput where
  components := [field, State]
  toComponents := fun { enabled, preState } => .cons enabled (.cons preState .nil)
  fromComponents := fun (.cons enabled (.cons preState .nil)) => { enabled, preState }

/-- NonEmptyProvableType instance for InstructionStepInput (size = 4 > 0) -/
instance : NonEmptyProvableType InstructionStepInput where
  nonempty := by simp only [ProvableType.size]; decide

/-- Capacities for each instruction type -/
structure InstructionCapacities where
  addCapacity : ℕ
  mulCapacity : ℕ
  storeStateCapacity : ℕ
  loadStateCapacity : ℕ
  addCapacity_nz : NeZero addCapacity := by infer_instance
  mulCapacity_nz : NeZero mulCapacity := by infer_instance
  storeStateCapacity_nz : NeZero storeStateCapacity := by infer_instance
  loadStateCapacity_nz : NeZero loadStateCapacity := by infer_instance

attribute [instance] InstructionCapacities.addCapacity_nz
attribute [instance] InstructionCapacities.mulCapacity_nz
attribute [instance] InstructionCapacities.storeStateCapacity_nz
attribute [instance] InstructionCapacities.loadStateCapacity_nz

/-- Bundled inputs for all instruction types -/
structure BundledInstructionInputs (capacities : InstructionCapacities) (F : Type) where
  addInputs : Vector (InstructionStepInput F) capacities.addCapacity
  mulInputs : Vector (InstructionStepInput F) capacities.mulCapacity
  storeStateInputs : Vector (InstructionStepInput F) capacities.storeStateCapacity
  loadStateInputs : Vector (InstructionStepInput F) capacities.loadStateCapacity

/-- ProvableStruct instance for BundledInstructionInputs -/
instance (capacities : InstructionCapacities) : ProvableStruct (BundledInstructionInputs capacities) where
  components := [
    ProvableVector InstructionStepInput capacities.addCapacity,
    ProvableVector InstructionStepInput capacities.mulCapacity,
    ProvableVector InstructionStepInput capacities.storeStateCapacity,
    ProvableVector InstructionStepInput capacities.loadStateCapacity
  ]
  toComponents := fun { addInputs, mulInputs, storeStateInputs, loadStateInputs } =>
    .cons addInputs (.cons mulInputs (.cons storeStateInputs (.cons loadStateInputs .nil)))
  fromComponents := fun (.cons addInputs (.cons mulInputs (.cons storeStateInputs (.cons loadStateInputs .nil)))) =>
    { addInputs, mulInputs, storeStateInputs, loadStateInputs }

/-- Full execution circuit input -/
structure ExecutionCircuitInput (capacities : InstructionCapacities) (F : Type) where
  initialState : State F
  finalState : State F
  bundledInputs : BundledInstructionInputs capacities F

/-- ProvableStruct instance for ExecutionCircuitInput -/
instance (capacities : InstructionCapacities) : ProvableStruct (ExecutionCircuitInput capacities) where
  components := [State, State, BundledInstructionInputs capacities]
  toComponents := fun { initialState, finalState, bundledInputs } =>
    .cons initialState (.cons finalState (.cons bundledInputs .nil))
  fromComponents := fun (.cons initialState (.cons finalState (.cons bundledInputs .nil))) =>
    { initialState, finalState, bundledInputs }

end Examples.PicoCairoMultiplicity.Types
