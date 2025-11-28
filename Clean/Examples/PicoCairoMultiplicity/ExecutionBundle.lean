/-
PicoCairo Execution Bundle (Multiplicity version)
Combines all four instruction bundles (ADD, MUL, LoadState, StoreState).
Each bundle processes multiple instructions of a single type with given capacity.
-/

import Clean.Circuit.Basic
import Clean.Circuit.Subcircuit
import Clean.Circuit.Loops
import Clean.Circuit.Theorems
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

/-- NonEmptyProvableType instance for BundledInstructionInputs -/
instance (capacities : InstructionCapacities) : NonEmptyProvableType (BundledInstructionInputs capacities) where
  nonempty := by
    simp only [size, circuit_norm]
    simp only [List.sum_cons, List.sum_nil, add_zero, Nat.reduceAdd, gt_iff_lt, add_pos_iff,
      Nat.ofNat_pos, mul_pos_iff_of_pos_right]
    have : NeZero capacities.addCapacity := inferInstance
    rcases this
    omega

/-- NonEmptyProvableType instance for ExecutionCircuitInput -/
instance (capacities : InstructionCapacities) : NonEmptyProvableType (ExecutionCircuitInput capacities) where
  nonempty := by
    simp only [size, circuit_norm]
    -- Simplify List.sum to get [3, 3, ...].sum = 3 + (3 + ...)
    simp only [List.sum_cons, List.sum_nil, add_zero]
    -- Now we have 3 + (3 + ...) > 0, which holds since 3 > 0
    omega

/--
Main execution bundle that combines all instruction type bundles.
Includes initial state (+1), all instruction bundles, and final state (-1).
-/
def main
    (capacities : InstructionCapacities)
    {programSize : ℕ} [NeZero programSize] (program : Fin programSize → (F p)) (h_programSize : programSize < p)
    {memorySize : ℕ} [NeZero memorySize] (memory : Fin memorySize → (F p)) (h_memorySize : memorySize < p)
    (inputs : Var (ExecutionCircuitInput capacities) (F p)) :
    Circuit (F p) Unit := do
  emitAdd "state" 1 [inputs.initialState.pc, inputs.initialState.ap, inputs.initialState.fp]
  (AddInstruction.Bundle.circuit capacities.addCapacity program h_programSize memory h_memorySize) inputs.bundledInputs.addInputs
  (MulInstruction.Bundle.circuit capacities.mulCapacity program h_programSize memory h_memorySize) inputs.bundledInputs.mulInputs
  (StoreStateInstruction.Bundle.circuit capacities.storeStateCapacity program h_programSize memory h_memorySize) inputs.bundledInputs.storeStateInputs
  (LoadStateInstruction.Bundle.circuit capacities.loadStateCapacity program h_programSize memory h_memorySize) inputs.bundledInputs.loadStateInputs
  emitAdd "state" (-1) [inputs.finalState.pc, inputs.finalState.ap, inputs.finalState.fp]

/--
Elaborated circuit for the execution bundle.
The localAdds include initial state (+1), all instruction bundle adds, and final state (-1).
-/
def elaborated
    (capacities : InstructionCapacities)
    {programSize : ℕ} [NeZero programSize] (program : Fin programSize → (F p)) (h_programSize : programSize < p)
    {memorySize : ℕ} [NeZero memorySize] (memory : Fin memorySize → (F p)) (h_memorySize : memorySize < p) :
    ElaboratedCircuit (F p) (ExecutionCircuitInput capacities) unit where
  main := main capacities program h_programSize memory h_memorySize
  localLength _ :=
    capacities.addCapacity * 27 +
    capacities.mulCapacity * 27 +
    capacities.storeStateCapacity * 27 +
    capacities.loadStateCapacity * 27
  localLength_eq := by
    intros input offset
    simp only [circuit_norm, main, emitAdd]
    simp only [AddInstruction.Bundle.circuit, AddInstruction.Bundle.elaborated]
    simp only [MulInstruction.Bundle.circuit, MulInstruction.Bundle.elaborated]
    simp only [StoreStateInstruction.Bundle.circuit, StoreStateInstruction.Bundle.elaborated]
    simp only [LoadStateInstruction.Bundle.circuit, LoadStateInstruction.Bundle.elaborated]
    omega
  output _ _ := ()
  localAdds inputs env offset :=
    let initialState := eval env inputs.initialState
    let finalState := eval env inputs.finalState
    -- Initial state (+1)
    InteractionDelta.single ⟨"state", [initialState.pc, initialState.ap, initialState.fp]⟩ 1 +
    -- All instruction bundle adds
    (AddInstruction.Bundle.elaborated capacities.addCapacity program h_programSize memory h_memorySize).localAdds
      inputs.bundledInputs.addInputs env offset +
    (MulInstruction.Bundle.elaborated capacities.mulCapacity program h_programSize memory h_memorySize).localAdds
      inputs.bundledInputs.mulInputs env (offset + capacities.addCapacity * 27) +
    (StoreStateInstruction.Bundle.elaborated capacities.storeStateCapacity program h_programSize memory h_memorySize).localAdds
      inputs.bundledInputs.storeStateInputs env (offset + capacities.addCapacity * 27 + capacities.mulCapacity * 27) +
    (LoadStateInstruction.Bundle.elaborated capacities.loadStateCapacity program h_programSize memory h_memorySize).localAdds
      inputs.bundledInputs.loadStateInputs env (offset + capacities.addCapacity * 27 + capacities.mulCapacity * 27 + capacities.storeStateCapacity * 27) +
    -- Final state (-1)
    InteractionDelta.single ⟨"state", [finalState.pc, finalState.ap, finalState.fp]⟩ (-1)
  localAdds_eq := by
    intros inputs env offset
    simp only [main, circuit_norm, emitAdd]
    -- Use toSubcircuit_localAdds to relate subcircuit localAdds to bundle localAdds
    simp only [Operations.collectAdds, FormalAssertionChangingMultiset.toSubcircuit_localAdds,
      add_zero]
    -- Simplify NamedList.eval and Expression.eval for the initial/final state terms
    simp only [NamedList.eval, Expression.eval, List.map]
    -- Now we have the bundle's localAdds on both sides
    simp only [AddInstruction.Bundle.circuit, MulInstruction.Bundle.circuit,
      StoreStateInstruction.Bundle.circuit, LoadStateInstruction.Bundle.circuit,
      AddInstruction.Bundle.elaborated, MulInstruction.Bundle.elaborated,
      StoreStateInstruction.Bundle.elaborated, LoadStateInstruction.Bundle.elaborated]
    -- LHS uses + while RHS uses ++, which are the same for InteractionDelta
    simp only [← InteractionDelta.add_eq_append, InteractionDelta.toFinsupp_add, add_assoc]
    -- Remaining difference: -1*1 vs -1
    simp only [mul_one]
    -- The State.pc/ap/fp after Expression.eval should match (eval env state).pc/ap/fp
    rfl
  subcircuitsConsistent := by
    intros inputs offset
    simp only [main, circuit_norm, emitAdd]
    -- After simp, the goal is arithmetic about ElaboratedCircuit.localLength
    -- Simplify localLength to capacity * 27 values
    simp only [AddInstruction.Bundle.circuit, MulInstruction.Bundle.circuit,
      StoreStateInstruction.Bundle.circuit,
      AddInstruction.Bundle.elaborated, MulInstruction.Bundle.elaborated,
      StoreStateInstruction.Bundle.elaborated,
      ElaboratedCircuit.localLength]
    omega

/--
Assumptions for the execution bundle: each instruction bundle must satisfy its assumptions.
-/
def Assumptions
    (capacities : InstructionCapacities)
    {programSize : ℕ} [NeZero programSize]
    (inputs : ExecutionCircuitInput capacities (F p)) : Prop :=
  AddInstruction.Bundle.Assumptions capacities.addCapacity (programSize := programSize) inputs.bundledInputs.addInputs ∧
  MulInstruction.Bundle.Assumptions capacities.mulCapacity (programSize := programSize) inputs.bundledInputs.mulInputs ∧
  StoreStateInstruction.Bundle.Assumptions capacities.storeStateCapacity (programSize := programSize) inputs.bundledInputs.storeStateInputs ∧
  LoadStateInstruction.Bundle.Assumptions capacities.loadStateCapacity (programSize := programSize) inputs.bundledInputs.loadStateInputs

/--
Spec for the execution bundle: each instruction bundle must satisfy its spec,
and the total adds include initial state (+1), all bundle adds, and final state (-1).
-/
def Spec
    (capacities : InstructionCapacities)
    {programSize : ℕ} [NeZero programSize] (program : Fin programSize → (F p))
    {memorySize : ℕ} [NeZero memorySize] (memory : Fin memorySize → (F p))
    (inputs : ExecutionCircuitInput capacities (F p))
    (adds : InteractionDelta (F p)) : Prop :=
  ∃ (addAdds mulAdds storeStateAdds loadStateAdds : InteractionDelta (F p)),
    AddInstruction.Bundle.Spec capacities.addCapacity program memory inputs.bundledInputs.addInputs addAdds ∧
    MulInstruction.Bundle.Spec capacities.mulCapacity program memory inputs.bundledInputs.mulInputs mulAdds ∧
    StoreStateInstruction.Bundle.Spec capacities.storeStateCapacity program memory inputs.bundledInputs.storeStateInputs storeStateAdds ∧
    LoadStateInstruction.Bundle.Spec capacities.loadStateCapacity program memory inputs.bundledInputs.loadStateInputs loadStateAdds ∧
    adds = InteractionDelta.single ⟨"state", [inputs.initialState.pc, inputs.initialState.ap, inputs.initialState.fp]⟩ 1 +
           addAdds + mulAdds + storeStateAdds + loadStateAdds +
           InteractionDelta.single ⟨"state", [inputs.finalState.pc, inputs.finalState.ap, inputs.finalState.fp]⟩ (-1)

/--
Spec for GeneralFormalCircuitChangingMultiset: wraps Assumptions implication around Spec.
-/
private def CircuitSpec
    (capacities : InstructionCapacities)
    {programSize : ℕ} [NeZero programSize] (program : Fin programSize → (F p))
    {memorySize : ℕ} [NeZero memorySize] (memory : Fin memorySize → (F p))
    (input : ExecutionCircuitInput capacities (F p)) (_ : Unit) (adds : InteractionDelta (F p)) : Prop :=
  Assumptions capacities (programSize := programSize) input → Spec capacities program memory input adds

/--
Soundness proof for the execution bundle.
-/
private theorem circuit_soundness
    (capacities : InstructionCapacities)
    {programSize : ℕ} [NeZero programSize] (program : Fin programSize → (F p)) (h_programSize : programSize < p)
    {memorySize : ℕ} [NeZero memorySize] (memory : Fin memorySize → (F p)) (h_memorySize : memorySize < p) :
    GeneralFormalCircuit.SoundnessChangingMultiset (F p)
      (elaborated capacities program h_programSize memory h_memorySize)
      (CircuitSpec capacities program memory)
      (elaborated capacities program h_programSize memory h_memorySize).localAdds := by
  circuit_proof_start [CircuitSpec, AddInstruction.Bundle.circuit, AddInstruction.Bundle.elaborated,
    MulInstruction.Bundle.circuit, MulInstruction.Bundle.elaborated,
    StoreStateInstruction.Bundle.circuit, StoreStateInstruction.Bundle.elaborated,
    LoadStateInstruction.Bundle.circuit, LoadStateInstruction.Bundle.elaborated]
  intro h_assumptions
  -- Extract the four assumptions from h_assumptions
  obtain ⟨h_assump_add, h_assump_mul, h_assump_store, h_assump_load⟩ := h_assumptions
  -- We need to rewrite using h_input to convert eval env input_var.3.* to input.bundledInputs.*
  have h_eval_add : eval (α := ProvableVector InstructionStepInput capacities.addCapacity) env input_var.3.addInputs = input.bundledInputs.addInputs :=
    congrArg (fun x => x.bundledInputs.addInputs) h_input
  have h_eval_mul : eval (α := ProvableVector InstructionStepInput capacities.mulCapacity) env input_var.3.mulInputs = input.bundledInputs.mulInputs :=
    congrArg (fun x => x.bundledInputs.mulInputs) h_input
  have h_eval_store : eval (α := ProvableVector InstructionStepInput capacities.storeStateCapacity) env input_var.3.storeStateInputs = input.bundledInputs.storeStateInputs :=
    congrArg (fun x => x.bundledInputs.storeStateInputs) h_input
  have h_eval_load : eval (α := ProvableVector InstructionStepInput capacities.loadStateCapacity) env input_var.3.loadStateInputs = input.bundledInputs.loadStateInputs :=
    congrArg (fun x => x.bundledInputs.loadStateInputs) h_input
  have h_eval_initial : eval env input_var.initialState = input.initialState :=
    congrArg ExecutionCircuitInput.initialState h_input
  have h_eval_final : eval env input_var.finalState = input.finalState :=
    congrArg ExecutionCircuitInput.finalState h_input
  -- Extract the four implications from h_holds, applying eval rewrites
  rw [h_eval_add, h_eval_mul, h_eval_store, h_eval_load] at h_holds
  obtain ⟨h_add_impl, h_mul_impl, h_store_impl, h_load_impl⟩ := h_holds
  -- Apply each implication with its corresponding assumption to get the Specs
  have h_add_spec := h_add_impl h_assump_add
  have h_mul_spec := h_mul_impl h_assump_mul
  have h_store_spec := h_store_impl h_assump_store
  have h_load_spec := h_load_impl h_assump_load
  -- Unfold Spec and provide witnesses
  simp only [Spec]
  rw [h_eval_initial, h_eval_final]
  -- Convert ++ to + in the adds equality (both in goal and hypotheses)
  simp only [← InteractionDelta.add_eq_append] at h_add_spec h_mul_spec h_store_spec h_load_spec ⊢
  refine ⟨_, _, _, _, h_add_spec, h_mul_spec, h_store_spec, h_load_spec, ?_⟩
  -- The equality needs associativity manipulation
  simp only [add_assoc]

/--
Formal circuit for the execution bundle.

Uses `GeneralFormalCircuitChangingMultiset` so that `weakenSpec` can be applied
without issues (since `GeneralFormalCircuit.Completeness` doesn't depend on Spec).
-/
def circuit
    (capacities : InstructionCapacities)
    {programSize : ℕ} [NeZero programSize] (program : Fin programSize → (F p)) (h_programSize : programSize < p)
    {memorySize : ℕ} [NeZero memorySize] (memory : Fin memorySize → (F p)) (h_memorySize : memorySize < p) :
    GeneralFormalCircuitChangingMultiset (F p) (ExecutionCircuitInput capacities) unit := {
  elaborated := elaborated capacities program h_programSize memory h_memorySize
  Assumptions := Assumptions capacities (programSize := programSize)
  Spec := CircuitSpec capacities program memory
  soundness := circuit_soundness capacities program h_programSize memory h_memorySize
  completeness := by sorry
}

end Examples.PicoCairoMultiplicity.ExecutionBundle
