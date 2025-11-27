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

/--
Instruction capacities for the execution bundle.
Groups all instruction type capacities with their NeZero constraints.
-/
structure InstructionCapacities where
  addCapacity : ℕ
  mulCapacity : ℕ
  storeStateCapacity : ℕ
  loadStateCapacity : ℕ
  addCapacity_nz : NeZero addCapacity
  mulCapacity_nz : NeZero mulCapacity
  storeStateCapacity_nz : NeZero storeStateCapacity
  loadStateCapacity_nz : NeZero loadStateCapacity

instance (capacities : InstructionCapacities) : NeZero capacities.addCapacity := capacities.addCapacity_nz
instance (capacities : InstructionCapacities) : NeZero capacities.mulCapacity := capacities.mulCapacity_nz
instance (capacities : InstructionCapacities) : NeZero capacities.storeStateCapacity := capacities.storeStateCapacity_nz
instance (capacities : InstructionCapacities) : NeZero capacities.loadStateCapacity := capacities.loadStateCapacity_nz

/--
Bundled instruction inputs for all instruction types.
Groups the input vectors for ADD, MUL, StoreState, and LoadState instructions.
-/
structure BundledInstructionInputs (capacities : InstructionCapacities) (F : Type) where
  addInputs : ProvableVector InstructionStepInput capacities.addCapacity F
  mulInputs : ProvableVector InstructionStepInput capacities.mulCapacity F
  storeStateInputs : ProvableVector InstructionStepInput capacities.storeStateCapacity F
  loadStateInputs : ProvableVector InstructionStepInput capacities.loadStateCapacity F

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

instance (capacities : InstructionCapacities) : NonEmptyProvableType (BundledInstructionInputs capacities) where
  nonempty := by
    simp only [size, circuit_norm]
    simp only [List.sum_cons, List.sum_nil, add_zero, Nat.reduceAdd, gt_iff_lt, add_pos_iff,
      Nat.ofNat_pos, mul_pos_iff_of_pos_right]
    have : NeZero capacities.addCapacity := inferInstance
    rcases this
    omega

/--
Main execution bundle that combines all instruction type bundles.
Includes ADD, MUL, StoreState, and LoadState bundles.
-/
def main
    (capacities : InstructionCapacities)
    {programSize : ℕ} [NeZero programSize] (program : Fin programSize → (F p)) (h_programSize : programSize < p)
    {memorySize : ℕ} [NeZero memorySize] (memory : Fin memorySize → (F p)) (h_memorySize : memorySize < p)
    (inputs : Var (BundledInstructionInputs capacities) (F p)) :
    Circuit (F p) Unit := do

  -- Execute ADD instruction bundle
  (AddInstruction.Bundle.circuit capacities.addCapacity program h_programSize memory h_memorySize) inputs.addInputs

  -- Execute MUL instruction bundle
  (MulInstruction.Bundle.circuit capacities.mulCapacity program h_programSize memory h_memorySize) inputs.mulInputs

  -- Execute StoreState instruction bundle
  (StoreStateInstruction.Bundle.circuit capacities.storeStateCapacity program h_programSize memory h_memorySize) inputs.storeStateInputs

  -- Execute LoadState instruction bundle
  (LoadStateInstruction.Bundle.circuit capacities.loadStateCapacity program h_programSize memory h_memorySize) inputs.loadStateInputs

/--
Elaborated circuit for the execution bundle.
The localAdds are the sum of adds from all instruction bundles.
-/
def elaborated
    (capacities : InstructionCapacities)
    {programSize : ℕ} [NeZero programSize] (program : Fin programSize → (F p)) (h_programSize : programSize < p)
    {memorySize : ℕ} [NeZero memorySize] (memory : Fin memorySize → (F p)) (h_memorySize : memorySize < p) :
    ElaboratedCircuit (F p) (BundledInstructionInputs capacities) unit where
  main := main capacities program h_programSize memory h_memorySize
  localLength _ :=
    capacities.addCapacity * 27 +
    capacities.mulCapacity * 27 +
    capacities.storeStateCapacity * 27 +
    capacities.loadStateCapacity * 27
  localLength_eq := by
    intros input offset
    simp only [circuit_norm, main]
    simp only [AddInstruction.Bundle.circuit, AddInstruction.Bundle.elaborated]
    simp only [MulInstruction.Bundle.circuit, MulInstruction.Bundle.elaborated]
    simp only [StoreStateInstruction.Bundle.circuit, StoreStateInstruction.Bundle.elaborated]
    simp only [LoadStateInstruction.Bundle.circuit, LoadStateInstruction.Bundle.elaborated]
    omega
  output _ _ := ()
  localAdds inputs env offset :=
    (AddInstruction.Bundle.elaborated capacities.addCapacity program h_programSize memory h_memorySize).localAdds
      inputs.addInputs env offset +
    (MulInstruction.Bundle.elaborated capacities.mulCapacity program h_programSize memory h_memorySize).localAdds
      inputs.mulInputs env (offset + capacities.addCapacity * 27) +
    (StoreStateInstruction.Bundle.elaborated capacities.storeStateCapacity program h_programSize memory h_memorySize).localAdds
      inputs.storeStateInputs env (offset + capacities.addCapacity * 27 + capacities.mulCapacity * 27) +
    (LoadStateInstruction.Bundle.elaborated capacities.loadStateCapacity program h_programSize memory h_memorySize).localAdds
      inputs.loadStateInputs env (offset + capacities.addCapacity * 27 + capacities.mulCapacity * 27 + capacities.storeStateCapacity * 27)
  localAdds_eq := by
    intros inputs env offset
    simp only [main, circuit_norm]
    -- Use toSubcircuit_localAdds to relate subcircuit localAdds to bundle localAdds
    simp only [Operations.collectAdds, FormalAssertionChangingMultiset.toSubcircuit_localAdds,
      add_zero]
    -- Now we have the bundle's localAdds on both sides
    simp only [AddInstruction.Bundle.circuit, MulInstruction.Bundle.circuit,
      StoreStateInstruction.Bundle.circuit, LoadStateInstruction.Bundle.circuit,
      AddInstruction.Bundle.elaborated, MulInstruction.Bundle.elaborated,
      StoreStateInstruction.Bundle.elaborated, LoadStateInstruction.Bundle.elaborated]
    -- LHS uses + while RHS uses ++, which are the same for InteractionDelta
    simp only [← InteractionDelta.add_eq_append, InteractionDelta.toFinsupp_add, add_assoc]
  subcircuitsConsistent := by
    intros inputs offset
    simp only [main, circuit_norm]
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
    (inputs : BundledInstructionInputs capacities (F p)) : Prop :=
  AddInstruction.Bundle.Assumptions capacities.addCapacity (programSize := programSize) inputs.addInputs ∧
  MulInstruction.Bundle.Assumptions capacities.mulCapacity (programSize := programSize) inputs.mulInputs ∧
  StoreStateInstruction.Bundle.Assumptions capacities.storeStateCapacity (programSize := programSize) inputs.storeStateInputs ∧
  LoadStateInstruction.Bundle.Assumptions capacities.loadStateCapacity (programSize := programSize) inputs.loadStateInputs

/--
Spec for the execution bundle: each instruction bundle must satisfy its spec,
and the local adds are the sum of all bundle adds.
-/
def Spec
    (capacities : InstructionCapacities)
    {programSize : ℕ} [NeZero programSize] (program : Fin programSize → (F p))
    {memorySize : ℕ} [NeZero memorySize] (memory : Fin memorySize → (F p))
    (inputs : BundledInstructionInputs capacities (F p))
    (adds : InteractionDelta (F p)) : Prop :=
  ∃ (addAdds mulAdds storeStateAdds loadStateAdds : InteractionDelta (F p)),
    AddInstruction.Bundle.Spec capacities.addCapacity program memory inputs.addInputs addAdds ∧
    MulInstruction.Bundle.Spec capacities.mulCapacity program memory inputs.mulInputs mulAdds ∧
    StoreStateInstruction.Bundle.Spec capacities.storeStateCapacity program memory inputs.storeStateInputs storeStateAdds ∧
    LoadStateInstruction.Bundle.Spec capacities.loadStateCapacity program memory inputs.loadStateInputs loadStateAdds ∧
    adds = addAdds + mulAdds + storeStateAdds + loadStateAdds

/--
Formal circuit for the execution bundle.
-/
def circuit
    (capacities : InstructionCapacities)
    {programSize : ℕ} [NeZero programSize] (program : Fin programSize → (F p)) (h_programSize : programSize < p)
    {memorySize : ℕ} [NeZero memorySize] (memory : Fin memorySize → (F p)) (h_memorySize : memorySize < p) :
    FormalAssertionChangingMultiset (F p) (BundledInstructionInputs capacities) where
  elaborated := elaborated capacities program h_programSize memory h_memorySize
  Assumptions := Assumptions capacities (programSize := programSize)
  Spec := Spec capacities program memory
  soundness := by
    circuit_proof_start
    -- Extract eval equalities from h_input
    have h_eval_add : eval env input_var.addInputs = input.addInputs := by
      have := congrArg BundledInstructionInputs.addInputs h_input; simp at this; exact this
    have h_eval_mul : eval env input_var.mulInputs = input.mulInputs := by
      have := congrArg BundledInstructionInputs.mulInputs h_input; simp at this; exact this
    have h_eval_store : eval env input_var.storeStateInputs = input.storeStateInputs := by
      have := congrArg BundledInstructionInputs.storeStateInputs h_input; simp at this; exact this
    have h_eval_load : eval env input_var.loadStateInputs = input.loadStateInputs := by
      have := congrArg BundledInstructionInputs.loadStateInputs h_input; simp at this; exact this
    -- Simplify h_holds to convert .circuit.Assumptions to Bundle.Assumptions etc
    -- and ElaboratedCircuit.localLength to capacity * 27
    simp only [AddInstruction.Bundle.circuit, AddInstruction.Bundle.elaborated,
      MulInstruction.Bundle.circuit, MulInstruction.Bundle.elaborated,
      StoreStateInstruction.Bundle.circuit, StoreStateInstruction.Bundle.elaborated,
      LoadStateInstruction.Bundle.circuit, LoadStateInstruction.Bundle.elaborated,
      ElaboratedCircuit.localLength] at h_holds
    -- Now apply eval equalities to h_holds
    rw [h_eval_add, h_eval_mul, h_eval_store, h_eval_load] at h_holds
    -- Extract the four implications from h_holds
    obtain ⟨h_add_impl, h_mul_impl, h_store_impl, h_load_impl⟩ := h_holds
    -- Extract the four assumptions from h_assumptions
    obtain ⟨h_assump_add, h_assump_mul, h_assump_store, h_assump_load⟩ := h_assumptions
    -- Apply each implication with its corresponding assumption to get the Specs
    have h_add_spec := h_add_impl h_assump_add
    have h_mul_spec := h_mul_impl h_assump_mul
    have h_store_spec := h_store_impl h_assump_store
    have h_load_spec := h_load_impl h_assump_load
    -- Simplify goal to use the same localAdds expressions
    simp only [AddInstruction.Bundle.elaborated, MulInstruction.Bundle.elaborated,
      StoreStateInstruction.Bundle.elaborated, LoadStateInstruction.Bundle.elaborated,
      ElaboratedCircuit.localAdds] at *
    -- Now provide the witnesses and prove the equality
    refine ⟨_, _, _, _, h_add_spec, h_mul_spec, h_store_spec, h_load_spec, ?_⟩
    -- LHS and RHS are now syntactically equal
    rfl
  completeness := by
    sorry

end Examples.PicoCairoMultiplicity.ExecutionBundle
