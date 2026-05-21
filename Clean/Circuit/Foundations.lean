/-
This file provides a justification for our definitions of `FormalCircuit` and `FormalAssertion`.

In those definitions, we use modified statements for `ConstraintsHold` and `UsesLocalWitnesses`,
where subcircuits replace the original statement with a new one that is easier to reason about during proofs.

Here, we prove soundness and completeness using the _original_ statements.

This ensures that the `FormalCircuit` and `FormalAssertion` definitions are not accidentally weaker than they should be.
-/
import Clean.Circuit.Formal
import Clean.Circuit.Theorems

variable {F : Type} [Field F]
variable {α β : TypeMap}

namespace GeneralFormalCircuit.WithHint
variable [CircuitType α] [CircuitType β]

/--
  Justification for using a modified statement for `ConstraintsHold`
  in the `GeneralFormalCircuit` definition.
-/
theorem original_soundness (circuit : GeneralFormalCircuit.WithHint F β α) :
    ∀ (offset : ℕ) (env : Environment F) (b_var : Var β F),
    let ops := circuit.main b_var |>.operations offset;
    let input := eval env b_var;
    let output := eval env (circuit.output b_var offset);
    circuit.Assumptions input env.data →
    -- if the constraints hold (original definition) and guarantees hold
    ops.ConstraintsHold env → ops.FullGuarantees env →
    -- the spec and requirements hold
    circuit.Spec input output env.data ∧ ops.FullRequirements env := by
  intro offset env b_var ops input output h_assumptions h_constraints h_full_guarantees
  have h_soundness_input : ConstraintsHold.Soundness env ops :=
    Circuit.can_replace_soundness h_constraints h_full_guarantees
  have ⟨ h_spec, h_requirements ⟩ :=
    circuit.soundness offset env b_var input rfl h_assumptions h_soundness_input
  use h_spec
  exact Circuit.requirements_toFlat_of_soundness (circuit.subcircuitChannelsLawful b_var offset)
    h_constraints h_full_guarantees h_requirements

/--
  Justification for using modified statements for `UsesLocalWitnesses`
  and `ConstraintsHold` in the `GeneralFormalCircuit` definition.
-/
theorem original_completeness (circuit : GeneralFormalCircuit.WithHint F β α) :
    ∀ (offset : ℕ) (env : ProverEnvironment F) (b_var : Var β F),
    let ops := circuit.main b_var |>.operations offset;
    let input := eval env b_var;
    -- if the environment uses default witness generators (original definition)
    env.UsesLocalWitnesses offset ops →
    circuit.ProverAssumptions input env.data env.hint →
    -- the constraints and guarantees hold (original definition)
    ops.ConstraintsHold env ∧ ops.FullGuarantees env ∧
    -- and the prover spec holds
    circuit.ProverSpec input (eval env (circuit.output b_var offset)) env.hint := by
  intro offset env b_var ops input h_env h_assumptions
  have h_consistent := circuit.subcircuitsConsistent b_var offset
  have h_env' := env.can_replace_usesLocalWitnessesCompleteness h_consistent h_env
  have h_completeness := circuit.completeness offset env b_var h_env' input rfl h_assumptions
  have h_constraints_and_guarantees :=
    Circuit.can_replace_completeness_and_guarantees h_consistent h_env h_completeness.1
  exact ⟨h_constraints_and_guarantees.1, h_constraints_and_guarantees.2, h_completeness.2⟩
end GeneralFormalCircuit.WithHint

variable [ProvableType α] [ProvableType β]

/--
  Justification for using a modified statement for `ConstraintsHold`
  in the `FormalCircuit` definition.
-/
theorem FormalCircuit.original_soundness (circuit : FormalCircuit F β α) :
    ∀ (offset : ℕ) (env : Environment F) (b_var : Var β F) (b : β F),
    eval env b_var = b → circuit.Assumptions b →
    -- if the constraints and guarantees hold (original definition)
    Operations.ConstraintsHold env (circuit.main b_var |>.operations offset) →
    Operations.FullGuarantees env (circuit.main b_var |>.operations offset) →
    -- the spec and requirements hold
    let a := eval env (circuit.output b_var offset)
    circuit.Spec b a ∧ Operations.FullRequirements env (circuit.main b_var |>.operations offset) := by

  intro offset env b_var b h_input h_assumptions h_constraints h_guarantees
  have h_holds' : ConstraintsHold.Soundness env (circuit.main b_var |>.operations offset) :=
    Circuit.can_replace_soundness h_constraints h_guarantees
  have h_soundness := circuit.soundness offset env b_var b h_input h_assumptions h_holds'
  exact ⟨h_soundness.1,
    Circuit.requirements_toFlat_of_soundness (circuit.subcircuitChannelsLawful b_var offset)
      h_constraints h_guarantees h_soundness.2⟩

/--
  Justification for using modified statements for `UsesLocalWitnesses`
  and `ConstraintsHold` in the `FormalCircuit` definition.
-/
theorem FormalCircuit.original_completeness (circuit : FormalCircuit F β α) :
    ∀ (offset : ℕ) (env : ProverEnvironment F) (b_var : Var β F) (b : β F),
    eval env b_var = b → circuit.Assumptions b →
    -- if the environment uses default witness generators (original definition)
    env.UsesLocalWitnesses offset (circuit.main b_var |>.operations offset) →
    -- the constraints and guarantees hold (original definition)
    Operations.ConstraintsHold env (circuit.main b_var |>.operations offset) ∧
    Operations.FullGuarantees env (circuit.main b_var |>.operations offset) := by

  intro offset env b_var b h_input h_assumptions h_env
  have h_env' := ProverEnvironment.can_replace_usesLocalWitnessesCompleteness (circuit.subcircuitsConsistent ..) h_env
  have h_compl_inter := circuit.completeness offset env b_var h_env' b h_input h_assumptions
  exact Circuit.can_replace_completeness_and_guarantees (circuit.subcircuitsConsistent ..) h_env h_compl_inter

/--
  Justification for using a modified statement for `ConstraintsHold`
  in the `FormalAssertion` definition.
-/
theorem FormalAssertion.original_soundness (circuit : FormalAssertion F β) :
    ∀ (offset : ℕ) (env : Environment F) (b_var : Var β F) (b : β F),
    eval env b_var = b → circuit.Assumptions b →
    -- if the constraints and guarantees hold (original definition)
    Operations.ConstraintsHold env (circuit.main b_var |>.operations offset) →
    Operations.FullGuarantees env (circuit.main b_var |>.operations offset) →
    -- the spec and requirements hold
    circuit.Spec b ∧ Operations.FullRequirements env (circuit.main b_var |>.operations offset) := by

  intro offset env b_var b h_input h_assumptions h_constraints h_guarantees
  have h_holds' : ConstraintsHold.Soundness env (circuit.main b_var |>.operations offset) :=
    Circuit.can_replace_soundness h_constraints h_guarantees
  have h_soundness := circuit.soundness offset env b_var b h_input h_assumptions h_holds'
  exact ⟨h_soundness.1,
    Circuit.requirements_toFlat_of_soundness (circuit.subcircuitChannelsLawful b_var offset)
      h_constraints h_guarantees h_soundness.2⟩

/--
  Justification for using modified statements for `UsesLocalWitnesses`
  and `ConstraintsHold` in the `FormalAssertion` definition.
-/
theorem FormalAssertion.original_completeness (circuit : FormalAssertion F β) :
    ∀ (offset : ℕ) (env : ProverEnvironment F) (b_var : Var β F) (b : β F),
    eval env b_var = b → circuit.Assumptions b →
    -- if the environment uses default witness generators (original definition)
    env.UsesLocalWitnesses offset (circuit.main b_var |>.operations offset) →
    -- the spec implies that the constraints hold (original definition)
    circuit.Spec b →
    Operations.ConstraintsHold env (circuit.main b_var |>.operations offset) ∧
    Operations.FullGuarantees env (circuit.main b_var |>.operations offset) := by

  intro offset env b_var b h_input h_assumptions h_env h_spec
  have h_env' := ProverEnvironment.can_replace_usesLocalWitnessesCompleteness (circuit.subcircuitsConsistent ..) h_env
  have h_compl_inter := circuit.completeness offset env b_var h_env' b h_input h_assumptions h_spec
  exact Circuit.can_replace_completeness_and_guarantees (circuit.subcircuitsConsistent ..) h_env h_compl_inter

/--
  Target foundational theorem for general circuits with interactions:
  full constraints + full guarantees imply spec + full requirements.
-/
theorem GeneralFormalCircuit.original_full_soundness
    (circuit : GeneralFormalCircuit F β α) :
    ∀ (offset : ℕ) env (input_var : Var β F),
    let ops := circuit.main input_var |>.operations offset;
    let input := eval env input_var;
    let output := eval env (circuit.output input_var offset);
    circuit.Assumptions input env.data →
    ops.ConstraintsHold env → ops.FullGuarantees env →
    circuit.Spec input output env.data ∧ ops.FullRequirements env := by
  intro offset env input_var ops input output h_assumptions h_constraints h_full_guarantees
  have h_soundness_input : ConstraintsHold.Soundness env ops :=
    Circuit.can_replace_soundness h_constraints h_full_guarantees
  have ⟨ h_spec, h_requirements ⟩ :=
    circuit.soundness offset env input_var input rfl h_assumptions h_soundness_input
  use h_spec
  exact Circuit.requirements_toFlat_of_soundness (circuit.subcircuitChannelsLawful input_var offset)
    h_constraints h_full_guarantees h_requirements

/--
  Foundational completeness theorem for general circuits with interactions:
  assumptions + local witness usage imply original constraints and full guarantees.
-/
theorem GeneralFormalCircuit.original_full_completeness
    (circuit : GeneralFormalCircuit F β α) :
    ∀ (offset : ℕ) (env : ProverEnvironment F) (input_var : Var β F),
    let ops := circuit.main input_var |>.operations offset;
    let input := eval env input_var;
    env.UsesLocalWitnesses offset ops → circuit.ProverAssumptions input env.data env.hint →
    ops.ConstraintsHold env ∧ ops.FullGuarantees env := by
  intro offset env input_var ops input h_env h_assumptions
  have h_consistent := circuit.subcircuitsConsistent input_var offset
  apply Circuit.can_replace_completeness_and_guarantees h_consistent h_env
  have h_env' := env.can_replace_usesLocalWitnessesCompleteness h_consistent h_env
  exact (circuit.completeness offset env input_var h_env' input rfl h_assumptions).1
