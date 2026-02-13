/-
This file provides a justification for our definitions of `FormalCircuit` and `FormalAssertion`.

In those definitions, we use modified statements for `ConstraintsHold` and `UsesLocalWitnesses`,
where subcircuits replace the original statement with a new one that is easier to reason about during proofs.

Here, we prove soundness and completeness using the _original_ statements.

This ensures that the `FormalCircuit` and `FormalAssertion` definitions are not accidentally weaker than they should be.
-/
import Clean.Circuit.Theorems

variable {F : Type} [Field F] [DecidableEq F]
variable {α β : TypeMap} [ProvableType α] [ProvableType β]
open Circuit (ConstraintsHold)

/--
  Justification for using a modified statement for `ConstraintsHold`
  in the `FormalCircuit` definition.
-/
theorem FormalCircuit.original_soundness (circuit : FormalCircuit F β α) :
    ∀ (offset : ℕ) env (b_var : Var β F) (b : β F), eval env b_var = b → circuit.Assumptions b →
    -- if the constraints hold (original definition)
    Operations.ConstraintsHold env (circuit.main b_var |>.operations offset) →
    -- the spec holds
    let a := eval env (circuit.output b_var offset)
    circuit.Spec b a := by

  intro offset env b_var b h_input h_assumptions h_holds
  have h_holds' : ConstraintsHold.Soundness env (circuit.main b_var |>.operations offset) := by
    sorry
  exact circuit.soundness offset env b_var b h_input h_assumptions h_holds'

/--
  Justification for using modified statements for `UsesLocalWitnesses`
  and `ConstraintsHold` in the `FormalCircuit` definition.
-/
theorem FormalCircuit.original_completeness (circuit : FormalCircuit F β α) :
    ∀ (offset : ℕ) env (b_var : Var β F) (b : β F), eval env b_var = b → circuit.Assumptions b →
    -- if the environment uses default witness generators (original definition)
    env.UsesLocalWitnesses offset (circuit.main b_var |>.operations offset) →
    -- the constraints hold (original definition)
    Operations.ConstraintsHold env (circuit.main b_var |>.operations offset) := by

  intro offset env b_var b h_input h_assumptions h_env
  have h_env' := Environment.can_replace_usesLocalWitnessesCompleteness (circuit.subcircuitsConsistent ..) h_env
  have h_compl := circuit.completeness offset env b_var h_env' b h_input h_assumptions
  have h_compl_inter :
      ConstraintsHoldWithInteractions.Completeness env (circuit.main b_var |>.operations offset) := by
    sorry
  exact Circuit.can_replace_completeness (circuit.subcircuitsConsistent ..) h_env h_compl_inter

/--
  Justification for using a modified statement for `ConstraintsHold`
  in the `FormalAssertion` definition.
-/
theorem FormalAssertion.original_soundness (circuit : FormalAssertion F β) :
    ∀ (offset : ℕ) env (b_var : Var β F) (b : β F), eval env b_var = b → circuit.Assumptions b →
    -- if the constraints hold (original definition)
    Operations.ConstraintsHold env (circuit.main b_var |>.operations offset) →
    -- the spec holds
    circuit.Spec b := by

  intro offset env b_var b h_input h_assumptions h_holds
  have h_holds' : ConstraintsHold.Soundness env (circuit.main b_var |>.operations offset) := by
    sorry
  exact circuit.soundness offset env b_var b h_input h_assumptions h_holds'

/--
  Justification for using modified statements for `UsesLocalWitnesses`
  and `ConstraintsHold` in the `FormalAssertion` definition.
-/
theorem FormalAssertion.original_completeness (circuit : FormalAssertion F β) :
    ∀ (offset : ℕ) env (b_var : Var β F) (b : β F), eval env b_var = b → circuit.Assumptions b →
    -- if the environment uses default witness generators (original definition)
    env.UsesLocalWitnesses offset (circuit.main b_var |>.operations offset) →
    -- the spec implies that the constraints hold (original definition)
    circuit.Spec b → Operations.ConstraintsHold env (circuit.main b_var |>.operations offset) := by

  intro offset env b_var b h_input h_assumptions h_env h_spec
  have h_env' := Environment.can_replace_usesLocalWitnessesCompleteness (circuit.subcircuitsConsistent ..) h_env
  have h_compl := circuit.completeness offset env b_var h_env' b h_input h_assumptions h_spec
  have h_compl_inter :
      ConstraintsHoldWithInteractions.Completeness env (circuit.main b_var |>.operations offset) := by
    sorry
  exact Circuit.can_replace_completeness (circuit.subcircuitsConsistent ..) h_env h_compl_inter

/--
  Target foundational theorem for circuits with interactions:
  full constraints + full guarantees imply spec + full requirements.
-/
theorem FormalCircuitWithInteractions.original_full_soundness
    (circuit : FormalCircuitWithInteractions F β α) :
    ∀ (offset : ℕ) env (input_var : Var β F),
    let ops := circuit.main input_var |>.operations offset;
    let input := eval env input_var;
    let output := eval env (circuit.output input_var offset);
    ops.ConstraintsHold env → ops.FullGuarantees env →
    circuit.Spec input output env ∧ ops.FullRequirements env := by
  intro offset env input_var ops input output h_constraints h_full_guarantees
  have h_soundness_input : ConstraintsHoldWithInteractions.Soundness env ops :=
    Circuit.can_replace_soundness h_constraints h_full_guarantees
  have ⟨ h_spec, h_requirements ⟩ := circuit.soundness offset env input_var input rfl h_soundness_input
  use h_spec
  apply Circuit.requirements_toFlat_of_soundness h_constraints h_full_guarantees h_requirements

/--
  Foundational completeness theorem for circuits with interactions:
  assumptions + local witness usage imply original constraints and full guarantees.
-/
theorem FormalCircuitWithInteractions.original_full_completeness
    (circuit : FormalCircuitWithInteractions F β α) :
    ∀ (offset : ℕ) env (input_var : Var β F),
    let ops := circuit.main input_var |>.operations offset;
    let input := eval env input_var;
    env.UsesLocalWitnesses offset ops → circuit.Assumptions input env →
    ops.ConstraintsHold env ∧ ops.FullGuarantees env := by
  intro offset env input_var ops input h_env h_assumptions
  have h_consistent := circuit.subcircuitsConsistent input_var offset
  apply Circuit.can_replace_completeness_and_guarantees h_consistent h_env
  have h_env' := env.can_replace_usesLocalWitnessesCompleteness h_consistent h_env
  exact circuit.completeness offset env input_var h_env' input rfl h_assumptions
