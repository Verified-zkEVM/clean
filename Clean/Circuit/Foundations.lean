/-
This file provides a justification for our definitions of `FormalCircuit` and `FormalAssertion`.

In those definitions, we use modified statements for `ConstraintsHold` and `UsesLocalWitnesses`,
where subcircuits replace the original statement with a new one that is easier to reason about during proofs.

Here, we prove soundness and completeness using the _original_ statements.

This ensures that the `FormalCircuit` and `FormalAssertion` definitions are not accidentally weaker than they should be.
-/
import Clean.Circuit.Theorems

open Circuit (ConstraintsHold)

variable {F : Type} [Field F]
variable {α β : TypeMap}

namespace GeneralFormalCircuit.WithHint
variable [CircuitType α] [CircuitType β]

/--
  Justification for using a modified statement for `ConstraintsHold`
  in the `FormalCircuit` definition.
-/
theorem original_soundness (circuit : GeneralFormalCircuit.WithHint F β α) :
    ∀ (offset : ℕ) (env : Environment F) (b_var : Var β F),
    circuit.Assumptions (eval env b_var) env.data →
    -- if the constraints hold (original definition)
    ConstraintsHold env (circuit.main b_var |>.operations offset) →
    -- the spec holds
    circuit.Spec (eval env b_var) (eval env (circuit.output b_var offset)) env.data := by
  intro offset env b_var h_assumptions h_holds
  apply circuit.soundness offset env b_var _ rfl h_assumptions
  exact Circuit.can_replace_soundness h_holds

/--
  Justification for using modified statements for `UsesLocalWitnesses`
  and `ConstraintsHold` in the `FormalCircuit` definition.
-/
theorem original_completeness (circuit : GeneralFormalCircuit.WithHint F β α) :
    ∀ (offset : ℕ) (env : ProverEnvironment F) (b_var : Var β F),
    circuit.ProverAssumptions (eval env b_var) env.data env.hint →
    -- if the environment uses default witness generators (original definition)
    env.UsesLocalWitnesses offset (circuit.main b_var |>.operations offset) →
    -- the constraints hold (original definition)
    ConstraintsHold env (circuit.main b_var |>.operations offset) ∧
    -- and the prover spec holds
    circuit.ProverSpec (eval env b_var) (eval env (circuit.output b_var offset)) env.hint := by
  intro offset env b_var h_assumptions h_env
  have h_env' := ProverEnvironment.can_replace_usesLocalWitnessesCompleteness (circuit.subcircuitsConsistent ..) h_env
  have completeness := circuit.completeness offset env b_var h_env' _ rfl h_assumptions
  constructor
  · apply Circuit.can_replace_completeness (circuit.subcircuitsConsistent ..) h_env
    exact completeness.1
  · exact completeness.2
end GeneralFormalCircuit.WithHint

variable [ProvableType α] [ProvableType β]

/--
  Justification for using a modified statement for `ConstraintsHold`
  in the `FormalCircuit` definition.
-/
theorem FormalCircuit.original_soundness (circuit : FormalCircuit F β α) :
    ∀ (offset : ℕ) (env : Environment F) (b_var : Var β F) (b : β F),
    eval env b_var = b → circuit.Assumptions b →
    -- if the constraints hold (original definition)
    ConstraintsHold env (circuit.main b_var |>.operations offset) →
    -- the spec holds
    let a := eval env (circuit.output b_var offset)
    circuit.Spec b a := by

  intro offset env b_var b h_input h_assumptions h_holds
  have h_holds' := Circuit.can_replace_soundness h_holds
  exact circuit.soundness offset env b_var b h_input h_assumptions h_holds'

/--
  Justification for using modified statements for `UsesLocalWitnesses`
  and `ConstraintsHold` in the `FormalCircuit` definition.
-/
theorem FormalCircuit.original_completeness (circuit : FormalCircuit F β α) :
    ∀ (offset : ℕ) (env : ProverEnvironment F) (b_var : Var β F) (b : β F),
    eval env b_var = b → circuit.Assumptions b →
    -- if the environment uses default witness generators (original definition)
    env.UsesLocalWitnesses offset (circuit.main b_var |>.operations offset) →
    -- the constraints hold (original definition)
    ConstraintsHold env (circuit.main b_var |>.operations offset) := by

  intro offset env b_var b h_input h_assumptions h_env
  apply Circuit.can_replace_completeness (circuit.subcircuitsConsistent ..) h_env
  have h_env' := ProverEnvironment.can_replace_usesLocalWitnessesCompleteness (circuit.subcircuitsConsistent ..) h_env
  exact circuit.completeness offset env b_var h_env' b h_input h_assumptions

/--
  Justification for using a modified statement for `ConstraintsHold`
  in the `FormalAssertion` definition.
-/
theorem FormalAssertion.original_soundness (circuit : FormalAssertion F β) :
    ∀ (offset : ℕ) (env : Environment F) (b_var : Var β F) (b : β F),
    eval env b_var = b → circuit.Assumptions b →
    -- if the constraints hold (original definition)
    ConstraintsHold env (circuit.main b_var |>.operations offset) →
    -- the spec holds
    circuit.Spec b := by

  intro offset env b_var b h_input h_assumptions h_holds
  have h_holds' := Circuit.can_replace_soundness h_holds
  exact circuit.soundness offset env b_var b h_input h_assumptions h_holds'

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
    circuit.Spec b → ConstraintsHold env (circuit.main b_var |>.operations offset) := by

  intro offset env b_var b h_input h_assumptions h_env h_spec
  apply Circuit.can_replace_completeness (circuit.subcircuitsConsistent ..) h_env
  have h_env' := ProverEnvironment.can_replace_usesLocalWitnessesCompleteness (circuit.subcircuitsConsistent ..) h_env
  exact circuit.completeness offset env b_var h_env' b h_input h_assumptions h_spec
