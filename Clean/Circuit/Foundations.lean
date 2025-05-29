/-
This file provides a justification for our definitions of `FormalCircuit` and `FormalAssertion`.

In those definitions, we use modified statements for `constraints_hold` and `uses_local_witnesses`,
where subcircuits replace the original statement with a new one that is easier to reason about during proofs.

Here, we prove soundness and completeness using the _original_ statements.

This ensures that the `FormalCircuit` and `FormalAssertion` definitions are not accidentally weaker than they should be.
-/
import Clean.Circuit.Theorems

variable {F: Type} [Field F]
variable {α β: TypeMap} [ProvableType α] [ProvableType β]
open Circuit (constraints_hold)

/--
  Justification for using a modified statement for `constraints_hold`
  in the `FormalCircuit` definition.
-/
theorem FormalCircuit.original_soundness (circuit : FormalCircuit F β α) :
    ∀ (offset : ℕ) env (b_var : Var β F) (b : β F), eval env b_var = b → circuit.assumptions b →
    -- if the constraints hold (original definition)
    constraints_hold env (circuit.main b_var |>.operations offset) →
    -- the spec holds
    let a := eval env (circuit.output b_var offset)
    circuit.spec b a := by

  intro offset env b_var b h_input h_assumptions h_holds
  have h_holds' := Circuit.can_replace_soundness h_holds
  exact circuit.soundness offset env b_var b h_input h_assumptions h_holds'

/--
  Justification for using modified statements for `uses_local_witnesses`
  and `constraints_hold` in the `FormalCircuit` definition.
-/
theorem FormalCircuit.original_completeness (circuit : FormalCircuit F β α) :
    ∀ (offset : ℕ) env (b_var : Var β F) (b : β F), eval env b_var = b → circuit.assumptions b →
    -- if the environment uses default witness generators (original definition)
    env.uses_local_witnesses offset (circuit.main b_var |>.operations offset) →
    -- the constraints hold (original definition)
    constraints_hold env (circuit.main b_var |>.operations offset) := by

  intro offset env b_var b h_input h_assumptions h_env
  apply Circuit.can_replace_completeness (circuit.subcircuits_consistent ..) h_env
  have h_env' := Environment.can_replace_local_witnesses_completeness (circuit.subcircuits_consistent ..) h_env
  exact circuit.completeness offset env b_var h_env' b h_input h_assumptions

/--
  Justification for using a modified statement for `constraints_hold`
  in the `FormalAssertion` definition.
-/
theorem FormalAssertion.original_soundness (circuit : FormalAssertion F β) :
    ∀ (offset : ℕ) env (b_var : Var β F) (b : β F), eval env b_var = b → circuit.assumptions b →
    -- if the constraints hold (original definition)
    constraints_hold env (circuit.main b_var |>.operations offset) →
    -- the spec holds
    circuit.spec b := by

  intro offset env b_var b h_input h_assumptions h_holds
  have h_holds' := Circuit.can_replace_soundness h_holds
  exact circuit.soundness offset env b_var b h_input h_assumptions h_holds'

/--
  Justification for using modified statements for `uses_local_witnesses`
  and `constraints_hold` in the `FormalAssertion` definition.
-/
theorem FormalAssertion.original_completeness (circuit : FormalAssertion F β) :
    ∀ (offset : ℕ) env (b_var : Var β F) (b : β F), eval env b_var = b → circuit.assumptions b →
    -- if the environment uses default witness generators (original definition)
    env.uses_local_witnesses offset (circuit.main b_var |>.operations offset) →
    -- the spec implies that the constraints hold (original definition)
    circuit.spec b → constraints_hold env (circuit.main b_var |>.operations offset) := by

  intro offset env b_var b h_input h_assumptions h_env h_spec
  apply Circuit.can_replace_completeness (circuit.subcircuits_consistent ..) h_env
  have h_env' := Environment.can_replace_local_witnesses_completeness (circuit.subcircuits_consistent ..) h_env
  exact circuit.completeness offset env b_var h_env' b h_input h_assumptions h_spec
