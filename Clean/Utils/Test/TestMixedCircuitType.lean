import Clean.Circuit

/-!
This regression test covers a mixed `CircuitType` input: one ordinary provable
field and one prover-only field-dependent hint. The important proof ergonomics
are that `circuit_proof_start` should split the `h_input` equality into
field-level facts and use them to rewrite constraints from evaluated vars to
verifier/prover values.
-/

namespace TestMixedCircuitType
variable {F : Type} [Field F]

structure Input (F : Type) where
  x : F
  inverse : UnconstrainedDep field F
deriving CircuitType

def circuit : GeneralFormalCircuit.WithHint F Input field where
  main input := do
    let inverse ← witness input.inverse
    input.x * inverse === 1
    return inverse

  output _ offset := varFromOffset field offset
  localLength _ := 1

  Spec
  | ⟨ (x : F), _ ⟩, (out : F), _ => x * out = 1
  ProverAssumptions
  | ⟨ (x : F), (inverse : F) ⟩, _, _ => x * inverse = 1
  ProverSpec
  | input, out, _ => out = input.inverse

  soundness := by
    circuit_proof_start
    -- Regression checks for the intended post-`circuit_proof_start` shape:
    -- the high-level verifier input is gone, and the constraints mention `input_x`.
    fail_if_success (exact input)
    guard_hyp h_input :
      input_var.x.eval env = input_x ∧ () = input_inverse
    exact h_holds

  completeness := by
    circuit_proof_start
    -- The prover-side equality should also be fieldwise; in particular the
    -- prover-only hint is connected to the generated witness by `h_env`.
    fail_if_success (exact input)
    guard_hyp h_input :
      input_var.x.eval env.toEnvironment = input_x ∧ input_var.inverse env = input_inverse
    refine ⟨ ?_, h_env ⟩
    rwa [h_env]

end TestMixedCircuitType
