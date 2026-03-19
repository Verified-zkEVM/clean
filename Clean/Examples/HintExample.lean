/-
  Example: Using prover hints in a GeneralFormalCircuit.

  This file demonstrates how to use the `Hint` parameter to pass prover-side
  information into a circuit's witness generation.

  `witnessBool` takes a hint callback that returns a `Bool`, witnesses a field
  element (1 if true, 0 if false), and constrains it to be boolean.

  `witnessAnd` demonstrates a circuit that uses a hint to witness the AND of
  two boolean inputs, constraining the result via `result = x * y`.
-/
import Clean.Circuit.Subcircuit
import Clean.Gadgets.Boolean
import Clean.Gadgets.Equality

variable {p : ℕ} [Fact p.Prime] [Fact (p > 2)]

namespace Examples.HintExample

/--
  A circuit that witnesses a boolean field element using a prover hint.

  The hint callback tells the prover which boolean value to witness.
  The circuit constrains the output to be boolean (0 or 1).
-/
def witnessBool : GeneralFormalCircuit (F p) unit field Bool where
  main _ hint := do
    let b ← witness fun env => if hint env then (1 : F p) else 0
    assertBool b
    return b

  localLength _ := 1
  output _ i := var ⟨i⟩

  Assumptions _ _ _ := True
  Spec _ (output : F p) _ := IsBool output

  soundness := by
    circuit_proof_all [assertBool, IsBool.iff_mul_sub_one, sub_eq_add_neg]

  completeness := by
    circuit_proof_start [assertBool, IsBool.iff_mul_sub_one, sub_eq_add_neg]
    cases hint env <;> simp_all

/--
  A circuit that computes the AND of two boolean inputs.

  This is a plain `FormalCircuit` (no hint parameter). It creates the hint
  internally from its inputs and passes it to `witnessBool` via
  `subcircuitWithAssertion`. This demonstrates how a regular circuit can
  compose a hint-aware subcircuit by constructing the hint at the call site.
-/
def booleanAnd : FormalCircuit (F p) (ProvablePair field field) field where
  main | (x, y) => do
    -- Use witnessBool as a subcircuit with a hint
    let result ← subcircuitWithAssertion witnessBool () fun env => x.eval env = 1 ∧ y.eval env = 1
    -- Constrain result = x * y (multiplication is AND for booleans)
    result === x * y
    return result

  localLength _ := 1
  output _ i := var ⟨i⟩

  Assumptions (input : F p × F p) := IsBool input.1 ∧ IsBool input.2

  Spec (input : F p × F p) (output : F p) := output = input.1 * input.2

  soundness := by
    circuit_proof_start [witnessBool]
    sorry

  completeness := by
    circuit_proof_start [witnessBool]
    sorry

end Examples.HintExample
