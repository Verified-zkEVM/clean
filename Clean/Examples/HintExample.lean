/-
  Example: Using prover hints in a `GeneralFormalCircuit` under the new
  `CircuitType`-based API.

  The hint is modelled as `Input = Unconstrained Bool`:
    - verifier-view of the input: `Unit` (hints are erased)
    - prover-view of the input: `Bool`
    - variable form: `ProverHint Bool F = ProverEnvironment F → Bool`

  `witnessBool` witnesses a field element (1 if the hint returns true, 0 otherwise),
  and constrains it to be boolean.
-/
import Clean.Circuit
import Clean.Gadgets.Boolean

variable {p : ℕ} [Fact p.Prime] [Fact (p > 2)]

namespace Examples.HintExample

/--
  A circuit that witnesses a boolean field element using a prover hint.

  The hint callback tells the prover which boolean value to witness.
  The circuit constrains the output to be boolean (0 or 1).
-/
def witnessBool : GeneralFormalCircuit (F p) (Unconstrained Bool) field where
  main (hint : ProverEnvironment (F p) → Bool) := do
    let b ← witness fun env => if hint env then 1 else 0
    assertBool b
    return b

  localLength _ := 1
  output _ i := var ⟨i⟩

  Assumptions (_ : Unit) _ := True
  Spec (_ : Unit) (output : F p) _ := IsBool output

  ProverAssumptions (hint : Bool) _ _ := True
  ProverSpec (hint : Bool) (b : F p) _ := b = if hint then 1 else 0

  soundness := by
    circuit_proof_all [assertBool, IsBool.iff_mul_sub_one, sub_eq_add_neg]

  completeness := by
    circuit_proof_start [assertBool, IsBool.iff_mul_sub_one, sub_eq_add_neg]
    cases input_var env <;> simp_all

structure Input (F : Type) where
  x : F
  y : F
deriving ProvableStruct

/--
  A circuit that computes the AND of two boolean inputs.

  This is a plain `FormalCircuit` (no hint input). It creates the hint
  internally from its inputs and passes it to `witnessBool` via
  `subcircuitWithAssertion`.
-/
def booleanAnd : FormalCircuit (F p) Input field where
  main | ⟨x, y⟩ => do
    -- Use witnessBool as a subcircuit with a hint synthesized from the inputs
    let z ← witnessBool fun env => eval env x = 1 ∧ eval env y = 1
    -- Constrain result = x * y (multiplication is AND for booleans)
    z === x * y
    return z

  localLength _ := 1
  output _ i := var ⟨i⟩

  Assumptions | ⟨x, y⟩ => IsBool x ∧ IsBool y
  Spec | ⟨x, y⟩, output => output = x * y

  soundness := by
    circuit_proof_start [witnessBool, assertBool]
    simp_all [circuit_norm]

  completeness := by
    circuit_proof_start [witnessBool, assertBool, IsBool]
    simp_all
    rcases h_assumptions with ⟨ x | notx, y | noty ⟩
      <;> simp_all


end Examples.HintExample
