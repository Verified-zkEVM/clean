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
import Clean.Circuit.Subcircuit
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
    let b ← witnessField fun env => if hint env then (1 : F p) else 0
    assertBool b
    return b

  localLength _ := 1
  output _ i := var ⟨i⟩

  Spec (_ : Unit) (output : F p) _ := IsBool output

  soundness := by
    circuit_proof_all [assertBool, IsBool.iff_mul_sub_one, sub_eq_add_neg]

  completeness := by
    circuit_proof_start [assertBool, IsBool.iff_mul_sub_one, sub_eq_add_neg]
    cases input_var env <;> simp_all

end Examples.HintExample
