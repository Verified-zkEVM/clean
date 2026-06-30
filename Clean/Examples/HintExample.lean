/-
Example: Using prover hints in a `GeneralFormalCircuit.WithHint` under the new
`CircuitType`-based API.

`witnessBool` witnesses a field element (1 if the hint returns true, 0 otherwise),
and constrains it to be boolean.

`andBool` uses `witnessBool` as a subcircuit.
-/
import Clean.Circuit
import Clean.Gadgets.Boolean
import Clean.Types.U32

variable {p : ℕ} [Fact p.Prime] [Fact (p > 2)]

namespace Examples.HintExample

/--
  A circuit that witnesses a boolean field element using a prover hint.

  The hint callback tells the prover which boolean value to witness.
  The circuit constrains the output to be boolean (0 or 1).
-/
def witnessBool : GeneralFormalCircuit.WithHint (F p) UnconstrainedBool field where
  main (hint : Witgen.M _ _) := do
    -- TODO WITGENIR we should be able to define prover hints written using IR
    -- and this example should use that
    let b ← witnessProgram do
      let b ← hint
      return .ite b 1 0
    assertBool b
    return b

  Spec (_ : Unit) (output : F p) _ := IsBool output

  ProverSpec (hint : Bool) (b : F p) _ := b = if hint then 1 else 0

  soundness := by
    circuit_proof_all [assertBool, IsBool.iff_mul_sub_one, sub_eq_add_neg]

  completeness := by
    circuit_proof_start [assertBool, IsBool.iff_mul_sub_one, sub_eq_add_neg]
    cases input <;> simp_all

structure Input (F : Type) where
  x : F
  y : F
deriving ProvableStruct

/--
  A circuit that computes the AND of two boolean inputs.

  This is a plain `FormalCircuit` (no hint input). It creates the hint
  internally from its inputs and passes it to `witnessBool`.
-/
def booleanAnd : FormalCircuit (F p) Input field where
  main | ⟨x, y⟩ => do
    -- Use witnessBool as a subcircuit with a hint synthesized from the inputs
    let z ← witnessBool <| unconstrainedBool (pure ((x =? 1) &&& (y =? 1)))
    -- Constrain result = x * y (multiplication is AND for booleans)
    z === x * y
    return z

  Assumptions | ⟨x, y⟩ => IsBool x ∧ IsBool y
  Spec | ⟨x, y⟩, z => IsBool z ∧ z.val = x.val &&& y.val

  soundness := by
    circuit_proof_start [witnessBool, assertBool, IsBool]
    rcases h_holds.1 with z | notz
    · simp_all
      cases h_holds <;> simp_all
    · grind

  completeness := by
    circuit_proof_start [witnessBool, assertBool, IsBool, ZMod.val_one]
    simp_all
    rcases h_assumptions with ⟨ x | notx, y | noty ⟩
      <;> simp_all [ZMod.val_one]

structure MixedInput (F : Type) where
  someElement : U32 F
  someHint : UnconstrainedNative Bool F
deriving CircuitType

example (input : MixedInput.Var (F p)) : U32 (Expression (F p)) × (ProverEnvironment (F p) → Bool) :=
  (input.someElement, input.someHint)
example (input : MixedInput.ProverValue (F p)) : U32 (F p) × Bool :=
  (input.someElement, input.someHint)
example (input : MixedInput.Value (F p)) : U32 (F p) × Unit :=
  (input.someElement, input.someHint)

/--
  This captures the field-dependent hint case: the prover-only data mentions the
  circuit field type, so `UnconstrainedNative Bool` is not expressive enough.
-/
structure InputWithFieldHint (F : Type) where
  publicInput : F
  hinted : UnconstrainedDepNative field F
deriving CircuitType

example (input : InputWithFieldHint.Var (F p)) :
    Expression (F p) × (ProverEnvironment (F p) → F p) :=
  (input.publicInput, input.hinted)
example (input : InputWithFieldHint.ProverValue (F p)) : F p × F p :=
  (input.publicInput, input.hinted)
example (input : InputWithFieldHint.Value (F p)) : F p × Unit :=
  (input.publicInput, input.hinted)

example : ProvableType (Value InputWithFieldHint) := inferInstance
end Examples.HintExample
