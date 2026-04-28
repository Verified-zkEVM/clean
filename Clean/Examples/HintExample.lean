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
def witnessBool : GeneralFormalCircuit.WithHint (F p) (Unconstrained Bool) field where
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
  internally from its inputs and passes it to `witnessBool`.
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
  Spec | ⟨x, y⟩, z => IsBool z ∧ z.val = x.val &&& y.val

  soundness := by
    circuit_proof_start [witnessBool, assertBool, IsBool]
    rcases h_holds.1 with z | notz
    · simp_all
      cases h_holds <;> simp_all
    · grind

  completeness := by
    circuit_proof_start [witnessBool, assertBool, IsBool]
    simp_all
    rcases h_assumptions with ⟨ x | notx, y | noty ⟩
      <;> simp_all

structure MixedInput (F : Type) where
  someElement : U32 F
  someHint : Unconstrained Bool F
deriving CircuitType

example (input : MixedInput.Var (F p)) : U32 (Expression (F p)) × (ProverEnvironment (F p) → Bool) :=
  (input.someElement, input.someHint)
example (input : MixedInput.ProverValue (F p)) : U32 (F p) × Bool :=
  (input.someElement, input.someHint)
example (input : MixedInput.Value (F p)) : U32 (F p) × Unit :=
  (input.someElement, input.someHint)

/--
The following seems like a cool experiment at first glance.
The main problem is that it's not possible to generate `CircuitBool` values in a circuit based
on prover knowledge, because we don't surface a way to reason about the environment
assuming honest prover witness generation.

For example, it is not possible to implement `HasAssignEq`:
we cannot prove the `isBool` property for the copied variable.

So, as it stands, this pattern is less useful than the code below suggests.
-/
structure CircuitBool (F : Type) where
  bool : F
  isBool [Field F] : IsBool bool
deriving CircuitType

example (input : CircuitBool.Var (F p)) : ∀ env : ProverEnvironment (F p),
    IsBool (eval env input.bool) := by
  intro env; exact input.isBool env

namespace CircuitBool
variable {F : Type} [Field F]

-- this seems generally useful: whenever we allow `eval` to be rewritten to a concrete `CircuitType` instance,
-- we can immediately unfold it with `circuit_norm`!
attribute [circuit_norm] CircuitType.evalVerifier CircuitType.evalProver

-- this seems like useful simp infrastructure for any derived CircuitType
@[circuit_norm] lemma eval_verifier (env : Environment F) (input : CircuitType.Var CircuitBool F) :
    eval env input = CircuitType.evalVerifier env input :=
  CircuitType.eval_verifier env input
@[circuit_norm] lemma eval_verifier_structvar (env : Environment F) (input : Var F) :
    eval env input = CircuitType.evalVerifier (M := CircuitBool) env input :=
  CircuitType.eval_verifier (M := CircuitBool) env input
@[circuit_norm] lemma eval_prover (env : ProverEnvironment F) (input : CircuitType.Var CircuitBool F) :
    eval env input = CircuitType.evalProver (M := CircuitBool) env input :=
  CircuitType.eval_prover env input
@[circuit_norm] lemma eval_prover_structvar (env : ProverEnvironment F) (input : Var F) :
    eval env input = CircuitType.evalProver (M := CircuitBool) env input :=
  CircuitType.eval_prover (M := CircuitBool) env input

def toBool [DecidableEq F] (x : CircuitBool F) : Bool := x.bool = 1

def Value.toBool [DecidableEq F] (x : CircuitBool.Value F) : Bool := x.bool = 1

def Var.negate (input : CircuitBool.Var F) : CircuitBool.Var F where
  bool := (1 : F) - input.bool
  isBool env := by
    have h_bool := input.isBool env
    simp only [circuit_norm, IsBool] at h_bool ⊢
    grind
end CircuitBool

def boolNegate : GeneralFormalCircuit.WithHint (F p) CircuitBool CircuitBool where
  main (input : CircuitBool.Var (F p)) := do
    let c := input.negate
    -- unnecessary constraint, just there to show that completeness is automatic
    assertBool c.bool
    return c

  localLength _ := 0
  output input _ := input.negate

  -- we don't need any completeness statements! these are already captured by the
  -- `CircuitBool.isBool` property
  Assumptions input _ := IsBool input.bool
  Spec input output _ := IsBool output.bool ∧
    output.toBool = ¬ input.toBool

  soundness := by
    circuit_proof_start [CircuitBool.Value.toBool, CircuitBool.Var.negate, IsBool]
    -- TODO do this automatically for circuit inputs
    rcases input with ⟨ bool, h_bool ⟩
    -- TODO why doesn't this work with simp only?
    rw [CircuitBool.Value.mk.injEq] at h_input
    simp_all only
    grind

  completeness := by
    circuit_proof_start [CircuitBool.Value.toBool, CircuitBool.Var.negate, IsBool]
    rcases input with ⟨ bool, h_bool ⟩
    rw [CircuitBool.ProverValue.mk.injEq] at h_input
    simp_all only [IsBool]
    grind

end Examples.HintExample
