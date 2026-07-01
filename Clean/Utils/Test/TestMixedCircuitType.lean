import Clean.Circuit

/-!
This regression test covers a mixed `CircuitType` input: one ordinary provable
field and one prover-only field-dependent hint. The important proof ergonomics
are that `circuit_proof_start` should split the `h_input` equality into
field-level facts and use them to rewrite constraints from evaluated vars to
verifier/prover values.
-/

namespace TestMixedCircuitType
variable {F : Type} [FiniteField F]

structure Input (F : Type) where
  x : F
  inverse : Unconstrained field F
deriving CircuitType

-- TODO automate this in the CircuitType deriver
instance : Inhabited (Var Input F) where
  default := { x := default, inverse := default }

def circuit : GeneralFormalCircuit.WithHint F Input field where
  main input := do
    let inverse ← witnessProgram input.inverse
    input.x * inverse === 1
    return inverse

  Spec input out _ :=
    input.x * out = 1
  ProverAssumptions input _ _ :=
    input.x * input.inverse = 1
  ProverSpec input out _ :=
    out = input.inverse

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
      input_var.x.eval env.toEnvironment = input_x ∧ (Witgen.FExpr.eval _ _ : F) = input_inverse
    refine ⟨ ?_, h_env ⟩
    rwa [h_env]

def parent : GeneralFormalCircuit F field field where
  main (input : Expression F) := do
    circuit { x := input, inverse := unconstrained (do return input⁻¹) }

  Spec input out _ :=
    input * out = 1
  ProverAssumptions input _ _ :=
    input ≠ 0

  soundness := by
    circuit_proof_start [circuit]
    -- The subcircuit spec should be stated in terms of the parent input, not
    -- the inline mixed child input passed to the subcircuit.
    guard_hyp h_holds : input * env.get i₀ = 1
    exact h_holds

  completeness := by
    circuit_proof_start [circuit]
    -- The child prover assumptions should reduce to the parent input and the
    -- inline inverse hint.
    guard_target = input * input⁻¹ = 1
    exact mul_inv_cancel₀ (G₀ := F) h_assumptions

structure BoolNatInput (F : Type) where
  x : F
  isZero : UnconstrainedBool F
  xNat : UnconstrainedNat F
deriving CircuitType

-- TODO automate this in the CircuitType deriver
instance : Inhabited (Var BoolNatInput F) where
  default := { x := default, isZero := default, xNat := default }

def boolNatCircuit : GeneralFormalCircuit.WithHint F BoolNatInput field where
  main input := return input.x

  Spec input out _ :=
    out = input.x

  ProverAssumptions input _ _ :=
    input.isZero = ((FiniteField.val (F:=F) input.x : ℕ) = 0) ∧
    input.xNat = FiniteField.val (F:=F) input.x

  soundness := by
    circuit_proof_start

  completeness := by
    circuit_proof_start

def boolNatParent : GeneralFormalCircuit F field field where
  main (input : Expression F) := do
    boolNatCircuit {
      x := input
      isZero := unconstrainedBool (do return ((input.val =? 0) &&& .true))
      xNat := unconstrainedNat (do return input.val)
    }

  Spec input out _ :=
    out = input

  soundness := by
    circuit_proof_start [boolNatCircuit]

  completeness := by
    circuit_proof_start [boolNatCircuit]
    simp

end TestMixedCircuitType
