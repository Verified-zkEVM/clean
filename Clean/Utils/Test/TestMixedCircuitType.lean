import Clean.Circuit

/-!
This regression test covers a mixed `CircuitType` input: one ordinary provable
field and one prover-only field-dependent hint. The important proof ergonomics
are that `circuit_proof_start` should split the `h_input` equality into
field-level facts and use them to rewrite constraints from evaluated vars to
verifier/prover values.
-/

namespace TestMixedCircuitType

variable {p : ℕ} [Fact p.Prime]

structure Input (F : Type) where
  x : F
  inverse : UnconstrainedDep field F
deriving CircuitType

def main (input : Var Input (F p)) : Circuit (F p) (Expression (F p)) := do
  let inverse ← witness fun env => input.inverse env
  assertZero (inverse * input.x - 1)
  return inverse

def Spec (input : Value Input (F p)) (out : F p) (_data : ProverData (F p)) :=
  let x : F p := input.x
  x * out = 1

def ProverAssumptions (input : ProverValue Input (F p))
    (_data : ProverData (F p)) (_hint : ProverHint (F p)) :=
  let x : F p := input.x
  let inverse : F p := input.inverse
  x * inverse = 1

def ProverSpec (input : ProverValue Input (F p)) (out : F p) (_hint : ProverHint (F p)) :=
  out = input.inverse

instance elaborated : ElaboratedCircuit (F p) Input field where
  main
  output _ offset := varFromOffset field offset
  localLength _ := 1

theorem soundness :
    GeneralFormalCircuit.WithHint.Soundness (F p) elaborated (fun _ _ => True) Spec := by
  circuit_proof_start
  -- Regression checks for the intended post-`circuit_proof_start` shape:
  -- the high-level verifier input is gone, and the constraints mention `input_x`.
  fail_if_success (exact input)
  guard_hyp h_input :
    input_var.x.eval env = input_x ∧ () = input_inverse
  rw [mul_comm, add_neg_eq_zero] at h_holds
  exact h_holds

theorem completeness :
    GeneralFormalCircuit.WithHint.Completeness (F p) elaborated ProverAssumptions ProverSpec := by
  circuit_proof_start
  -- The prover-side equality should also be fieldwise; in particular the
  -- prover-only hint is connected to the generated witness by `h_env`.
  fail_if_success (exact input)
  guard_hyp h_input :
    input_var.x.eval env.toEnvironment = input_x ∧ input_var.inverse env = input_inverse
  constructor
  · rw [h_env, mul_comm, h_assumptions]
    ring
  · exact h_env

def circuit : GeneralFormalCircuit.WithHint (F p) Input field :=
  { elaborated with Spec, ProverAssumptions, ProverSpec, soundness, completeness }

end TestMixedCircuitType
