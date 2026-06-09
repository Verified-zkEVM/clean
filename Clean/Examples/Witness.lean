import Clean.Circuit
import Clean.Circomlib.Gates
import Clean.Utils.Primes

namespace Examples.Witness

def oneWitness : Circuit Rat (Expression Rat) := do
  let x ← witnessField fun _ => 7
  return x

compile_witness oneWitness => oneWitnessCompiled

def twoWitnesses : Circuit Rat (Expression Rat) := do
  let x ← witnessField fun _ => 7
  let y ← witnessField fun env => env x + 1
  return y

compile_witness twoWitnesses => twoWitnessesCompiled

def vectorWitness : Circuit Rat (Vector (Expression Rat) 3) := do
  let x ← witnessField fun _ => 10
  let y ← witnessField fun env => env x + 1
  let xs ← witnessVector 3 fun env =>
    .mapRange 3 fun i => env x + env y + i
  return xs

compile_witness vectorWitness => vectorWitnessCompiled


def formalBaseWitness : FormalCircuitBase Rat field field where
  main x := do
    let y ← witnessField fun env => env x + 1
    assertZero (y - (x + 1))
    return y

compile_witness formalBaseWitness => formalBaseWitnessCompiled

compile_witness (Circomlib.AND.circuit (p:=pBabybear)) => circomlibAndWitness
compile_witness (Circomlib.XOR.circuit (p:=pBabybear)) => circomlibXorWitness
compile_witness (Circomlib.OR.circuit (p:=pBabybear)) => circomlibOrWitness

@[circuit_norm]
def assertBoolWithReturn : FormalAssertion (F pBabybear) field where
  -- works
  main x := do assertZero (x * (x - 1)); return ()
  -- doesn't work
  -- main x := assertZero (x * (x - 1))
  Spec x := IsBool x
  soundness := by circuit_proof_all
  completeness := by circuit_proof_all


example : ∀ a : Expression (F pBabybear) × Expression (F pBabybear),
  ExplicitCircuit (Circomlib.AND.circuit.main a) := by infer_explicit_circuit

/-- error: unsolved goals
a✝ : Expression (F pBabybear)
⊢ ExplicitCircuit (assertBool.main a✝) -/
#guard_msgs in
example : ∀ a : Expression (F pBabybear), ExplicitCircuit (assertBool.main a) := by
  infer_explicit_circuit

example : ∀ a : Expression (F pBabybear),
  ExplicitCircuit ((fun x => assertZero (x * (x - 1)) : Var field (F pBabybear) → Circuit (F pBabybear) (Var unit (F pBabybear))) a) := by
  infer_explicit_circuit

example : ∀ a : Expression (F pBabybear), ExplicitCircuit (assertBoolWithReturn.main a) := by
  infer_explicit_circuit

compile_witness (assertBool (p:=pBabybear)) => assertBoolWitness

compile_witness assertBoolWithReturn => assertBoolWithReturnWitness

end Examples.Witness
