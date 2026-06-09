import Clean.Circuit
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

compile_witness do
    let x : Expression (F pBabybear) := .const 0
    assertZero (x * (x - 1))
  => babybearZeroOneWitness

end Examples.Witness
