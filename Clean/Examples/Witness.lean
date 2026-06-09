import Clean.Circuit
import Clean.Utils.Primes

namespace Examples.Witness

def oneWitness : Circuit Rat (Expression Rat) := do
  let x ← witnessField fun _ => 7
  return x

#compile_witness oneWitness

def twoWitnesses : Circuit Rat (Expression Rat) := do
  let x ← witnessField fun _ => 7
  let y ← witnessField fun env => env x + 1
  return y

#compile_witness twoWitnesses

def vectorWitness : Circuit Rat (Vector (Expression Rat) 3) := do
  let x ← witnessField fun _ => 10
  let y ← witnessField fun env => env x + 1
  let xs ← witnessVector 3 fun env =>
    .mapRange 3 fun i => env x + env y + i
  return xs

#compile_witness vectorWitness

#compile_witness (do
  let x : Expression (F pBabybear) ← witnessField fun _ => 0
  assertZero (x * (x - 1)))

end Examples.Witness
