import Clean.Air.WitnessRust
import Clean.Examples.FibonacciWithChannels
import Clean.Utils.Primes

def main : IO Unit := do
  match Air.Flat.WitnessGeneration.Rust.ensembleToRust
      "FibonacciWitnessProgram"
      (fibonacciEnsemble (p := pBabybear)).ensemble
      (FibonacciWitness.config (p := pBabybear)) with
  | .ok rust => IO.print rust
  | .error error => throw (IO.userError error)
