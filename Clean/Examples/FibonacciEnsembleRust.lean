import Clean.Air.EnsembleRust
import Clean.Examples.FibonacciWithChannels
import Clean.Utils.Primes

def main : IO Unit := do
  match Air.Flat.EnsembleRust.ensembleToRust
      "FibonacciEnsembleProgram"
      (fibonacciEnsemble (p := pBabybear)).ensemble
      (FibonacciWitness.config (p := pBabybear)) with
  | .ok rust => IO.print rust
  | .error error => throw (IO.userError error)
