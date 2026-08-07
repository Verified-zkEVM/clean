import Clean.Air.Extraction.Rust
import Clean.Examples.FibonacciVm.Circuit
import Clean.Utils.Primes

def main : IO Unit := do
  match Air.Flat.Extraction.Rust.ensembleToRust
      "FibonacciEnsembleProgram"
      (fibonacciEnsemble (p := pBabybear)).ensemble
      (FibonacciWitness.config (p := pBabybear) 100000) with
  | .ok rust => IO.print rust
  | .error error => throw (IO.userError error)
