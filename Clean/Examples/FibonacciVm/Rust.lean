module

public import Clean.Air.Extraction.Rust
public import Clean.Examples.FibonacciVm.Ensemble
public import Clean.Utils.Primes

@[expose] public section

def main : IO Unit := do
  match Air.Flat.Extraction.Rust.ensembleToRust
      "FibonacciEnsembleProgram"
      (fibonacciEnsemble (p := pBabybear)).ensemble
      (FibonacciWitness.config (p := pBabybear) 100000) with
  | .ok rust => IO.print rust
  | .error error => throw (IO.userError error)
