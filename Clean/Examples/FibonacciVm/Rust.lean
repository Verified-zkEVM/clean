module

public import Clean.Backends.Plonky3.Print
public import Clean.Examples.FibonacciVm.Ensemble
public import Clean.Utils.Primes

@[expose] public section

def main : IO Unit := do
  match Backends.Plonky3.Print.ensembleToRust
      "FibonacciEnsembleProgram"
      (fibonacciEnsemble (p := pBabybear))
      (FibonacciWitness.config (p := pBabybear)) with
  | .ok rust => IO.print rust
  | .error error => throw (IO.userError error)
