module

public import Clean.Backends.Plonky3.Print
public import Clean.Examples.SquaresTable.Ensemble
public import Clean.Utils.Primes

@[expose] public section

def main : IO Unit := do
  match Backends.Plonky3.Print.ensembleToRust (SquaresTable.ensemble (p := pBabybear) 16) 1000 with
  | .ok rust => IO.print rust
  | .error error => throw (IO.userError error)
