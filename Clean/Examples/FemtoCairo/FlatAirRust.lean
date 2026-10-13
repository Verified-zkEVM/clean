module

public import Clean.Backends.Plonky3.Print
public import Clean.Examples.FemtoCairo.FlatAir
public import Clean.Examples.FemtoCairo.FlatAirTestData
public import Clean.Utils.Primes

@[expose] public section

open Examples.FemtoCairo
open Examples.FemtoCairo.Types
open Examples.FemtoCairo.FlatAirTestData

def main : IO Unit := do
  match Backends.Plonky3.Print.ensembleToRust
      "FemtoCairoFlatAirProgram"
      (Examples.FemtoCairo.FlatAir.formalEnsemble testProgram programSize_lt memorySize_lt
        initialState)
      (Examples.FemtoCairo.FlatAir.Witness.config (memorySize := 8)
        testProgram programSize_lt initialState 8 1000) with
  | .ok rust => IO.print rust
  | .error error => throw (IO.userError error)
