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
      (Examples.FemtoCairo.FlatAir.formalEnsemble testProgram h_programSize h_memorySize
        initialState)
      (Examples.FemtoCairo.FlatAir.Witness.plan (memorySize := 8)
        testProgram h_programSize initialState) with
  | .ok rust => IO.print rust
  | .error error => throw (IO.userError error)
