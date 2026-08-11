import Clean.Air.Extraction.Rust
import Clean.Examples.FemtoCairo.FlatAir
import Clean.Examples.FemtoCairo.Plonky3MemoryTestData
import Clean.Utils.Primes

open Examples.FemtoCairo
open Examples.FemtoCairo.Types
open Examples.FemtoCairo.Plonky3MemoryTestData

private theorem h_memorySize : 8 < pBabybear := by native_decide

def main : IO Unit := do
  match Air.Flat.Extraction.Rust.ensembleToRust
      "FemtoCairoFlatAirProgram"
      (Examples.FemtoCairo.FlatAir.soundEnsemble testProgram h_programSize h_memorySize
        initialState).ensemble
      (Examples.FemtoCairo.FlatAir.Witness.config (memorySize := 8)
        testProgram initialState 8 1000) with
  | .ok rust => IO.print rust
  | .error error => throw (IO.userError error)
