-- Trace generation for the FemtoCairo plonky3 backend (memory test)
import Clean.Examples.FemtoCairo.Plonky3MemoryTestData
import Clean.Examples.FemtoCairo.Plonky3Helpers
import Clean.Table.WitnessGeneration
import Clean.Table.Json

open Examples.FemtoCairo.Plonky3MemoryTestData
open Examples.FemtoCairo.Plonky3Helpers
open Examples.FemtoCairo.Types

def main (args : List String) : IO Unit := do
  match args with
  | [output_path] =>
    let numRows := numSteps + 1
    let initRow : Row (F pBabybear) (ProvablePair State unit) := (initialState, ())
    let trace := witnessesWithData femtoCairoTable.inductiveConstraint initRow numRows memData
    generateTraceJson trace memData output_path
  | _ => IO.println "Usage: lake env lean --run FemtoCairoMemoryTraceGen.lean <output_path>"
