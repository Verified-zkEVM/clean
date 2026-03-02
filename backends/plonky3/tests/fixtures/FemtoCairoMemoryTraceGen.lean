-- Trace generation for the FemtoCairo plonky3 backend (memory test)
-- Generates the execution trace using witnessesWithData + inductiveWitness
import Lean
import Clean.Examples.FemtoCairo.Plonky3MemoryTestData
import Clean.Table.WitnessGeneration
import Clean.Table.Json

open Examples.FemtoCairo.Plonky3MemoryTestData
open Examples.FemtoCairo.Types

-- N = 8 rows (7 steps)
def numRows : ℕ := 8

def initRow : Row (F pBabybear) (ProvablePair State unit) := (initialState, ())

def generateTrace (output_path : String) : IO Unit := do
  let trace_data := witnessesWithData femtoCairoTable.inductiveWitness initRow numRows memData
  let json_data := Lean.toJson trace_data
  IO.FS.writeFile output_path json_data.pretty
  IO.println s!"Generated FemtoCairo memory trace with {numRows} rows -> {output_path}"

def main (args : List String) : IO Unit := do
  match args with
  | [output_path] => generateTrace output_path
  | _ => IO.println "Usage: lake env lean --run FemtoCairoMemoryTraceGen.lean <output_path>"
