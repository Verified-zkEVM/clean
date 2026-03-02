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
  let main_trace_json := Lean.toJson trace_data

  -- Serialize memory table: memData "memory" 2 gives Array (Vector F 2)
  let mem_rows := memData "memory" 2
  let mem_rows_json := Lean.Json.arr (mem_rows.map fun row =>
    Lean.Json.arr (row.toArray.map fun x => Lean.toJson x))

  let prover_tables := Lean.Json.mkObj [
    ("memory", Lean.Json.mkObj [
      ("width", Lean.toJson (2 : Nat)),
      ("rows", mem_rows_json)
    ])
  ]

  let wrapper := Lean.Json.mkObj [
    ("main_trace", main_trace_json),
    ("prover_tables", prover_tables)
  ]

  IO.FS.writeFile output_path wrapper.pretty
  IO.println s!"Generated FemtoCairo memory trace with {numRows} rows -> {output_path}"

def main (args : List String) : IO Unit := do
  match args with
  | [output_path] => generateTrace output_path
  | _ => IO.println "Usage: lake env lean --run FemtoCairoMemoryTraceGen.lean <output_path>"
