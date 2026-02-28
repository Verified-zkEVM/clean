-- Circuit JSON generation for the FemtoCairo plonky3 backend
-- Generates the circuit structure (constraints + lookups) as JSON,
-- along with preprocessed table data (program table).
import Lean
import Clean.Examples.FemtoCairo.Plonky3TestData
import Clean.Table.Json

open Examples.FemtoCairo.Plonky3TestData
open Examples.FemtoCairo.Types

def femtoCairoConstraints := femtoCairoTable.tableConstraintsWitness initialState finalState

def generateCircuit (output_path : String) : IO Unit := do
  let constraints_json := Lean.toJson femtoCairoConstraints
  -- Encode program table as [[index, value], ...] rows (matching RowMajorMatrix format)
  let program_rows : Array Lean.Json := (Array.range programSize).map fun i =>
    let idx : F pBabybear := OfNat.ofNat i
    Lean.toJson #[idx, programData[i]!]
  let combined := Lean.Json.mkObj [
    ("constraints", constraints_json),
    ("preprocessed_tables", Lean.Json.mkObj [
      ("program", Lean.Json.mkObj [
        ("width", (2 : Nat)),
        ("rows", Lean.Json.arr program_rows)
      ])
    ])
  ]
  IO.FS.writeFile output_path combined.pretty

def main (args : List String) : IO Unit := do
  match args with
  | [output_path] => generateCircuit output_path
  | _ => IO.println "Usage: lake env lean --run FemtoCairoCircuitGen.lean <output_path>"
