-- Circuit JSON generation for the FemtoCairo plonky3 backend
-- Generates the circuit structure (constraints + lookups) as JSON
import Lean
import Clean.Examples.FemtoCairo.Plonky3TestData
import Clean.Table.Json

open Examples.FemtoCairo.Plonky3TestData
open Examples.FemtoCairo.Types

def femtoCairoConstraints := femtoCairoTable.tableConstraintsWitness initialState finalState

def generateCircuit (output_path : String) : IO Unit := do
  let circuit_json := Lean.toJson femtoCairoConstraints
  IO.FS.writeFile output_path circuit_json.pretty

def main (args : List String) : IO Unit := do
  match args with
  | [output_path] => generateCircuit output_path
  | _ => IO.println "Usage: lake env lean --run FemtoCairoCircuitGen.lean <output_path>"
