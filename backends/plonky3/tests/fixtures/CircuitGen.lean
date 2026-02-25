-- Circuit JSON generation for plonky3 backend
-- Generates the circuit structure (constraints + lookups) as JSON
import Lean
import Clean.Tables.Fibonacci8
import Clean.Table.Json

open Tables.Fibonacci8Table

def generateCircuit (output_path : String) : IO Unit := do
  let circuit_json := Lean.toJson (fibTable (p:=pBabybear))
  IO.FS.writeFile output_path circuit_json.pretty

def main (args : List String) : IO Unit := do
  match args with
  | [output_path] => generateCircuit output_path
  | _ => IO.println "Usage: lake env lean --run CircuitGen.lean <output_path>"
