-- Simplified trace generation for plonky3 backend
-- This file generates Fibonacci witness traces with custom steps
import Lean
import Clean.Tables.Fibonacci8
import Clean.Table.WitnessGeneration
import Clean.Table.Json

open Tables.Fibonacci8Table

-- Generate trace with specified steps and output path
def generateTrace (steps : Nat) (output_path : String) : IO Unit := do
  let fib_relation_babybear := fib_relation (p := p_babybear)
  let init_row : RowType (F p_babybear) := { x := 0, y := 1 }

  let trace_data := witnesses fib_relation_babybear init_row steps
  let json_data := Lean.toJson trace_data

  IO.FS.writeFile output_path json_data.pretty
  IO.println s!"Generated trace with {steps} steps -> {output_path}"

-- Main function that takes steps and output path
def main (args : List String) : IO Unit := do
  match args with
  | [steps_str, output_path] =>
    -- Generate trace with specified steps and output path
    match steps_str.toNat? with
    | some steps => generateTrace steps output_path
    | none => IO.println "Error: Invalid number of steps"
  | _ =>
    IO.println "Usage: lake lean TraceGen.lean -- <steps> <output_path>"
