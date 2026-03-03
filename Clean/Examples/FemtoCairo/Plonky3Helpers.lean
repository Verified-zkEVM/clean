import Lean
import Clean.Circuit.Json
import Clean.Table.Json
import Clean.Utils.Primes

namespace Examples.FemtoCairo.Plonky3Helpers

/-- Write FemtoCairo circuit JSON (constraints + preprocessed program table + prover table metadata)
    to a file. Computes `num_columns` from the provable type size and maximum auxiliary columns. -/
def generateCircuitJson {S : Type → Type} [ProvableType S]
    (constraints : List (TableOperation S (F pBabybear)))
    (programSize : ℕ)
    (programData : Array (F pBabybear))
    (proverTablesMeta : Array (String × ℕ))
    (output_path : String) : IO Unit := do
  -- Compute num_columns = size S + max(numAux) across all constraint operations
  let maxAux := constraints.foldl (fun acc op =>
    let aux := match op with
    | .boundary _ c => c.finalAssignment.numAux
    | .everyRow c => c.finalAssignment.numAux
    | .everyRowExceptLast c => c.finalAssignment.numAux
    max acc aux) 0
  let numColumns := ProvableType.size S + maxAux

  -- Build prover_tables metadata JSON
  let proverTablesJson := Lean.Json.mkObj (proverTablesMeta.toList.map fun (name, w) =>
    (name, Lean.Json.mkObj [("width", w)]))

  let program_rows : Array Lean.Json := (Array.range programSize).map fun i =>
    let idx : F pBabybear := OfNat.ofNat i
    Lean.toJson #[idx, programData[i]!]
  let combined := Lean.Json.mkObj [
    ("num_columns", numColumns),
    ("constraints", Lean.toJson constraints),
    ("preprocessed_tables", Lean.Json.mkObj [
      ("program", Lean.Json.mkObj [
        ("width", (2 : Nat)),
        ("rows", Lean.Json.arr program_rows)
      ])
    ]),
    ("prover_tables", proverTablesJson)
  ]
  IO.FS.writeFile output_path combined.pretty

/-- Write FemtoCairo trace JSON (main trace + prover memory table) to a file. -/
def generateTraceJson
    (trace_data : Array (Array (F pBabybear)))
    (memData : ProverData (F pBabybear))
    (output_path : String) : IO Unit := do
  let main_trace_json := Lean.toJson trace_data
  let mem_rows := memData "memory" 2
  let mem_rows_json := Lean.Json.arr (mem_rows.map fun row =>
    Lean.Json.arr (row.toArray.map fun x => Lean.toJson x))
  let prover_tables := Lean.Json.mkObj [
    ("memory", Lean.Json.mkObj [
      ("width", Lean.toJson (2 : Nat)),
      ("rows", mem_rows_json)
    ])
  ]
  let combined := Lean.Json.mkObj [
    ("main_trace", main_trace_json),
    ("prover_tables", prover_tables)
  ]
  IO.FS.writeFile output_path combined.pretty

end Examples.FemtoCairo.Plonky3Helpers
