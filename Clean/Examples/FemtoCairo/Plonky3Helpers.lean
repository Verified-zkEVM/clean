import Lean
import Clean.Circuit.Json
import Clean.Utils.Primes

namespace Examples.FemtoCairo.Plonky3Helpers

/-- Write FemtoCairo circuit JSON (constraints + preprocessed program table) to a file. -/
def generateCircuitJson
    (constraints_json : Lean.Json)
    (programSize : ℕ)
    (programData : Array (F pBabybear))
    (output_path : String) : IO Unit := do
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

end Examples.FemtoCairo.Plonky3Helpers
