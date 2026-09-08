import Clean.Air.Extraction.Rust
import Clean.Examples.FibonacciVm.Circuit
import Clean.Utils.Primes

/-! Generate differential-test fixtures using the Lean reference evaluators. -/

namespace Air.Flat.Extraction.TestData

private abbrev Field := F pBabybear

private def input : Witgen.FExpr Field := .expr (.var ⟨0⟩)

private def bit (index : ℕ) : Witgen.FExpr Field :=
  .ite (.bit input index) (.const 1) (.const 0)

private def edgeOutput : Witgen.VExpr Field 140 :=
  .append (.lit #v[
    .ofU64 (.mod (.val input) (.const 0)),
    .ofU64 (.mod (.val input) (.const 3)),
    .ofU64 (.div (.val input) (.const 0)),
    .ofU64 (.div (.val input) (.const 3)),
    bit 0, bit 30, bit 63, bit 64, bit 65, bit (2^64)
  ]) (.bitsOf (n := 130) input)

private def edgeBlock : WitnessBlock Field where
  outputWidth := 140
  steps := []
  output := edgeOutput
  wellFormed := by decide

private def edgeComponent : ComponentProgram Field where
  inputWidth := 1
  width := 141
  witnesses := [edgeBlock]
  constraints := []
  interactions := []

private def edgeProgram : Program Field where
  publicInputWidth := 0
  components := [edgeComponent]
  verifierInteractions := []
  modes := [.fixed [#[1]] []]
  padding := [{ input := #[1], minimumRows := 1 }]
  fuel := 10

private def edgeCase (value : ℕ) : Except String Lean.Json := do
  let input : Array Field := #[(value : Field)]
  let row ← edgeComponent.completeRow input (fun _ _ => #[])
  return Lean.Json.mkObj [
    ("input", Lean.toJson (input.map FiniteField.val)),
    ("row", Lean.toJson (row.map FiniteField.val))
  ]

private def fibonacciCase (steps : ℕ) : Except String Lean.Json :=
  let state := fibonacci steps
  let publicInput : fieldTriple Field := (steps, state.1, state.2)
  match FibonacciWitness.generate publicInput 10000 with
  | .error error => .error error
  | .ok witness => do
      unless WitnessGeneration.constraintsHold witness && WitnessGeneration.channelsBalanced witness do
        throw s!"invalid Lean reference witness for {steps} Fibonacci steps"
      return Lean.Json.mkObj [
        ("public_input", Lean.toJson ((toElements publicInput).toArray.map FiniteField.val)),
        ("tables", Lean.toJson (witness.tables.map fun table =>
          table.table.map fun row => row.map FiniteField.val))
      ]

def write (directory : System.FilePath) : IO Unit := do
  let rust ← IO.ofExcept (Rust.programToRust "WitnessEdges" edgeProgram)
  let edges ← IO.ofExcept ([0, 1, 7, pBabybear - 1].mapM edgeCase)
  let fibonacci ← IO.ofExcept ([0, 1, 32, 400].mapM fibonacciCase)
  let reference := Lean.Json.mkObj [
    ("edges", Lean.toJson edges),
    ("fibonacci", Lean.toJson fibonacci)
  ]
  IO.FS.createDirAll directory
  IO.FS.writeFile (directory / "witness_edges.rs") rust
  IO.FS.writeFile (directory / "witness_reference.json") (reference.compress ++ "\n")

end Air.Flat.Extraction.TestData

def main (args : List String) : IO Unit := do
  let [directory] := args
    | throw (IO.userError "usage: export_backend_test_data OUTPUT_DIRECTORY")
  Air.Flat.Extraction.TestData.write directory
