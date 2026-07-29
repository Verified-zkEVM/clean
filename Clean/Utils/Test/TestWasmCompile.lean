import Clean.Backends.Wasm.Compile
import Clean.Backends.Wasm.R1CS
import Clean.Utils.Field
import Clean.Utils.FiniteField
import Clean.Utils.Primes
import Clean.Specs.Poseidon
import Clean.Circomlib.Poseidon

/-!
# WASM Compiler Tests

Tests for the WASM compiler and R1CS exporter, including negative tests
checking that unsupported constructs are rejected with an error.
Uses `#eval!` since witness IR infrastructure contains `sorry`'d proofs
that prevent `native_decide` and `#eval`.
-/

open Backends.Wasm

namespace TestWasmCompile

/-- Substring check (`String.contains` takes a `Char`, not a substring). -/
def hasSubstr (s needle : String) : Bool := (s.splitOn needle).length > 1

def expectOk (label needle : String) (r : Except String String) : IO Unit :=
  match r with
  | .ok s =>
    if hasSubstr s needle then IO.println s!"OK: {label}"
    else throw <| IO.userError s!"FAIL: {label}: output missing '{needle}'"
  | .error e => throw <| IO.userError s!"FAIL: {label}: unexpected error: {e}"

def expectError (label needle : String) (r : Except String String) : IO Unit :=
  match r with
  | .ok _ => throw <| IO.userError s!"FAIL: {label}: expected an error, got success"
  | .error e =>
    if hasSubstr e needle then IO.println s!"OK: {label}"
    else throw <| IO.userError s!"FAIL: {label}: error '{e}' missing '{needle}'"

/-! ## Empty circuits -/

#eval! expectOk "empty circuit compiles" "getWitness"
  (compileModule p1009 0 ([] : List (Operation (F p1009))) 1)

#eval! expectOk "empty circuit R1CS exports" "\"n8\""
  (compileR1CS p1009 0 0 ([] : List (Operation (F p1009))) 1)

/-! ## numWords validation -/

#eval! expectError "BN254 with 1 word is rejected" "2^32"
  (compileModule Specs.Poseidon.BN254_PRIME 0 ([] : List (Operation Specs.Poseidon.F)) 1)

#eval! expectOk "BN254 with 4 words compiles" "getWitness"
  (compileModule Specs.Poseidon.BN254_PRIME 0 ([] : List (Operation Specs.Poseidon.F)) 4)

/-! ## Witness arithmetic -/

/-- One input `x`, one witness `w = x + 5`. -/
def addOps : List (Operation (F p1009)) :=
  [.witness 1 (.ir [] (.lit #v[.add (.expr (.var ⟨0⟩)) (.const 5)]))]

#eval! expectOk "witness addition compiles to $fadd" "call $fadd"
  (compileModule p1009 1 addOps 1)

/-- One input `x`, witness `w = x`, assert `w - x = 0`. -/
def assertOps : List (Operation (F p1009)) :=
  [.witness 1 (.ir [] (.lit #v[.expr (.var ⟨0⟩)])),
   .assert (.add (.var ⟨1⟩) (.mul (.const (-1)) (.var ⟨0⟩)))]

#eval! expectOk "assert exports a constraint" "nConstraints"
  (compileR1CS p1009 1 1 assertOps 1)

/-! ## Unsupported constructs are rejected with errors -/

#eval! expectError "native witness is rejected" "native"
  (compileModule p1009 0
    ([.witness 1 (.native fun _ => #v[1])] : List (Operation (F p1009))) 1)

#eval! expectOk "append compiles" "getWitness"
  (compileModule p1009 0
    ([.witness 2 (.ir [] (.append (.lit #v[.const 0]) (.lit #v[.const 1])))] :
      List (Operation (F p1009))) 1)

#eval! expectError "envGet is rejected" "envGet"
  (compileModule p1009 0
    ([.witness 1 (.ir [] (.lit #v[.envGet (.const 0)]))] : List (Operation (F p1009))) 1)

#eval! expectOk "multi-word val compiles" "getWitness"
  (compileModule Specs.Poseidon.BN254_PRIME 0
    ([.witness 1 (.ir [.letN (.val (.const 1))] (.lit #v[.const 0]))] :
      List (Operation Specs.Poseidon.F)) 4)

#eval! expectError "R1CS rejects native witness" "native"
  (compileR1CS p1009 0 0
    ([.witness 1 (.native fun _ => #v[1])] : List (Operation (F p1009))) 1)

/-! ## let-step indexing: steps don't shift circuit variable indices -/

/-- Two witness ops. The first uses a letF step to compute `x+1` and stores it as output 0.
    The second witnesses a constant. If let-steps shifted circuit variable indices,
    output 0 would be at the wrong local and the assert referencing it would fail
    (or the output store would write the wrong value). -/
def letStepOps : List (Operation (F p1009)) :=
  [.witness 1 (.ir [.letF (.add (.expr (.var ⟨0⟩)) (.const 1))]
                 (.lit #v[.localVar 0])),
   .witness 1 (.ir [] (.lit #v[.const 42])),
   .assert (.add (.var ⟨2⟩) (.mul (.const (-1 : F p1009)) (.var ⟨1⟩)))]

#eval! expectOk "let-step circuit compiles" "getWitness"
  (compileModule p1009 1 letStepOps 1)

#eval! expectOk "let-step R1CS exports" "\"nConstraints\""
  (compileR1CS p1009 1 1 letStepOps 1)

/-! ## Binary path validation with simple circuits -/

#eval! do
  -- Empty circuit: binary must validate
  let r := compileModuleBinary p1009 0 ([] : List (Operation (F p1009))) 1
  match r with
  | .error e => throw <| IO.userError s!"FAIL empty binary: {e}"
  | .ok binary =>
    IO.FS.writeBinFile (System.FilePath.mk "/tmp/test_bin_empty.wasm") binary
    let v ← IO.Process.output { cmd := "wasm-validate", args := #["/tmp/test_bin_empty.wasm"] }
    if v.exitCode ≠ 0 then throw <| IO.userError s!"FAIL empty validate: {v.stderr}"
    IO.println s!"OK: empty circuit binary validates ({binary.size} bytes)"

#eval! do
  -- Witness addition circuit (single-word): binary must validate
  let r := compileModuleBinary p1009 1 addOps 1
  match r with
  | .error e => throw <| IO.userError s!"FAIL addOps binary: {e}"
  | .ok binary =>
    IO.FS.writeBinFile (System.FilePath.mk "/tmp/test_bin_addops.wasm") binary
    let v ← IO.Process.output { cmd := "wasm-validate", args := #["/tmp/test_bin_addops.wasm"] }
    if v.exitCode ≠ 0 then throw <| IO.userError s!"FAIL addOps validate: {v.stderr}"
    IO.println s!"OK: addOps circuit binary validates ({binary.size} bytes)"

/-! ## End-to-end: Poseidon1 circuit via compileModuleBinary (direct WASM) -/

#eval! do
  let ops : List (Operation Specs.Poseidon.F) :=
    (Circomlib.Poseidon.Poseidon1.circuit.main (varFromOffset field 0)).operations 1
  -- Direct binary compilation (no WAT intermediate)
  let result := compileModuleBinary Specs.Poseidon.BN254_PRIME 1 ops 4
  match result with
  | .error e => throw <| IO.userError s!"FAIL: Poseidon1 binary: {e}"
  | .ok binary =>
    IO.FS.writeBinFile (System.FilePath.mk "/tmp/poseidon1_e2e.wasm") binary
    let v ← IO.Process.output { cmd := "wasm-validate", args := #["/tmp/poseidon1_e2e.wasm"] }
    if v.exitCode ≠ 0 then
      throw <| IO.userError s!"FAIL: wasm-validate: {v.stderr}"
    -- Round-trip through wasm2wat and verify exports
    let watOut ← IO.Process.output { cmd := "wasm2wat", args := #["/tmp/poseidon1_e2e.wasm"] }
    if watOut.exitCode ≠ 0 then
      throw <| IO.userError s!"FAIL: wasm2wat: {watOut.stderr}"
    if ¬ (watOut.stdout.contains "getWitness" || watOut.stdout.contains "\"getWitness\"") then
      throw <| IO.userError "FAIL: missing getWitness export"
    IO.println s!"OK: Poseidon1 binary validates ({binary.size} bytes)"

end TestWasmCompile
