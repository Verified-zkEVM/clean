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

/-- Validate a compiled module: write binary, validate with wasm-validate,
    then check wasm2wat output contains the expected substring. -/
def expectBinaryOk (label needle : String) (r : Except String ByteArray) : IO Unit :=
  match r with
  | .error e => throw <| IO.userError s!"FAIL: {label}: unexpected error: {e}"
  | .ok binary => do
    IO.FS.writeBinFile (System.FilePath.mk s!"/tmp/test_{label.replace " " "_"}.wasm") binary
    let v ← IO.Process.output { cmd := "wasm-validate", args := #[s!"/tmp/test_{label.replace " " "_"}.wasm"] }
    if v.exitCode ≠ 0 then throw <| IO.userError s!"FAIL: {label}: invalid wasm: {v.stderr}"
    if needle.isEmpty then IO.println s!"OK: {label}"
    else do
      let watOut ← IO.Process.output { cmd := "wasm2wat", args := #[s!"/tmp/test_{label.replace " " "_"}.wasm"] }
      if watOut.exitCode ≠ 0 then throw <| IO.userError s!"FAIL: {label}: wasm2wat failed"
      if hasSubstr watOut.stdout needle then IO.println s!"OK: {label}"
      else throw <| IO.userError s!"FAIL: {label}: output missing '{needle}'"

def expectBinaryError (label needle : String) (r : Except String ByteArray) : IO Unit :=
  match r with
  | .ok _ => throw <| IO.userError s!"FAIL: {label}: expected an error, got success"
  | .error e =>
    if hasSubstr e needle then IO.println s!"OK: {label}"
    else throw <| IO.userError s!"FAIL: {label}: error '{e}' missing '{needle}'"

/-! ## Empty circuits -/

#eval! expectBinaryOk "empty circuit binary validates" "" (compileModule p1009 0 ([] : List (Operation (F p1009))) 1)
#eval! expectOk "empty circuit R1CS exports" "\"n8\"" (compileR1CS p1009 0 0 ([] : List (Operation (F p1009))) 1)

/-! ## numWords validation -/

#eval! expectBinaryError "BN254 with 1 word rejected" "2^32" (compileModule Specs.Poseidon.BN254_PRIME 0 ([] : List (Operation Specs.Poseidon.F)) 1)
#eval! expectBinaryOk "BN254 with 4 words compiles" "" (compileModule Specs.Poseidon.BN254_PRIME 0 ([] : List (Operation Specs.Poseidon.F)) 4)

/-! ## Witness arithmetic -/

/-- One input `x`, one witness `w = x + 5`. -/
def addOps : List (Operation (F p1009)) :=
  [.witness 1 (.ir [] (.lit #v[.add (.expr (.var ⟨0⟩)) (.const 5)]))]

#eval! expectBinaryOk "witness addition compiles" "" (compileModule p1009 1 addOps 1)

/-- One input `x`, witness `w = x`, assert `w - x = 0`. -/
def assertOps : List (Operation (F p1009)) :=
  [.witness 1 (.ir [] (.lit #v[.expr (.var ⟨0⟩)])),
   .assert (.add (.var ⟨1⟩) (.mul (.const (-1)) (.var ⟨0⟩)))]

#eval! expectOk "assert exports a constraint" "nConstraints"
  (compileR1CS p1009 1 1 assertOps 1)

/-! ## Unsupported constructs are rejected with errors -/

#eval! expectBinaryError "native witness rejected" "native" (compileModule p1009 0 ([.witness 1 (.native fun _ => #v[1])] : List (Operation (F p1009))) 1)

#eval! expectBinaryOk "append compiles" "" (compileModule p1009 0 ([.witness 2 (.ir [] (.append (.lit #v[.const 0]) (.lit #v[.const 1])))] : List (Operation (F p1009))) 1)

#eval! expectBinaryError "listGet rejected" "listGet" (compileModule p1009 0 ([.witness 1 (.ir [] (.lit #v[.listGet [.const 0] (.const 0)]))] : List (Operation (F p1009))) 1)

#eval! expectBinaryOk "multi-word val compiles" "" (compileModule Specs.Poseidon.BN254_PRIME 0 ([.witness 1 (.ir [.letU (.val (.const 1))] (.lit #v[.const 0]))] : List (Operation Specs.Poseidon.F)) 4)

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

#eval! expectBinaryOk "let-step circuit compiles" "" (compileModule p1009 1 letStepOps 1)

#eval! expectOk "let-step R1CS exports" "\"nConstraints\""
  (compileR1CS p1009 1 1 letStepOps 1)

/-! ## New u64 IR constructors (flt, bit, bitsOf, envRange) -/

/-- Witness program using `BExpr.flt` (field-sorted less-than):
    w = if x < 5 then 1 else 0. -/
def fltOps : List (Operation (F p1009)) :=
  [.witness 1 (.ir [] (.lit #v[
    .ite (.flt (.expr (.var ⟨0⟩)) (.const 5))
      (.const 1) (.const 0)]))]

#eval! expectBinaryOk "flt compiles" "" (compileModule p1009 1 fltOps 1)

/-- Witness program using `BExpr.bit` (bit test):
    w = if bit 2 of x is set then 1 else 0. -/
def bitOps : List (Operation (F p1009)) :=
  [.witness 1 (.ir [] (.lit #v[
    .ite (.bit (.expr (.var ⟨0⟩)) 2)
      (.const 1) (.const 0)]))]

#eval! expectBinaryOk "bit compiles" "" (compileModule p1009 1 bitOps 1)

/-- Witness program using `VExpr.bitsOf`: 8 low bits of x. -/
def bitsOfOps : List (Operation (F p1009)) :=
  [.witness 8 (.ir [] (.bitsOf (.expr (.var ⟨0⟩))))]

#eval! expectBinaryOk "bitsOf compiles" "" (compileModule p1009 1 bitsOfOps 1)

/-- Witness program using `VExpr.envRange`: witness env cells 0..1 (the input twice). -/
def envRangeOps : List (Operation (F p1009)) :=
  [.witness 2 (.ir [] (.envRange 0))]

#eval! expectBinaryOk "envRange compiles" "" (compileModule p1009 1 envRangeOps 1)

/-! ## Binary path validation with simple circuits -/

#eval! do
  -- Empty circuit: binary must validate
  let r := compileModule p1009 0 ([] : List (Operation (F p1009))) 1
  match r with
  | .error e => throw <| IO.userError s!"FAIL empty binary: {e}"
  | .ok binary =>
    IO.FS.writeBinFile (System.FilePath.mk "/tmp/test_bin_empty.wasm") binary
    let v ← IO.Process.output { cmd := "wasm-validate", args := #["/tmp/test_bin_empty.wasm"] }
    if v.exitCode ≠ 0 then throw <| IO.userError s!"FAIL empty validate: {v.stderr}"
    IO.println s!"OK: empty circuit binary validates ({binary.size} bytes)"

#eval! do
  -- Witness addition circuit (single-word): binary must validate
  let r := compileModule p1009 1 addOps 1
  match r with
  | .error e => throw <| IO.userError s!"FAIL addOps binary: {e}"
  | .ok binary =>
    IO.FS.writeBinFile (System.FilePath.mk "/tmp/test_bin_addops.wasm") binary
    let v ← IO.Process.output { cmd := "wasm-validate", args := #["/tmp/test_bin_addops.wasm"] }
    if v.exitCode ≠ 0 then throw <| IO.userError s!"FAIL addOps validate: {v.stderr}"
    IO.println s!"OK: addOps circuit binary validates ({binary.size} bytes)"

/-! ## End-to-end: Poseidon1 → binary WASM → wasm-validate → snarkjs witness -/

#eval! do
  let ops : List (Operation Specs.Poseidon.F) :=
    (Circomlib.Poseidon.Poseidon1.circuit.main (varFromOffset field 0)).operations 1
  let result := compileModule Specs.Poseidon.BN254_PRIME 1 ops 4
  match result with
  | .error e => throw <| IO.userError s!"FAIL: Poseidon1: {e}"
  | .ok binary =>
    let wasmPath := "/tmp/poseidon1_e2e.wasm"
    IO.FS.writeBinFile (System.FilePath.mk wasmPath) binary
    -- wasm-validate
    let v ← IO.Process.output { cmd := "wasm-validate", args := #[wasmPath] }
    if v.exitCode ≠ 0 then throw <| IO.userError s!"FAIL: wasm-validate: {v.stderr}"
    -- snarkjs wtns calculate (Poseidon1 of input=0)
    IO.FS.writeFile (System.FilePath.mk "/tmp/poseidon1_input.json") "{\"in\": \"0\"}"
    let snarkOut ← IO.Process.output {
      cmd := "snarkjs", args := #["wtns", "calculate", wasmPath, "/tmp/poseidon1_input.json", "/tmp/poseidon1_witness.wtns"]
    }
    if snarkOut.exitCode ≠ 0 then throw <| IO.userError s!"FAIL: snarkjs: {snarkOut.stderr}"
    -- Verify against Lean ground truth. The Poseidon1 output is the circuit
    -- variable at index 402 (0-based signal 402), which is NOT the last signal
    -- (later signals are intermediate constraint witnesses).
    -- Ground truths from Specs.PoseidonOptimized.poseidon1Opt:
    --   0 → 19014214495641488759237505126948346942972912379615652741039992445865937985820
    --   1 → 18586133768512220936620570745912940619677854269274689475585506675881198879027
    --   5 → 19065150524771031435284970883882288895168425523179566388456001105768498065277
    let gts := [("0", "19014214495641488759237505126948346942972912379615652741039992445865937985820"),
               ("1", "18586133768512220936620570745912940619677854269274689475585506675881198879027"),
               ("5", "19065150524771031435284970883882288895168425523179566388456001105768498065277")]
    for (input, gt) in gts do
      IO.FS.writeFile (System.FilePath.mk "/tmp/poseidon1_input.json") (String.intercalate "" ["{\"in\": \"", input, "\"}"])
      let r ← IO.Process.output {
        cmd := "snarkjs", args := #["wtns", "calculate", wasmPath, "/tmp/poseidon1_input.json", "/tmp/poseidon1_witness.wtns"]
      }
      if r.exitCode ≠ 0 then throw <| IO.userError s!"FAIL: snarkjs input={input}: {r.stderr}"
      -- Parse the wtns file: read signal 402 (32 bytes, little-endian)
      let wtnsBytes ← IO.FS.readBinFile (System.FilePath.mk "/tmp/poseidon1_witness.wtns")
      -- wtns layout: "wtns"(4) version(4) nSections(4) id1(4) len1(8) n8(4) prime(n8) nWitnesses(4) id2(4) len2(8) witnesses...
      -- Section 2 header is id2(4)+len2(8), then witness data directly (nWitnesses is in section 1).
      let n8 := 32
      let witnessData := 4+4+4+4+8+4+n8+4+4+8
      let signal402 := wtnsBytes.extract (witnessData + 402*n8) (witnessData + 403*n8)
      -- little-endian u256: byte 0 is the least significant
      let leVal := (List.range signal402.size).foldl (fun acc i => acc * 256 + (signal402.get! (signal402.size - 1 - i)).toNat) 0
      let expected := String.toNat? gt
      match expected with
      | none => throw <| IO.userError "FAIL: bad ground truth"
      | some exp =>
        if leVal ≠ exp then
          throw <| IO.userError s!"FAIL: Poseidon1({input}) = {leVal}, expected {exp}"
        else
          IO.println s!"OK: Poseidon1({input}) matches ground truth"
    IO.println s!"OK: Poseidon1 → wasm-validate + snarkjs (3 inputs verified vs ground truth, {binary.size} bytes WASM)"

end TestWasmCompile
