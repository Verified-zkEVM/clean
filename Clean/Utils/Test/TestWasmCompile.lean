import Clean.Backends.Wasm.Compile
import Clean.Backends.Wasm.R1CS
import Clean.Utils.Field
import Clean.Utils.FiniteField
import Clean.Utils.Primes
import Clean.Specs.Poseidon
import Clean.Circomlib.Poseidon
import Clean.Circomlib.Bitify

/-!
# WASM Compiler Tests

Tests for the WASM compiler and R1CS exporter, including negative tests
checking that unsupported constructs are rejected with an error.
Uses `#eval!` so the tests can shell out to `wasm-validate` and `snarkjs`
(depending on both being installed).
-/

open Backends.Wasm

namespace TestWasmCompile

/-- Substring check (`String.contains` takes a `Char`, not a substring). -/
def hasSubstr (s needle : String) : Bool := (s.splitOn needle).length > 1

/-- Whether a command is on the PATH (`command -v`). -/
def hasCommand (cmd : String) : IO Bool := do
  let r ← IO.Process.output { cmd := "sh", args := #["-c", s!"command -v {cmd}"] }
  pure (r.exitCode = 0)

/-- Run `action` if every tool in `tools` is installed, else print SKIP.
    The snarkjs-backed checks need external tools that the CI runner may not
    have; skipping (rather than failing) keeps the suite portable, while CI
    installs the tools so the checks actually run there. -/
def withTools (tools : List String) (action : IO Unit) : IO Unit := do
  let missing ← tools.filterM (fun t => do pure (!(← hasCommand t)))
  if missing.isEmpty then action
  else IO.println s!"SKIP: {tools} not installed ({missing})"

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
def expectBinaryOk (label needle : String) (r : Except String ByteArray) : IO Unit := do
  if !(← hasCommand "wasm-validate") then
    IO.println s!"SKIP: {label} (wasm-validate not installed)"
  else
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

#eval! expectBinaryOk "empty circuit binary validates" "" (compileModule p1009 0 [] [] ([] : List (Operation (F p1009))) 1)
#eval! expectOk "empty circuit R1CS exports" "\"n8\"" (compileR1CS p1009 0 [] [] ([] : List (Operation (F p1009))) 1)

/-! ## numWords validation -/

#eval! expectBinaryError "BN254 with 1 word rejected" "2^32" (compileModule Specs.Poseidon.BN254_PRIME 0 [] [] ([] : List (Operation Specs.Poseidon.F)) 1)
#eval! expectBinaryOk "BN254 with 4 words compiles" "" (compileModule Specs.Poseidon.BN254_PRIME 0 [] [] ([] : List (Operation Specs.Poseidon.F)) 4)

/-! ## Witness arithmetic -/

/-- One input `x`, one witness `w = x + 5`. -/
def addOps : List (Operation (F p1009)) :=
  [.witness 1 (.ir [] (.lit #v[.add (.expr (.var ⟨0⟩)) (.const 5)]))]

#eval! expectBinaryOk "witness addition compiles" "" (compileModule p1009 1 [] [] addOps 1)

/-- One input `x`, witness `w = x`, assert `w - x = 0`. -/
def assertOps : List (Operation (F p1009)) :=
  [.witness 1 (.ir [] (.lit #v[.expr (.var ⟨0⟩)])),
   .assert (.add (.var ⟨1⟩) (.mul (.const (-1)) (.var ⟨0⟩)))]

#eval! expectOk "assert exports a constraint" "nConstraints"
  (compileR1CS p1009 1 [] [] assertOps 1)

/-! ## Binary .r1cs export (r1csfile format) -/

#eval! withTools ["snarkjs"] do
  let binary ← match compileR1CSBin p1009 1 [] [] assertOps 1 with
    | .ok b => pure b
    | .error e => throw <| IO.userError s!"FAIL: compileR1CSBin: {e}"
  let path := "/tmp/test_bin_r1cs.r1cs"
  IO.FS.writeBinFile (System.FilePath.mk path) binary
  let r ← IO.Process.output { cmd := "snarkjs", args := #["r1cs", "info", path] }
  if r.exitCode ≠ 0 then throw <| IO.userError s!"FAIL: snarkjs r1cs info: {r.stderr}"
  if !hasSubstr r.stdout "# of Constraints: 1" then throw <| IO.userError "FAIL: expected 1 constraint"
  if !hasSubstr r.stdout "# of Wires: 3" then throw <| IO.userError "FAIL: expected 3 wires"
  if !hasSubstr r.stdout "# of Outputs: 0" then throw <| IO.userError "FAIL: expected 0 outputs (none declared)"
  IO.println "OK: binary R1CS validates with snarkjs r1cs info"

/-! ## Unsupported constructs are rejected with errors -/

#eval! expectBinaryError "native witness rejected" "native" (compileModule p1009 0 [] [] ([.witness 1 (.native fun _ => #v[1])] : List (Operation (F p1009))) 1)

#eval! expectBinaryOk "append compiles" "" (compileModule p1009 0 [] [] ([.witness 2 (.ir [] (.append (.lit #v[.const 0]) (.lit #v[.const 1])))] : List (Operation (F p1009))) 1)

#eval! expectBinaryOk "listGet compiles" "" (compileModule p1009 0 [] [] ([.witness 1 (.ir [] (.lit #v[.listGet [.const 0] (.const 0)]))] : List (Operation (F p1009))) 1)

#eval! expectBinaryOk "multi-word val compiles" "" (compileModule Specs.Poseidon.BN254_PRIME 0 [] [] ([.witness 1 (.ir [.letU (.val (.const 1))] (.lit #v[.const 0]))] : List (Operation Specs.Poseidon.F)) 4)

#eval! expectError "R1CS rejects native witness" "native"
  (compileR1CS p1009 0 [] []
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

#eval! expectBinaryOk "let-step circuit compiles" "" (compileModule p1009 1 [] [] letStepOps 1)

#eval! expectOk "let-step R1CS exports" "\"nConstraints\""
  (compileR1CS p1009 1 [] [] letStepOps 1)

/-! ## New u64 IR constructors (flt, bit, bitsOf, envRange) -/

/-- Witness program using `BExpr.flt` (field-sorted less-than):
    w = if x < 5 then 1 else 0. -/
def fltOps : List (Operation (F p1009)) :=
  [.witness 1 (.ir [] (.lit #v[
    .ite (.flt (.expr (.var ⟨0⟩)) (.const 5))
      (.const 1) (.const 0)]))]

#eval! expectBinaryOk "flt compiles" "" (compileModule p1009 1 [] [] fltOps 1)

/-- Witness program using `BExpr.bit` (bit test):
    w = if bit 2 of x is set then 1 else 0. -/
def bitOps : List (Operation (F p1009)) :=
  [.witness 1 (.ir [] (.lit #v[
    .ite (.bit (.expr (.var ⟨0⟩)) 2)
      (.const 1) (.const 0)]))]

#eval! expectBinaryOk "bit compiles" "" (compileModule p1009 1 [] [] bitOps 1)

/-- Witness program using `VExpr.bitsOf`: 8 low bits of x. -/
def bitsOfOps : List (Operation (F p1009)) :=
  [.witness 8 (.ir [] (.bitsOf (.expr (.var ⟨0⟩))))]

#eval! expectBinaryOk "bitsOf compiles" "" (compileModule p1009 1 [] [] bitsOfOps 1)

/-- Witness program using `VExpr.envRange`: witness env cells 0..1 (the input twice). -/
def envRangeOps : List (Operation (F p1009)) :=
  [.witness 2 (.ir [] (.envRange 0))]

#eval! expectBinaryOk "envRange compiles" "" (compileModule p1009 1 [] [] envRangeOps 1)

/-! ## Binary path validation with simple circuits -/

#eval! withTools ["wasm-validate"] do
  -- Empty circuit: binary must validate
  let r := compileModule p1009 0 [] [] ([] : List (Operation (F p1009))) 1
  match r with
  | .error e => throw <| IO.userError s!"FAIL empty binary: {e}"
  | .ok binary =>
    IO.FS.writeBinFile (System.FilePath.mk "/tmp/test_bin_empty.wasm") binary
    let v ← IO.Process.output { cmd := "wasm-validate", args := #["/tmp/test_bin_empty.wasm"] }
    if v.exitCode ≠ 0 then throw <| IO.userError s!"FAIL empty validate: {v.stderr}"
    IO.println s!"OK: empty circuit binary validates ({binary.size} bytes)"

#eval! withTools ["wasm-validate"] do
  -- Witness addition circuit (single-word): binary must validate
  let r := compileModule p1009 1 [] [] addOps 1
  match r with
  | .error e => throw <| IO.userError s!"FAIL addOps binary: {e}"
  | .ok binary =>
    IO.FS.writeBinFile (System.FilePath.mk "/tmp/test_bin_addops.wasm") binary
    let v ← IO.Process.output { cmd := "wasm-validate", args := #["/tmp/test_bin_addops.wasm"] }
    if v.exitCode ≠ 0 then throw <| IO.userError s!"FAIL addOps validate: {v.stderr}"
    IO.println s!"OK: addOps circuit binary validates ({binary.size} bytes)"

/-! ## End-to-end: Poseidon1 → binary WASM → wasm-validate → snarkjs witness -/

#eval! withTools ["wasm-validate", "snarkjs"] do
  let ops : List (Operation Specs.Poseidon.F) :=
    (Circomlib.Poseidon.Poseidon1.circuit.main (varFromOffset field 0)).operations 1
  let result := compileModule Specs.Poseidon.BN254_PRIME 1 [] [] ops 4
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

/-! ## Audit regression tests (2026-08 audit) -/

/-- Write the input JSON, run `snarkjs wtns calculate`, and parse all witness
    signals from the .wtns file (n8 read from the file header). -/
def witnessFor (wasmPath inputJson : String) : IO (List ℕ) := do
  let inPath := "/tmp/audit_input.json"
  IO.FS.writeFile (System.FilePath.mk inPath) inputJson
  let r ← IO.Process.output { cmd := "snarkjs", args := #["wtns", "calculate", wasmPath, inPath, "/tmp/audit_witness.wtns"] }
  if r.exitCode ≠ 0 then throw <| IO.userError s!"FAIL: snarkjs: {r.stderr}"
  let bytes ← IO.FS.readBinFile (System.FilePath.mk "/tmp/audit_witness.wtns")
  let u32At (off : ℕ) : ℕ := (List.range 4).foldl (fun acc i => acc + (bytes.get! (off + i)).toNat * 256^i) 0
  let n8 := u32At 24
  let nWit := u32At (28 + n8)  -- after n8 u32 + prime (n8 bytes)
  let dataOff := 44 + n8
  (List.range nWit).mapM fun idx =>
    pure <| (List.range n8).foldl (fun acc i => acc * 256 + (bytes.get! (dataOff + idx * n8 + n8 - 1 - i)).toNat) 0

/-- Compile to a wasm file and run snarkjs on the given input JSON. -/
def compileAndWitness (fieldPrime numInputs : ℕ) [Fact fieldPrime.Prime]
    (inputNames : List String) (outputVarIdx : List ℕ)
    (ops : List (Operation (F fieldPrime))) (numWords : ℕ) (path inputJson : String) : IO (List ℕ) := do
  let wasm ← match compileModule fieldPrime numInputs inputNames outputVarIdx ops numWords with
    | .ok b => pure b
    | .error e => throw <| IO.userError s!"compileModule: {e}"
  IO.FS.writeBinFile (System.FilePath.mk path) wasm
  witnessFor path inputJson

/-! ### C1: `a·b === z` asserts keep R1CS signal numbering in sync with the witness -/

#eval! withTools ["snarkjs"] do
  let ops : List (Operation (F p1009)) :=
    [.assert (.add (.mul (.var ⟨0⟩) (.var ⟨1⟩)) (.mul (.const (-1)) (.var ⟨2⟩)))]
  let r1cs ← match compileR1CS p1009 3 [] [] ops 1 with
    | .ok s => pure s
    | .error e => throw <| IO.userError e
  -- 1 const + 3 inputs + 1 intermediate for a·b.
  if !hasSubstr r1cs "\"nVars\": 5" then throw <| IO.userError "FAIL: C1: expected nVars=5"
  if !hasSubstr r1cs "\"nConstraints\": 2" then throw <| IO.userError "FAIL: C1: expected 2 constraints"
  let wit ← compileAndWitness p1009 3 [] [] ops 1 "/tmp/audit_c1.wasm" "{\"in\": [\"3\", \"4\", \"12\"]}"
  if wit.length ≠ 5 then throw <| IO.userError s!"FAIL: C1: witness length {wit.length} ≠ nVars 5"
  IO.println "OK: C1 a*b === z keeps R1CS numbering in sync"

/-! ### H1: let-step locals sized by the TOTAL step count (not the max) -/

#eval! withTools ["snarkjs"] do
  let stepOps : List (Operation (F p1009)) :=
    (List.range 4).map fun _ =>
      .witness 1 (.ir [.letF (.expr (.var ⟨0⟩))] (.lit #v[.bit (.localVar 0) 0]))
  let wit ← compileAndWitness p1009 1 [] [] stepOps 1 "/tmp/audit_h1.wasm" "{\"in\": [\"5\"]}"
  -- 4 witnesses, each = bit 0 of the input (5 → 1), plus const + input.
  let expected := [1, 5, 1, 1, 1, 1]
  if wit ≠ expected then throw <| IO.userError s!"FAIL: H1: got {wit}, expected {expected}"
  IO.println "OK: H1 scratch region sized by total steps"

/-! ### H2: $fadd carry corner (a_i = b_i = 2^64-1 with carry-in 1) -/

#eval! withTools ["snarkjs"] do
  let p := Specs.Poseidon.BN254_PRIME
  -- mont(x) = 2^128-1 (limbs [2^64-1, 2^64-1, 0, 0]) and
  -- mont(y) = 2^128-2^64+1 (limbs [1, 2^64-1, 0, 0]): limb 1 of $fadd hits the
  -- a = b = 2^64-1, carry-in 1 corner.
  let rInv := Nat.gcdA (2^256) p % p  -- R⁻¹ mod p (Bézout coefficient)
  let x := (((2^128 : ℕ) - 1) * rInv) % p
  let y := (((2^128 : ℕ) - (2^64 : ℕ) + 1) * rInv) % p
  let ops : List (Operation Specs.Poseidon.F) :=
    [.witness 1 (.ir [] (.lit #v[.add (.expr (.var ⟨0⟩)) (.expr (.var ⟨1⟩))]))]
  let wit ← compileAndWitness p 2 [] [] ops 4 "/tmp/audit_h2.wasm"
    (String.intercalate "" ["{\"in\": [\"", toString x, "\", \"", toString y, "\"]}"])
  let expected := (x + y) % p
  if wit.getD 3 0 ≠ expected then
    throw <| IO.userError s!"FAIL: H2: got signal 3 = {wit.getD 3 0}, expected {expected}"
  IO.println "OK: H2 $fadd carry corner"

/-! ### H3: nested flt inside a multi-word comparison operand -/

#eval! withTools ["snarkjs"] do
  let p := Specs.Poseidon.BN254_PRIME
  let ops : List (Operation Specs.Poseidon.F) :=
    [.witness 1 (.ir [] (.lit #v[
      .ite (.flt (.expr (.var ⟨0⟩)) (.ite (.flt (.expr (.var ⟨1⟩)) (.const 5)) (.const 1) (.const 0)))
        (.const 1) (.const 0)]))]
  -- x=0, y=3: inner flt(3,5) = 1 → inner ite = 1 → outer flt(0,1) = 1 → w = 1.
  let wit ← compileAndWitness p 2 [] [] ops 4 "/tmp/audit_h3.wasm" "{\"in\": [\"0\", \"3\"]}"
  if wit.getD 3 0 ≠ 1 then throw <| IO.userError s!"FAIL: H3: got signal 3 = {wit.getD 3 0}, expected 1"
  IO.println "OK: H3 nested flt does not clobber the outer capture"

/-! ### H4: multi-word feq emits valid WASM -/

#eval! withTools ["snarkjs"] do
  let p := Specs.Poseidon.BN254_PRIME
  let ops : List (Operation Specs.Poseidon.F) :=
    [.witness 1 (.ir [] (.lit #v[.ite (.feq (.expr (.var ⟨0⟩)) (.const 1)) (.const 7) (.const 8)]))]
  let wit1 ← compileAndWitness p 1 [] [] ops 4 "/tmp/audit_h4.wasm" "{\"in\": \"1\"}"
  let wit2 ← compileAndWitness p 1 [] [] ops 4 "/tmp/audit_h4b.wasm" "{\"in\": \"2\"}"
  if wit1.getD 2 0 ≠ 7 then throw <| IO.userError s!"FAIL: H4: feq(x,1) for x=1 gave {wit1.getD 2 0}, expected 7"
  if wit2.getD 2 0 ≠ 8 then throw <| IO.userError s!"FAIL: H4: feq(x,1) for x=2 gave {wit2.getD 2 0}, expected 8"
  IO.println "OK: H4 multi-word feq validates and computes"

/-! ### H5: listGet index survives an `.ite` element (single-word) -/

#eval! withTools ["snarkjs"] do
  let ops : List (Operation (F p1009)) :=
    [.witness 1 (.ir [] (.lit #v[
      .listGet [.ite (.lt (.const 0) (.const 1)) (.expr (.var ⟨0⟩)) (.expr (.var ⟨1⟩)), .const 7] (.const 0)]))]
  -- Element 0 = ite(true, x0, x1) = x0; index 0 selects it.
  let wit ← compileAndWitness p1009 2 [] [] ops 1 "/tmp/audit_h5.wasm" "{\"in\": [\"5\", \"6\"]}"
  if wit.getD 3 0 ≠ 5 then throw <| IO.userError s!"FAIL: H5: got signal 3 = {wit.getD 3 0}, expected 5"
  IO.println "OK: H5 listGet index survives ite elements"

/-! ### H6: multi-word listGet selector is in Montgomery form -/

#eval! withTools ["snarkjs"] do
  let p := Specs.Poseidon.BN254_PRIME
  let ops : List (Operation Specs.Poseidon.F) :=
    [.witness 1 (.ir [] (.lit #v[.listGet [.expr (.var ⟨0⟩), .const 7] (.const 0)]))]
  let wit ← compileAndWitness p 1 [] [] ops 4 "/tmp/audit_h6.wasm" "{\"in\": \"5\"}"
  if wit.getD 2 0 ≠ 5 then throw <| IO.userError s!"FAIL: H6: got signal 2 = {wit.getD 2 0}, expected 5"
  IO.println "OK: H6 multi-word listGet selects in Montgomery form"

/-! ### D1: strict input names reject unknown keys (like circom) -/

#eval! withTools ["snarkjs"] do
  let ops : List (Operation (F p1009)) :=
    [.witness 1 (.ir [] (.lit #v[.add (.expr (.var ⟨0⟩)) (.expr (.var ⟨1⟩))]))]
  let wasm ← match compileModule p1009 2 ["a", "b"] [] ops 1 with
    | .ok b => pure b
    | .error e => throw <| IO.userError s!"compileModule: {e}"
  let path := "/tmp/audit_d1.wasm"
  IO.FS.writeBinFile (System.FilePath.mk path) wasm
  -- Standard circom format works: one key per input.
  let wit ← witnessFor path "{\"a\": \"3\", \"b\": \"4\"}"
  if wit.getD 3 0 ≠ 7 then throw <| IO.userError s!"FAIL: D1: w = {wit.getD 3 0}, expected 7"
  -- A misspelled key must be rejected ("Signal not found").
  IO.FS.writeFile (System.FilePath.mk "/tmp/audit_typo.json") "{\"a\": \"3\", \"typo\": \"4\"}"
  let r ← IO.Process.output { cmd := "snarkjs", args := #["wtns", "calculate", path, "/tmp/audit_typo.json", "/tmp/audit_witness.wtns"] }
  if r.exitCode = 0 then throw <| IO.userError "FAIL: D1: unknown input key silently accepted"
  IO.println "OK: D1 strict input names reject unknown keys"

/-! ### D2: outputs-first layout puts the output at signal 1 -/

#eval! withTools ["snarkjs"] do
  let ops : List (Operation (F p1009)) :=
    [.witness 1 (.ir [] (.lit #v[.add (.expr (.var ⟨0⟩)) (.const 5)]))]
  let r1cs ← match compileR1CS p1009 1 ["x"] [1] ops 1 with
    | .ok s => pure s
    | .error e => throw <| IO.userError e
  if !hasSubstr r1cs "\"nOutputs\": 1" then throw <| IO.userError "FAIL: D2: nOutputs != 1"
  let wit ← compileAndWitness p1009 1 ["x"] [1] ops 1 "/tmp/audit_d2.wasm" "{\"x\": \"5\"}"
  -- Outputs-first: signal 1 = w (= 10), signal 2 = x (= 5).
  if wit.getD 1 0 ≠ 10 then throw <| IO.userError s!"FAIL: D2: output signal 1 = {wit.getD 1 0}, expected 10"
  if wit.getD 2 0 ≠ 5 then throw <| IO.userError s!"FAIL: D2: input signal 2 = {wit.getD 2 0}, expected 5"
  IO.println "OK: D2 outputs-first layout"

/-! ### Performance regression tests -/

-- These compile large flat operation lists. Before the fixes they were
-- quadratic: accumulating instructions with `acc ++ chunk` re-copied the
-- whole prefix per witness op (2.6s for a 2000-op circuit, 3.6s after a
-- reviewer "fixed" it), and the Keccak-shaped 3000-element mapRange was
-- similarly dominated by the O(n^2) layout. The `Num2Bits 128` circuit
-- below hung entirely (interrupted after 6 minutes): its `e2 + e2` power
-- accumulator shared one expression subtree, and expression flattening is a
-- structural recursion, so the sum blew up to 2^128 visits. Post-fix all of
-- these complete in well under a second per element; the tests assert
-- completion only, and print the elapsed milliseconds for the record.

-- `Num2Bits.main` needs `[Fact p.Prime] [Fact (p > 2)]`; the prime fact comes
-- from `Clean.Utils.Primes`, but no `> 2` instance exists for `p1009`.
instance : Fact (p1009 > 2) := ⟨by native_decide⟩

#eval! ((do
  let ops : List (Operation (F p1009)) :=
    List.replicate 2000 (.witness 1 (.ir [] (.lit #v[.const 0])))
  let t0 ← IO.monoMsNow
  let r := compileModule p1009 0 [] [] ops 1
  let t1 ← IO.monoMsNow
  match r with
  | .ok _ => IO.println s!"OK: 2000 witness ops compile to WASM ({t1 - t0} ms)"
  | .error e => throw <| IO.userError s!"FAIL: 2000 witness ops compileModule: {e}") : IO Unit)

#eval! ((do
  let ops : List (Operation (F p1009)) :=
    List.replicate 2000 (.witness 1 (.ir [] (.lit #v[.const 0])))
  let t0 ← IO.monoMsNow
  let r := compileR1CS p1009 0 [] [] ops 1
  let t1 ← IO.monoMsNow
  match r with
  | .ok _ => IO.println s!"OK: 2000 witness ops export R1CS ({t1 - t0} ms)"
  | .error e => throw <| IO.userError s!"FAIL: 2000 witness ops compileR1CS: {e}") : IO Unit)

#eval! ((do
  -- Keccak-shaped: one 3000-element mapRange witness (with 3000 witness
  -- cells), as produced by multi-limb gadgets.
  let ops : List (Operation (F p1009)) :=
    [.witness 3000 (.ir [] (.mapRange 3000 (.const 0)))]
  let t0 ← IO.monoMsNow
  let r := compileModule p1009 0 [] [] ops 1
  let t1 ← IO.monoMsNow
  match r with
  | .ok _ => IO.println s!"OK: 3000-element mapRange compiles ({t1 - t0} ms)"
  | .error e => throw <| IO.userError s!"FAIL: 3000-element mapRange compileModule: {e}") : IO Unit)

#eval! ((do
  -- Num2Bits 128: the power-of-two accumulator (`e2 * 2`) is a chain of 128
  -- multiplications, so both the WASM and the R1CS paths stay linear.
  let ops : List (Operation (F p1009)) := (Circomlib.Num2Bits.main 128 (varFromOffset field 0)).operations 1
  let t0 ← IO.monoMsNow
  let r := compileModule p1009 0 [] [] ops 1
  let t1 ← IO.monoMsNow
  match r with
  | .ok _ => IO.println s!"OK: Num2Bits 128 compiles to WASM ({t1 - t0} ms)"
  | .error e => throw <| IO.userError s!"FAIL: Num2Bits 128 compileModule: {e}"
  let t2 ← IO.monoMsNow
  let r := compileR1CS p1009 0 [] [] ops 1
  let t3 ← IO.monoMsNow
  match r with
  | .ok _ => IO.println s!"OK: Num2Bits 128 exports R1CS ({t3 - t2} ms)"
  | .error e => throw <| IO.userError s!"FAIL: Num2Bits 128 compileR1CS: {e}") : IO Unit)

end TestWasmCompile
