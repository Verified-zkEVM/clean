import Clean.Backends.Wasm.Compile
import Clean.Backends.Wasm.R1CS
import Clean.Utils.Field
import Clean.Utils.FiniteField
import Clean.Utils.Primes
import Clean.Specs.Poseidon

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
  (compileR1CS p1009 0 ([] : List (Operation (F p1009))))

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
  (compileR1CS p1009 1 assertOps)

/-! ## Unsupported constructs are rejected with errors -/

#eval! expectError "native witness is rejected" "native"
  (compileModule p1009 0
    ([.witness 1 (.native fun _ => #v[1])] : List (Operation (F p1009))) 1)

#eval! expectError "append is rejected" "append"
  (compileModule p1009 0
    ([.witness 2 (.ir [] (.append (.lit #v[.const 0]) (.lit #v[.const 1])))] :
      List (Operation (F p1009))) 1)

#eval! expectError "envGet is rejected" "envGet"
  (compileModule p1009 0
    ([.witness 1 (.ir [] (.lit #v[.envGet (.const 0)]))] : List (Operation (F p1009))) 1)

#eval! expectError "multi-word val is rejected" "val"
  (compileModule Specs.Poseidon.BN254_PRIME 0
    ([.witness 1 (.ir [.letN (.val (.const 1))] (.lit #v[.const 0]))] :
      List (Operation Specs.Poseidon.F)) 4)

#eval! expectError "R1CS rejects native witness" "native"
  (compileR1CS p1009 0
    ([.witness 1 (.native fun _ => #v[1])] : List (Operation (F p1009))))

end TestWasmCompile
