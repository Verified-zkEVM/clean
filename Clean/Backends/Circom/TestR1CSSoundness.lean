module

public import Clean.Backends.Circom.R1CS
public import Clean.Backends.Circom.R1CSSemantics
public import Clean.Backends.Circom.R1CSSoundness
public import Clean.Circuit.Provable
public import Clean.Utils.Field
public import Clean.Utils.FiniteField
public import Clean.Specs.Poseidon
public import Clean.Circomlib.Poseidon

public meta import Clean.Backends.Circom.R1CS
public meta import Clean.Backends.Circom.R1CSSemantics
public meta import Clean.Backends.Circom.R1CSSoundness
public meta import Clean.Circuit.Provable
public meta import Clean.Utils.Field
public meta import Clean.Utils.FiniteField
public meta import Clean.Specs.Poseidon
public meta import Clean.Circomlib.Poseidon

@[expose] public section

/-!
# R1CS export tests

A regression on Poseidon1's exported constraint and wire counts, a snarkjs check that the
WASM module's witness satisfies the exported `.r1cs` (the direction `exportConstraints_sound`
does not cover), and an instantiation of the generic soundness theorem
`FormalCircuit.r1cs_soundness` on Poseidon1.
-/

open Backends.Circom

namespace TestR1CSSoundness

def hasSubstr (s needle : String) : Bool := (s.splitOn needle).length > 1

/-- The value of a top-level numeric field in the exporter's JSON, e.g. `"nVars"`. -/
def jsonNat (json key : String) : Option ℕ :=
  match json.splitOn s!"\"{key}\": " with
  | _ :: rest :: _ => (rest.takeWhile Char.isDigit).toNat?
  | _ => none

/-- Whether a command is on the PATH. -/
def hasCommand (cmd : String) : IO Bool := do
  let r ← IO.Process.output { cmd := "sh", args := #["-c", s!"command -v {cmd}"] }
  pure (r.exitCode = 0)

/-- The input variable Poseidon1 is exported with. -/
def poseidonInput : Var field Specs.Poseidon.F := varFromOffset field 0

def poseidonOps : List (Operation Specs.Poseidon.F) :=
  (Circomlib.Poseidon.Poseidon1.circuit.main poseidonInput).operations 1

/-! ### Poseidon1 (BN254): regression on the counts -/

#eval! (do
  let r ← match compileR1CS Specs.Poseidon.BN254_PRIME 1 ["in"] [402] poseidonOps 4 with
    | .ok s => pure s
    | .error e => throw <| IO.userError s!"FAIL: Poseidon1 compileR1CS: {e}"
  let counts := (jsonNat r "nConstraints", jsonNat r "nVars")
  if counts != (some 618, some 620) then
    throw <| IO.userError s!"FAIL: Poseidon1: expected 618 constraints / 620 wires, got {counts}"
  IO.println "OK: Poseidon1 exports 618 constraints over 620 wires" : IO Unit)

/-! ### Poseidon1: the WASM witness satisfies the exported R1CS (snarkjs) -/

#eval! (do
  if !(← hasCommand "snarkjs") then
    IO.println "SKIP: Poseidon1 snarkjs witness check (snarkjs not installed)"
    return
  let wasm ← match compileModule Specs.Poseidon.BN254_PRIME 1 ["in"] [402] poseidonOps 4 with
    | .ok b => pure b | .error e => throw <| IO.userError s!"FAIL: Poseidon1 compileModule: {e}"
  let r1cs ← match compileR1CSBin Specs.Poseidon.BN254_PRIME 1 ["in"] [402] poseidonOps 4 with
    | .ok b => pure b | .error e => throw <| IO.userError s!"FAIL: Poseidon1 compileR1CSBin: {e}"
  let wasmPath := "/tmp/test_r1cs_poseidon1.wasm"
  let r1csPath := "/tmp/test_r1cs_poseidon1.r1cs"
  let inPath := "/tmp/test_r1cs_poseidon1_input.json"
  let wtnsPath := "/tmp/test_r1cs_poseidon1.wtns"
  IO.FS.writeBinFile wasmPath wasm
  IO.FS.writeBinFile r1csPath r1cs
  for input in ["0", "1", "5"] do
    IO.FS.writeFile inPath ("{\"in\": \"" ++ input ++ "\"}")
    let calcArgs := #["wtns", "calculate", wasmPath, inPath, wtnsPath]
    let calcOut ← IO.Process.output { cmd := "snarkjs", args := calcArgs }
    unless calcOut.exitCode == 0 do
      throw <| IO.userError s!"FAIL: Poseidon1({input}) wtns calculate: {calcOut.stderr}"
    let checkArgs := #["wtns", "check", r1csPath, wtnsPath]
    let checkOut ← IO.Process.output { cmd := "snarkjs", args := checkArgs }
    unless checkOut.exitCode == 0 && hasSubstr checkOut.stdout "WITNESS IS CORRECT" do
      throw <| IO.userError s!"FAIL: Poseidon1({input}) witness rejected by the exported R1CS:\n{checkOut.stdout}{checkOut.stderr}"
  IO.println "OK: Poseidon1 WASM witnesses (in = 0, 1, 5) satisfy the exported R1CS (snarkjs wtns check)" : IO Unit)

/-! ### The soundness theorem instantiates on Poseidon1

`FormalCircuit.r1cs_soundness` is generic in the circuit; this only checks that it applies
to a real `FormalCircuit` with no further hypotheses: a satisfying assignment of the
exported constraints implies Poseidon1's `Spec` on the input and output read from the
signals. -/

example {cs : List (Constraint Specs.Poseidon.F)} {n : ℕ} {vm : VarMap}
    (h : exportConstraints Specs.Poseidon.BN254_PRIME 1 ["in"] [402] poseidonOps 4 = .ok (cs, n, vm))
    {w : ℕ → Specs.Poseidon.F} (hw : Sat w cs)
    (hA : Circomlib.Poseidon.Poseidon1.circuit.Assumptions (eval (envOfWitness vm w) poseidonInput)) :
    Circomlib.Poseidon.Poseidon1.circuit.Spec (eval (envOfWitness vm w) poseidonInput)
      (eval (envOfWitness vm w) (Circomlib.Poseidon.Poseidon1.circuit.output poseidonInput 1)) :=
  Circomlib.Poseidon.Poseidon1.circuit.r1cs_soundness poseidonInput 1 h hw hA

end TestR1CSSoundness
