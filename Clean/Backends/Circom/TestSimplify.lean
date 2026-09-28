module

public import Clean.Backends.Circom.Simplify
public import Clean.Backends.Circom.R1CS
public import Clean.Circuit.Basic
public import Clean.Circuit.Provable
public import Clean.Gadgets.Equality
public import Clean.Utils.Field
public import Clean.Utils.FiniteField
public import Clean.Utils.Primes
public import Clean.Specs.Poseidon
public import Clean.Circomlib.Poseidon

public meta import Clean.Backends.Circom.Simplify
public meta import Clean.Backends.Circom.R1CS
public meta import Clean.Circuit.Basic
public meta import Clean.Circuit.Provable
public meta import Clean.Gadgets.Equality
public meta import Clean.Utils.Field
public meta import Clean.Utils.FiniteField
public meta import Clean.Utils.Primes
public meta import Clean.Specs.Poseidon
public meta import Clean.Circomlib.Poseidon

@[expose] public section

/-!
# Certified R1CS simplification tests

Sanity checks on the executable behaviour of `simplifyConstraints`.
-/

open Backends.Circom

namespace TestSimplify

abbrev Fp := F p1009

/-- Linear constraint `lc = 0`. -/
def lin (lc : List (ℕ × Fp)) : Constraint Fp := ([], [], lc)

/-- A field element as a signed integer: values above `p/2` print as negatives. -/
def coeffToString (c : Fp) : String :=
  let v := FiniteField.val c
  if 2 * v > FiniteField.size Fp then s!"-{FiniteField.size Fp - v}" else s!"{v}"

def lcToString (lc : List (ℕ × Fp)) : String :=
  " + ".intercalate (lc.map fun (i, c) =>
    match coeffToString c with
    | "1" => s!"s{i}"
    | "-1" => s!"-s{i}"
    | k => s!"{k}·s{i}")

def constraintToString (c : Constraint Fp) : String :=
  let (a, b, c) := c
  s!"({lcToString a}) * ({lcToString b}) = {lcToString c}"

def substToString (es : SubstEntries Fp) : String :=
  ", ".intercalate (es.map fun (x, r) => s!"s{x} ↦ {lcToString r}")

def hasSubstr (s needle : String) : Bool := (s.splitOn needle).length > 1

/-- A constant, unsatisfiable constraint `k = 0` with `k ≠ 0`. -/
def isUnsatConst : Constraint Fp → Bool
  | ([], [], [(0, k)]) => k ≠ 0
  | _ => false

/-! ### iden3/circom#425: contradictory constant pins

Signals: `0` = constant, `1` = `o` (public output), `2` = `a`, `3` = `b` (private inputs),
`4` = `x`. circom `--O1` drops `x = 3`; `--O2` drops everything. -/

def pins : List (Constraint Fp) :=
  [ lin [(2, 1), (3, 1), (4, -1)],   -- x = a + b
    lin [(0, -3), (4, 1)],           -- x = 3
    lin [(0, -5), (4, 1)],           -- x = 5
    lin [(1, -1), (2, 1), (4, 1)] ]  -- o = x + a

def pub425 : ℕ → Bool := fun i => i ≤ 1

#eval! (do
  let (cs, subst) := simplifyConstraints pub425 pins
  IO.println s!"#425 simplified: {cs.length} constraints; substitutions: {substToString subst}"
  for c in cs do IO.println s!"  {constraintToString c}"
  if !(cs.any isUnsatConst) then
    throw <| IO.userError "FAIL: #425: contradiction was lost"
  if cs.length ≠ 3 then
    throw <| IO.userError s!"FAIL: #425: expected 3 constraints, got {cs.length}"
  IO.println "OK: #425 contradiction preserved by the certified pass" : IO Unit)

/-! ### iden3/circom#252 / #224: private inputs are eliminated, public signals are not

`Bits2Num(1)`: `out = in0` with `in0` private (signal `2`) and `out` public (signal `1`).
The constraint disappears — correctly: the relation on `{out}` is "any value" either way,
and the theorem states exactly that. -/

def bits2num1 : List (Constraint Fp) := [lin [(1, -1), (2, 1)]]

#eval! (do
  let (cs, subst) := simplifyConstraints (fun i => i ≤ 1) bits2num1
  IO.println s!"#252 simplified: {cs.length} constraints; substitutions: {substToString subst}"
  if cs.length ≠ 0 then throw <| IO.userError "FAIL: #252: expected the private input to be eliminated"
  if subst ≠ [(2, [(1, 1)])] then throw <| IO.userError "FAIL: #252: unexpected substitution"
  -- with `in0` public as well, nothing may be eliminated
  let (cs', subst') := simplifyConstraints (fun i => i ≤ 2) bits2num1
  if cs'.length ≠ 1 ∨ !subst'.isEmpty then throw <| IO.userError "FAIL: #252: public signal eliminated"
  IO.println "OK: #252 private input eliminated, public input kept" : IO Unit)

/-! ### Substitution chains stay non-overlapping, contradictions through chains survive

`x = y`, `y = 3`, `x = 4` (all private): the map must end up `x ↦ 3, y ↦ 3` and the last
constraint must leave `-1 = 0`. -/

def chain : List (Constraint Fp) :=
  [ lin [(1, 1), (2, -1)],     -- x = y
    lin [(0, -3), (2, 1)],     -- y = 3
    lin [(0, -4), (1, 1)] ]    -- x = 4

#eval! (do
  let (cs, subst) := simplifyConstraints (fun i => i = 0) chain
  IO.println s!"chain simplified: {cs.length} constraints; substitutions: {substToString subst}"
  if !(cs.any isUnsatConst) then throw <| IO.userError "FAIL: chain: contradiction lost"
  -- non-overlapping: no right-hand side mentions an eliminated signal
  let keys := subst.map (·.1)
  for (_, r) in subst do
    for (i, _) in r do
      if keys.contains i then throw <| IO.userError s!"FAIL: chain: overlapping substitution on s{i}"
  IO.println "OK: chain substitutions non-overlapping, contradiction preserved" : IO Unit)

/-! ### Poseidon1 (BN254): regression on the counts, and snarkjs witness check -/

def poseidonOps : List (Operation Specs.Poseidon.F) :=
  (Circomlib.Poseidon.Poseidon1.circuit.main (varFromOffset field 0)).operations 1

/-- The value of a top-level numeric field in the exporter's JSON, e.g. `"nVars"`. -/
def jsonNat (json key : String) : Option ℕ :=
  match json.splitOn s!"\"{key}\": " with
  | _ :: rest :: _ => (rest.takeWhile Char.isDigit).toNat?
  | _ => none

#eval! (do
  let get (simplify : Bool) : IO String :=
    match compileR1CS Specs.Poseidon.BN254_PRIME 1 ["in"] [402] poseidonOps 4 simplify with
    | .ok s => pure s
    | .error e => throw <| IO.userError s!"FAIL: Poseidon1 compileR1CS: {e}"
  let raw ← get false
  let simp ← get true
  let counts (json : String) := (jsonNat json "nConstraints", jsonNat json "nVars")
  if counts raw != (some 618, some 620) then
    throw <| IO.userError s!"FAIL: Poseidon1 raw: expected 618 constraints / 620 wires, got {counts raw}"
  if counts simp != (some 398, some 620) then
    throw <| IO.userError s!"FAIL: Poseidon1 simplified: expected 398 constraints / 620 wires, got {counts simp}"
  IO.println "OK: Poseidon1 simplifies from 618 to 398 constraints, 620 wires unchanged" : IO Unit)

/-- Whether a command is on the PATH. -/
def hasCommand (cmd : String) : IO Bool := do
  let r ← IO.Process.output { cmd := "sh", args := #["-c", s!"command -v {cmd}"] }
  pure (r.exitCode = 0)

/- The forward direction of `simplifyConstraints_equisat` on a real circuit: the witness
computed by the (unchanged) WASM module satisfies the simplified R1CS. -/
#eval! (do
  if !(← hasCommand "snarkjs") then
    IO.println "SKIP: Poseidon1 snarkjs witness check (snarkjs not installed)"
    return
  let wasm ← match compileModule Specs.Poseidon.BN254_PRIME 1 ["in"] [402] poseidonOps 4 with
    | .ok b => pure b | .error e => throw <| IO.userError s!"FAIL: Poseidon1 compileModule: {e}"
  let r1cs ← match compileR1CSBin Specs.Poseidon.BN254_PRIME 1 ["in"] [402] poseidonOps 4 with
    | .ok b => pure b | .error e => throw <| IO.userError s!"FAIL: Poseidon1 compileR1CSBin: {e}"
  let wasmPath := "/tmp/test_simplify_poseidon1.wasm"
  let r1csPath := "/tmp/test_simplify_poseidon1.r1cs"
  let inPath := "/tmp/test_simplify_poseidon1_input.json"
  let wtnsPath := "/tmp/test_simplify_poseidon1.wtns"
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
      throw <| IO.userError s!"FAIL: Poseidon1({input}) witness rejected by the simplified R1CS:\n{checkOut.stdout}{checkOut.stderr}"
  IO.println "OK: Poseidon1 WASM witnesses (in = 0, 1, 5) satisfy the simplified R1CS (snarkjs wtns check)" : IO Unit)

end TestSimplify
