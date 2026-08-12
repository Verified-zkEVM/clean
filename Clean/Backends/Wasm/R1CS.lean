/-
R1CS Constraint Export

Converts Clean circuit operations to R1CS constraints in both formats
consumed by the snarkjs toolchain:

* JSON (`compileR1CS`) — the pretty-printed constraint object;
* binary `.r1cs` (`compileR1CSBin`) — the r1csfile format read by
  `snarkjs r1cs info`, `groth16 setup`, and the other `r1cs` subcommands.

Uses the shared flattening logic from Compile.lean.
-/
import Clean.Circuit.Expression
import Clean.Circuit.Operations
import Clean.Backends.Wasm.Compile

open Lean

namespace Backends.Wasm

open Expression (const add mul)

variable {F : Type} [FiniteField F]

private def bitsPerByte : ℕ := 8
private def fieldWordBits : ℕ := 64  -- field word size in bits (matches limbBits)

def processOps (vm : VarMap) (ops : List (FlatOperation F)) (st : FlattenState F) :
    Except String (List (Constraint F) × ℕ) :=
  match ops with
  | [] => pure (st.constraints, st.nextSignal)
  | .witness _ _ :: rest => processOps vm rest st
  | .assert e@(.add (.mul a b) (.mul (.const c) z)) :: rest =>
    if c = -1 ∨ c = 1 then
      let (la, st1) := flattenExpr vm a st
      let (lb, st2) := flattenExpr vm b st1
      -- Linearize a·b exactly like the WASM witness module does (it flattens
      -- the whole assert in order: the product first, then z), so intermediate
      -- numbering stays in sync: k = a·b, then k ± z = 0. A constant factor
      -- collapses into a scalar, no intermediate.
      if isConstant la ∨ isConstant lb then
        let (lz, st3) := flattenExpr vm z st2
        let lz' := if c = -1 then scaleLinComb (-1 : F) lz else lz
        processOps vm rest { st3 with constraints := (la, lb, lz') :: st3.constraints }
      else
        let k := st2.nextSignal
        let st3 : FlattenState F := { nextSignal := k + 1, constraints := (la, lb, [(k, (1 : F))]) :: st2.constraints }
        let (lz, st4) := flattenExpr vm z st3
        let lz' := if c = -1 then scaleLinComb (-1 : F) lz else lz
        let lc := addLinCombs [(k, (1 : F))] lz'
        processOps vm rest { st4 with constraints := (lc, [(0, (1 : F))], []) :: st4.constraints }
    else
      let (lc, st1) := flattenExpr vm e st
      processOps vm rest { st1 with constraints := (lc, [(0, (1 : F))], []) :: st1.constraints }
  | .assert e@(.add (.mul (.const c) z) (.mul a b)) :: rest =>
    if c = -1 ∨ c = 1 then
      let (la, st1) := flattenExpr vm a st
      let (lb, st2) := flattenExpr vm b st1
      if isConstant la ∨ isConstant lb then
        let (lz, st3) := flattenExpr vm z st2
        let lz' := if c = -1 then scaleLinComb (-1 : F) lz else lz
        processOps vm rest { st3 with constraints := (la, lb, lz') :: st3.constraints }
      else
        let k := st2.nextSignal
        let st3 : FlattenState F := { nextSignal := k + 1, constraints := (la, lb, [(k, (1 : F))]) :: st2.constraints }
        let (lz, st4) := flattenExpr vm z st3
        let lz' := if c = -1 then scaleLinComb (-1 : F) lz else lz
        let lc := addLinCombs [(k, (1 : F))] lz'
        processOps vm rest { st4 with constraints := (lc, [(0, (1 : F))], []) :: st4.constraints }
    else
      let (lc, st1) := flattenExpr vm e st
      processOps vm rest { st1 with constraints := (lc, [(0, (1 : F))], []) :: st1.constraints }
  | .assert e :: rest =>
      let (lc, st1) := flattenExpr vm e st
      processOps vm rest { st1 with constraints := (lc, [(0, (1 : F))], []) :: st1.constraints }
  | .lookup _ :: _ => .error "processOps: lookup constraints cannot be represented in R1CS"
  | .interact _ :: _ => .error "processOps: interactions cannot be represented in R1CS"

/-- Convert a linear combination to a sparse JSON object: {"signalIndex": "coeff", ...} -/
def linCombToJson (lc : List (ℕ × F)) : Json :=
  Json.mkObj (lc.map fun (i, coeff) =>
    (toString i, Json.str (toString (FiniteField.val coeff))))

/-- Convert a constraint (A, B, C) to a JSON array of three sparse objects. -/
def constraintToJson (c : Constraint F) : Json :=
  let (a, b, c') := c
  Json.arr #[linCombToJson a, linCombToJson b, linCombToJson c']

/--
Flatten the operations and extract the constraints, using the WASM compiler's
VarMap so the signal layout matches the witness-generation module.
Returns (constraints, nVars, n8), where n8 is the byte width of a field element.
`outputVarIdx` switches the signal numbering to the outputs-first layout,
matching `compileModule` with the same argument.
-/
private def compileConstraints (fieldPrime numInputs : ℕ) (inputNames : List String := []) (outputVarIdx : List ℕ := []) (ops : List (Operation F)) (numWords : ℕ) :
    Except String (List (Constraint F) × ℕ × ℕ) := do
  let numOutputs := outputVarIdx.length
  if !inputNames.isEmpty ∧ inputNames.length ≠ numInputs then
    throw s!"compileR1CS: {inputNames.length} input names for {numInputs} inputs (either none, or one per input)"
  if outputVarIdx.length ≠ outputVarIdx.eraseDups.length then
    throw "compileR1CS: outputVarIdx must not contain duplicate variables"
  if !(outputVarIdx.all fun v => v ≥ numInputs) then
    throw "compileR1CS: outputVarIdx must be witness circuit variables (indices ≥ numInputs)"
  let flatOps := Operations.toFlat ops
  let vm := { (VarMap.init numInputs numWords fieldPrime) with numOutputs, outputVars := outputVarIdx }
  let (_, finalVarIdx, _) ← processFlatOps flatOps vm numInputs []
  -- finalVarIdx = numInputs + total witness outputs (steps don't count)
  let witnessCount := finalVarIdx - numInputs
  if !(outputVarIdx.all fun v => v < finalVarIdx) then
    throw "compileR1CS: outputVarIdx contains a variable outside the witness range"
  let totalSignals := 1 + numInputs + witnessCount  -- +1 for constant signal
  let st : FlattenState F := { nextSignal := totalSignals }
  let (allConstraints, nVars) ← processOps vm flatOps st
  let primeBits := Nat.log2 fieldPrime + 1
  let n8 : ℕ := (primeBits + bitsPerByte - 1) / bitsPerByte
  pure (allConstraints.reverse, nVars, n8)

/--
Compile Clean circuit operations to R1CS JSON (snarkjs-compatible format).
Returns a pretty-printed JSON string, or an error for operations that cannot
be represented in R1CS (lookups, interactions) or witness IR the WASM
backend cannot compile.
-/
def compileR1CS (fieldPrime numInputs : ℕ) (inputNames : List String := []) (outputVarIdx : List ℕ := []) (ops : List (Operation F)) (numWords : ℕ) :
    Except String String := do
  let (constraints, nVars, n8) ← compileConstraints fieldPrime numInputs inputNames outputVarIdx ops numWords
  let constraintsArr := Json.arr (constraints.map constraintToJson |>.toArray)
  let json := Json.mkObj [
    ("n8", Json.num n8),
    ("prime", Json.str (toString fieldPrime)),
    ("nVars", Json.num nVars),
    ("nOutputs", Json.num outputVarIdx.length),
    ("nPubInputs", Json.num numInputs),
    ("nPrvInputs", Json.num 0),
    ("nLabels", Json.num nVars),
    ("nConstraints", Json.num constraints.length),
    ("constraints", constraintsArr)
  ]
  pure json.pretty

/-! ## Binary `.r1cs` encoding (the r1csfile format)

Layout (little-endian throughout), as read by `r1csfile` in snarkjs:

```
"r1cs" magic (4 bytes)  version u32 = 1  nSections u32 = 3
section 1 (header):      n8 u32, prime (n8 bytes), nVars u32, nOutputs u32,
                         nPubInputs u32, nPrvInputs u32, nLabels u64, nConstraints u32
section 2 (constraints): per constraint, three linear combinations A B C;
                         each is a count u32, then (signalIdx u32, coeff n8 bytes)
section 3 (wire2label):  one u64 label per wire (identity here)
```
-/

/-- Append `n` as little-endian `width`-byte integer. -/
private def putNatLE (arr : ByteArray) (width : ℕ) (n : ℕ) : ByteArray :=
  (List.range width).foldl (fun a i => a.push (UInt8.ofNat ((n >>> (8*i)) % 256))) arr

/-- Append `n` as a little-endian u32. -/
private def putUInt32LE (arr : ByteArray) (n : ℕ) : ByteArray :=
  putNatLE arr 4 n

/-- Append `n` as a little-endian u64. -/
private def putUInt64LE (arr : ByteArray) (n : ℕ) : ByteArray :=
  putNatLE arr 8 n

/-- Append a field element as `n8` little-endian bytes of its integer representation. -/
private def putFieldLE (arr : ByteArray) (n8 : ℕ) (x : F) : ByteArray :=
  putNatLE arr n8 (FiniteField.val x)

/-- Append a linear combination: count u32, then (signalIdx u32, coeff n8 bytes) entries. -/
private def linCombToBin (arr : ByteArray) (n8 : ℕ) (lc : List (ℕ × F)) : ByteArray :=
  lc.foldl (fun a (i, c) => putFieldLE (putUInt32LE a i) n8 c) (putUInt32LE arr lc.length)

/-- Append a constraint: three linear combinations A, B, C. -/
private def constraintToBin (arr : ByteArray) (n8 : ℕ) (c : Constraint F) : ByteArray :=
  let (a, b, c') := c
  linCombToBin (linCombToBin (linCombToBin arr n8 a) n8 b) n8 c'

/--
Compile Clean circuit operations to a binary `.r1cs` file (the r1csfile
format consumed by `snarkjs r1cs info`, `groth16 setup`, ...).
Returns the raw bytes, or an error for operations that cannot be
represented in R1CS.
-/
def compileR1CSBin (fieldPrime numInputs : ℕ) (inputNames : List String := []) (outputVarIdx : List ℕ := []) (ops : List (Operation F)) (numWords : ℕ) :
    Except String ByteArray := do
  let (constraints, nVars, _) ← compileConstraints fieldPrime numInputs inputNames outputVarIdx ops numWords
  let primeBits := Nat.log2 fieldPrime + 1
  -- snarkjs's r1csfile builds the field from the prime and reads each
  -- coefficient with that field's byte width (`8·⌈bitLength/limbBits⌉`); the
  -- file's n8 must match it or coefficient reads go out of bounds. For BN254
  -- that width is 32, which equals the minimal n8; for smaller primes
  -- (p1009 → 8) it is larger, so pad to it (values are < p < 2^(8·n8),
  -- encoding unchanged).
  -- 64-bit field words (matches Compile.lean's private `limbBits`).
  let n8Bin := 8 * ((primeBits + fieldWordBits - 1) / fieldWordBits)
  -- Header section payload
  let header := ByteArray.empty
  let header := putUInt32LE header n8Bin
  let header := putNatLE header n8Bin fieldPrime
  let header := putUInt32LE header nVars
  let header := putUInt32LE header outputVarIdx.length
  let header := putUInt32LE header numInputs
  let header := putUInt32LE header 0  -- nPrvInputs
  let header := putUInt64LE header nVars  -- nLabels
  let header := putUInt32LE header constraints.length
  -- Constraints section payload
  let conSec := constraints.foldl (fun arr c => constraintToBin arr n8Bin c) ByteArray.empty
  -- Wire-to-label section payload: identity map, one u64 label per wire
  let mapSec := (List.range nVars).foldl (fun arr i => putUInt64LE arr i) ByteArray.empty
  -- Assemble: magic, version, nSections, then each section id u32 + size u64 + payload
  let arr := "r1cs".toUTF8
  let arr := putUInt32LE arr 1
  let arr := putUInt32LE arr 3
  let arr := putUInt32LE arr 1 |> fun a => putUInt64LE a header.size |> fun a => a ++ header
  let arr := putUInt32LE arr 2 |> fun a => putUInt64LE a conSec.size |> fun a => a ++ conSec
  let arr := putUInt32LE arr 3 |> fun a => putUInt64LE a mapSec.size |> fun a => a ++ mapSec
  pure arr

end Backends.Wasm
