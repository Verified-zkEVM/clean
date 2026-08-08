/-
R1CS Constraint Export

Converts Clean circuit operations to R1CS JSON format compatible with snarkjs.
Uses the shared flattening logic from Compile.lean.
-/
import Clean.Circuit.Expression
import Clean.Circuit.Operations
import Clean.Backends.Wasm.Compile

open Lean

namespace Backends.Wasm

open Expression (var const add mul)

variable {F : Type} [FiniteField F]

def processOps (vm : VarMap) (ops : List (FlatOperation F)) (st : FlattenState F) :
    Except String (List (Constraint F) × ℕ) :=
  match ops with
  | [] => pure (st.constraints, st.nextSignal)
  | .witness _ _ :: rest => processOps vm rest st
  | .assert e@(.add (.mul a b) (.mul (.const c) z)) :: rest =>
    if c = -1 then
      let (la, st1) := flattenExpr vm a st
      let (lb, st2) := flattenExpr vm b st1
      let (lz, st3) := flattenExpr vm z st2
      processOps vm rest { st3 with constraints := (la, lb, lz) :: st3.constraints }
    else if c = 1 then
      let (la, st1) := flattenExpr vm a st
      let (lb, st2) := flattenExpr vm b st1
      let (lz, st3) := flattenExpr vm z st2
      processOps vm rest { st3 with constraints := (la, lb, scaleLinComb (-1 : F) lz) :: st3.constraints }
    else
      let (lc, st1) := flattenExpr vm e st
      processOps vm rest { st1 with constraints := (lc, [(0, (1 : F))], []) :: st1.constraints }
  | .assert e@(.add (.mul (.const c) z) (.mul a b)) :: rest =>
    if c = -1 then
      let (la, st1) := flattenExpr vm a st
      let (lb, st2) := flattenExpr vm b st1
      let (lz, st3) := flattenExpr vm z st2
      processOps vm rest { st3 with constraints := (la, lb, lz) :: st3.constraints }
    else if c = 1 then
      let (la, st1) := flattenExpr vm a st
      let (lb, st2) := flattenExpr vm b st1
      let (lz, st3) := flattenExpr vm z st2
      processOps vm rest { st3 with constraints := (la, lb, scaleLinComb (-1 : F) lz) :: st3.constraints }
    else
      let (lc, st1) := flattenExpr vm e st
      processOps vm rest { st1 with constraints := (lc, [(0, (1 : F))], []) :: st1.constraints }
  | .assert e :: rest =>
      let (lc, st1) := flattenExpr vm e st
      processOps vm rest { st1 with constraints := (lc, [(0, (1 : F))], []) :: st1.constraints }
  | .lookup _ :: _ => .error "compileR1CS: lookup constraints cannot be represented in R1CS"
  | .interact _ :: _ => .error "compileR1CS: interactions cannot be represented in R1CS"

/-- Convert a linear combination to a sparse JSON object: {"signalIndex": "coeff", ...} -/
def linCombToJson (lc : List (ℕ × F)) : Json :=
  Json.mkObj (lc.map fun (i, coeff) =>
    (toString i, Json.str (toString (FiniteField.val coeff))))

/-- Convert a constraint (A, B, C) to a JSON array of three sparse objects. -/
def constraintToJson (c : Constraint F) : Json :=
  let (a, b, c') := c
  Json.arr #[linCombToJson a, linCombToJson b, linCombToJson c']

/--
Compile Clean circuit operations to R1CS JSON (snarkjs-compatible format).
Returns a pretty-printed JSON string, or an error for operations that cannot
be represented in R1CS (lookups, interactions) or witness IR the WASM
backend cannot compile.
-/
def compileR1CS (fieldPrime numInputs numOutputs : ℕ) (ops : List (Operation F)) (numWords : ℕ) :
    Except String String := do
  let flatOps := Operations.toFlat ops
  -- Use the WASM compiler’s VarMap to get the same signal layout
  let vm := VarMap.init numInputs numWords fieldPrime
  let (_, finalVarIdx, _) ← processFlatOps numInputs flatOps vm numInputs []
  -- finalVarIdx = numInputs + total witness outputs (steps don’t count)
  let witnessCount := finalVarIdx - numInputs
  let totalSignals := 1 + numInputs + witnessCount  -- +1 for constant signal
  let st : FlattenState F := { nextSignal := totalSignals }
  let (allConstraints, nVars) ← processOps vm flatOps st
  let ps := toString fieldPrime
  let constraintsArr := Json.arr (allConstraints.reverse.map constraintToJson |>.toArray)
  let primeBits := Nat.log2 fieldPrime + 1
  let n8 : ℕ := (primeBits + 7) / 8
  let json := Json.mkObj [
    ("n8", Json.num n8),
    ("prime", Json.str ps),
    ("nVars", Json.num nVars),
    ("nOutputs", Json.num numOutputs),
    ("nPubInputs", Json.num numInputs),
    ("nPrvInputs", Json.num 0),
    ("nLabels", Json.num nVars),
    ("nConstraints", Json.num allConstraints.length),
    ("constraints", constraintsArr)
  ]
  pure json.pretty

end Backends.Wasm
