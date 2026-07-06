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

def processOps (p : ℕ) (vm : VarMap) (ops : List (FlatOperation F)) (st : FlattenState) :
    List Constraint × ℕ :=
  match ops with
  | [] => (st.constraints, st.nextSignal)
  | .witness _ _ :: rest =>
    processOps p vm rest st  -- VarMap already handles witness allocation
  | .assert e :: rest =>
    let (lc, st1) := flattenExpr p vm e st
    let constr : Constraint := (lc, [(0, 1)], [])
    let st2 := { st1 with constraints := constr :: st1.constraints }
    processOps p vm rest st2
  | _ :: rest => processOps p vm rest st

/-- Convert a linear combination to a sparse JSON object: {"signalIndex": "coeff", ...} -/
def linCombToJson (lc : LinComb) : Json :=
  Json.mkObj (lc.map fun (i, coeff) =>
    (toString i, Json.str (toString coeff)))

/-- Convert a constraint (A, B, C) to a JSON array of three sparse objects. -/
def constraintToJson (c : Constraint) : Json :=
  let (a, b, c') := c
  Json.arr #[linCombToJson a, linCombToJson b, linCombToJson c']

/--
Compile Clean circuit operations to R1CS JSON (snarkjs-compatible format).
Returns a pretty-printed JSON string.
-/
def compileR1CS (fieldPrime numInputs : ℕ) (ops : List (Operation F)) : String :=
  let flatOps := flattenOps ops
  -- Use the WASM compiler's VarMap to get the same signal layout
  let vm := VarMap.init numInputs
  let (finalVm, _, _) := processFlatOps numInputs flatOps vm numInputs []
  let totalSignals := 1 + finalVm.nextLocal  -- +1 for constant signal
  let st : FlattenState := { nextSignal := totalSignals }
  let (allConstraints, nVars) := processOps fieldPrime vm flatOps st
  let ps := toString fieldPrime
  let constraintsArr := Json.arr (allConstraints.reverse.map constraintToJson |>.toArray)
  let json := Json.mkObj [
    ("n8", Json.num 32),
    ("prime", Json.str ps),
    ("nVars", Json.num nVars),
    ("nOutputs", Json.num 1),
    ("nPubInputs", Json.num numInputs),
    ("nPrvInputs", Json.num 0),
    ("nLabels", Json.num nVars),
    ("nConstraints", Json.num allConstraints.length),
    ("constraints", constraintsArr)
  ]
  json.pretty

end Backends.Wasm
