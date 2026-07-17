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
    List (Constraint F) × ℕ :=
  match ops with
  | [] => (st.constraints, st.nextSignal)
  | .witness _ _ :: rest =>
    processOps vm rest st  -- VarMap already handles witness allocation
  | .assert e :: rest =>
    let (lc, st1) := flattenExpr vm e st
    let constr : Constraint F := (lc, [(0, (1 : F))], [])
    let st2 := { st1 with constraints := constr :: st1.constraints }
    processOps vm rest st2
  | _ :: rest => processOps vm rest st

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
Returns a pretty-printed JSON string.
-/
def compileR1CS (fieldPrime numInputs : ℕ) (ops : List (Operation F)) : String :=
  let flatOps := Operations.toFlat ops
  -- Use the WASM compiler's VarMap to get the same signal layout
  let vm := VarMap.init numInputs
  let (finalVm, _, _) := processFlatOps numInputs flatOps vm numInputs []
  -- finalVm.nextLocal counts WASM locals (limbs). Convert to field element count.
  let witnessLocals := finalVm.nextLocal - numInputs * vm.numWords
  let witnessCount := witnessLocals / vm.numWords
  let totalSignals := 1 + numInputs + witnessCount  -- +1 for constant signal
  let st : FlattenState F := { nextSignal := totalSignals }
  let (allConstraints, nVars) := processOps vm flatOps st
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
