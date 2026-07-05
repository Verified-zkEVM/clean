/-
R1CS Constraint Export

Converts Clean circuit operations to R1CS JSON format compatible with snarkjs.
Uses the shared flattening logic from Compile.lean.
-/
import Clean.Circuit.Expression
import Clean.Circuit.Operations
import Clean.Backends.Wasm.Compile

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

def compileR1CS (fieldPrime numInputs : ℕ) (ops : List (Operation F)) : String :=
  let flatOps := flattenOps ops
  -- Use the WASM compiler's VarMap to get the same signal layout
  -- Process operations to build the variable-to-signal mapping
  let vm := VarMap.init numInputs
  let (finalVm, _, _) := processFlatOps numInputs flatOps vm numInputs []
  let totalSignals := 1 + finalVm.nextLocal  -- +1 for constant signal
  let st : FlattenState := { nextSignal := totalSignals }
  let (allConstraints, nVars) := processOps fieldPrime vm flatOps st
  let ps := toString fieldPrime
  let constraintLines := allConstraints.reverse.map fun (a, b, c) =>
    "    [" ++ linCombToJson a ++ ", " ++ linCombToJson b ++ ", " ++ linCombToJson c ++ "]"
  "{\n" ++
  "  \"n8\": 32,\n" ++
  "  \"prime\": \"" ++ ps ++ "\",\n" ++
  "  \"nVars\": " ++ toString nVars ++ ",\n" ++
  "  \"nOutputs\": 1,\n" ++
  "  \"nPubInputs\": " ++ toString numInputs ++ ",\n" ++
  "  \"nPrvInputs\": 0,\n" ++
  "  \"nLabels\": " ++ toString nVars ++ ",\n" ++
  "  \"nConstraints\": " ++ toString allConstraints.length ++ ",\n" ++
  "  \"constraints\": [\n" ++
  String.intercalate ",\n" constraintLines ++ "\n" ++
  "  ]\n" ++
  "}"
where
  linCombToJson (lc : LinComb) : String :=
    let entries := lc.map fun (i, coeff) =>
      "\"" ++ toString i ++ "\": \"" ++ toString coeff ++ "\""
    "{" ++ String.intercalate ", " entries ++ "}"

end Backends.Wasm
