/-
R1CS Constraint Export

Converts Clean circuit operations to R1CS JSON format compatible with snarkjs.
-/
import Clean.Circuit.Expression
import Clean.Circuit.Operations
import Clean.Backends.Wasm.Compile

namespace Backends.Wasm

open Expression (var const add mul)

variable {F : Type} [FiniteField F]

abbrev LinComb := List (ℕ × ℕ)  -- sparse (signalIndex × coefficient) pairs
abbrev Constraint := LinComb × LinComb × LinComb  -- (A, B, C)

structure FlattenState where
  nextSignal : ℕ := 1
  constraints : List Constraint := []

def isConstant (lc : LinComb) : Bool :=
  match lc with | [(0, _)] => true | _ => false

def scaleLinComb (c : ℕ) (lc : LinComb) (p : ℕ) : LinComb :=
  lc.map fun (i, coeff) => (i, (c * coeff) % p)

def addLinCombs (a b : LinComb) (p : ℕ) : LinComb :=
  match a, b with
  | [], _ => b
  | _, [] => a
  | (i1, c1) :: xs, (i2, c2) :: ys =>
    if i1 < i2 then (i1, c1) :: addLinCombs xs ((i2, c2) :: ys) p
    else if i1 = i2 then (i1, (c1 + c2) % p) :: addLinCombs xs ys p
    else (i2, c2) :: addLinCombs ((i1, c1) :: xs) ys p

partial def flattenExpr (p : ℕ) (vm : VarMap) : Expression F → FlattenState → (LinComb × FlattenState)
  | .var i, st => ([(1 + vm.lookup i.index, 1)], st)  -- R1CS signal = 1 + WASM local
  | .const c, st =>
    let val := FiniteField.val c % p
    ([(0, val)], st)
  | .add a b, st =>
    let (la, st1) := flattenExpr p vm a st
    let (lb, st2) := flattenExpr p vm b st1
    (addLinCombs la lb p, st2)
  | .mul a b, st =>
    let (la, st1) := flattenExpr p vm a st
    let (lb, st2) := flattenExpr p vm b st1
    if isConstant la then
      (scaleLinComb ((la.head?.getD (0,0)).2) lb p, st2)
    else if isConstant lb then
      (scaleLinComb ((lb.head?.getD (0,0)).2) la p, st2)
    else
      let k := st2.nextSignal
      let st3 : FlattenState := { nextSignal := k + 1, constraints := (la, lb, [(k, 1)]) :: st2.constraints }
      ([(k, 1)], st3)

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
