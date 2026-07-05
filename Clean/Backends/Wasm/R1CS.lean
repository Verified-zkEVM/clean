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

def scaleLinComb (c : ℕ) (lc : LinComb) : LinComb :=
  lc.map fun (i, coeff) => (i, c * coeff)

def addLinCombs (a b : LinComb) : LinComb :=
  match a, b with
  | [], _ => b
  | _, [] => a
  | (i1, c1) :: xs, (i2, c2) :: ys =>
    if i1 < i2 then (i1, c1) :: addLinCombs xs ((i2, c2) :: ys)
    else if i1 = i2 then (i1, c1 + c2) :: addLinCombs xs ys
    else (i2, c2) :: addLinCombs ((i1, c1) :: xs) ys

partial def flattenExpr : Expression F → FlattenState → (LinComb × FlattenState)
  | .var i, st => ([(i.index, 1)], st)
  | .const c, st =>
    let val := FiniteField.val c
    ([(0, val)], st)
  | .add a b, st =>
    let (la, st1) := flattenExpr a st
    let (lb, st2) := flattenExpr b st1
    (addLinCombs la lb, st2)
  | .mul a b, st =>
    let (la, st1) := flattenExpr a st
    let (lb, st2) := flattenExpr b st1
    if isConstant la then
      (scaleLinComb ((la.head?.getD (0,0)).2) lb, st2)
    else if isConstant lb then
      (scaleLinComb ((lb.head?.getD (0,0)).2) la, st2)
    else
      let k := st2.nextSignal
      let st3 : FlattenState := { nextSignal := k + 1, constraints := (la, lb, [(k, 1)]) :: st2.constraints }
      ([(k, 1)], st3)

def processOps (ops : List (FlatOperation F)) (st : FlattenState) (nextSig : ℕ)
    (acc : List Constraint) : List Constraint × ℕ :=
  match ops with
  | [] => (acc, st.nextSignal)
  | .witness m _ :: rest =>
    processOps rest { st with nextSignal := st.nextSignal + m } (nextSig + m) acc
  | .assert e :: rest =>
    let (lc, st1) := flattenExpr e st
    let constr : Constraint := (lc, [(0, 1)], [])
    let st2 := { st1 with constraints := constr :: st1.constraints }
    processOps rest st2 nextSig (constr :: acc)
  | _ :: rest => processOps rest st nextSig acc

def compileR1CS (fieldPrime numInputs : ℕ) (ops : List (Operation F)) : String :=
  let flatOps := flattenOps ops
  -- Count witnesses for signal allocation
  let totalWitness : ℕ := flatOps.foldl (fun (acc : ℕ) (op : FlatOperation F) =>
    match op with | .witness m _ => acc + m | _ => acc) 0
  let st : FlattenState := { nextSignal := 1 + numInputs + totalWitness }
  let (allConstraints, nVars) := processOps flatOps st (1 + numInputs) []
  let ps := toString fieldPrime
  -- Build JSON manually (avoid s! for escaped quotes)
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
