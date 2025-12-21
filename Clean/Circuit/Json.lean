import Clean.Utils.Field
import Clean.Circuit.Expression
import Clean.Circuit.Extensions
import Clean.Circuit.Basic

open Lean

-- needs to be above the variable F, otherwise the F p from Utils.Field got overrided
instance (p : ℕ) : ToJson (F p) where
  toJson x := toJson x.val

variable {F : Type} [Field F] [ToJson F]

def Expression.toJson [ToJson F]: Expression F → Json
  | .var v => Json.mkObj [
    ("type", Json.str "var"),
    ("index", Json.num v.index)
  ]
  | .const c => Json.mkObj [
    ("type", Json.str "const"),
    ("value", Lean.toJson c)
  ]
  | .add x y => Json.mkObj [
    ("type", Json.str "add"),
    ("lhs", toJson x),
    ("rhs", toJson y)
  ]
  | .mul x y => Json.mkObj [
    ("type", Json.str "mul"),
    ("lhs", toJson x),
    ("rhs", toJson y)
  ]

instance : ToJson (Expression F) where
  toJson e := e.toJson

instance : ToJson (Lookup F) where
  toJson l := Json.mkObj [
    ("table", toJson l.table.name),
    ("entry", l.entry.map (fun e => e.reduceConstants.toJson) |>.toArray |> toJson),
  ]

instance : ToJson (FlatOperation F) where
  toJson
    | FlatOperation.witness m _ => Json.mkObj [
      ("type", Json.str "witness"), ("length", toJson m)]
    | FlatOperation.assert e => Json.mkObj [
      ("type", Json.str "assert"), ("constraint", e.reduceConstants.toJson)]
    | FlatOperation.lookup l => Json.mkObj [
      ("type", Json.str "lookup"), ("lookup", toJson l)]

instance : ToJson (Operation F) where
  toJson
    | Operation.witness m _ => Json.mkObj [
      ("type", Json.str "witness"), ("length", toJson m)]
    | Operation.assert e => Json.mkObj [
      ("type", Json.str "assert"), ("constraint", e.reduceConstants.toJson)]
    | Operation.lookup l => Json.mkObj [
      ("type", Json.str "lookup"), ("lookup", toJson l)]
    | Operation.subcircuit { ops, .. } => Json.mkObj [
      ("type", Json.str "subcircuit"), ("operations", toJson ops)]

instance : ToJson (Operations F) where
  toJson ops := toJson ops.toFlat

instance {α} : ToJson (Circuit F α) where
  toJson circuit := toJson (circuit.operations 0)

instance {α β} [ProvableType α] [ProvableType β] : ToJson (FormalCircuit F α β) where
  toJson circuit :=
    -- we witness the input, get the json, and remove the initial witness command
    let json := toJson (do circuit.main (←default))
    let arr := json.getArr?.toOption.getD #[]
    arr.drop 1 |> toJson

instance {α} [ProvableType α] : ToJson (FormalAssertion F α) where
  toJson assertion :=
    let json := toJson (do assertion.main (←default))
    let arr := json.getArr?.toOption.getD #[]
    arr.drop 1 |> toJson
