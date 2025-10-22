import Clean.Utils.Field
import Clean.Circuit.Expression
import Clean.Circuit.Basic

open Lean

-- needs to be above the variable F, otherwise the F p from Utils.Field got overrided
instance (p : ℕ) : ToJson (F p) where
  toJson x := toJson x.val

variable {F : Type} [Field F] [ToJson F]

def exprToJson [ToJson F]: Expression F → Json
  | .var v => Json.mkObj [
    ("type", Json.str "var"),
    ("index", Json.num v.index)
  ]
  | .const c => Json.mkObj [
    ("type", Json.str "const"),
    ("value", toJson c)
  ]
  | .add x y => Json.mkObj [
    ("type", Json.str "add"),
    ("lhs", exprToJson x),
    ("rhs", exprToJson y)
  ]
  | .mul x y => Json.mkObj [
    ("type", Json.str "mul"),
    ("lhs", exprToJson x),
    ("rhs", exprToJson y)
  ]

instance : ToJson (Expression F) where
  toJson := exprToJson

instance : ToJson (Lookup F) where
  toJson l := Json.mkObj [
    ("table", toJson l.table.name),
    ("entry", toJson l.entry.toArray),
  ]

instance : ToJson (FlatOperation F) where
  toJson
    | FlatOperation.witness m _ => Json.mkObj [("witness", toJson m)]
    | FlatOperation.assert e => Json.mkObj [("assert", toJson e)]
    | FlatOperation.lookup l => Json.mkObj [("lookup", toJson l)]
    | FlatOperation.yield enabled nl => Json.mkObj [("yield", toJson nl.name), ("enabled", toJson enabled)]
    | FlatOperation.use enabled nl => Json.mkObj [("use", toJson nl.name), ("enabled", toJson enabled)]

instance : ToJson (Operation F) where
  toJson
    | Operation.witness m _ => Json.mkObj [("witness", toJson m)]
    | Operation.assert e => Json.mkObj [("assert", toJson e)]
    | Operation.lookup l => Json.mkObj [("lookup", toJson l)]
    | Operation.subcircuit { ops, .. } => Json.mkObj [("subcircuit", toJson ops)]
    | Operation.yield enabled nl => Json.mkObj [("yield", toJson nl.name), ("enabled", toJson enabled)]
    | Operation.use enabled nl => Json.mkObj [("use", toJson nl.name), ("enabled", toJson enabled)]

instance : ToJson (Operations F) where
  toJson ops := toJson ops.toList
