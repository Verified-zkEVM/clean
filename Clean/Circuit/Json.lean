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

instance : ToJson (NamedArray (Expression F)) where
  toJson nl := Json.mkObj [
    ("name", toJson nl.1),
    ("values", toJson nl.2),
  ]

instance : ToJson (FlatOperation F) where
  toJson
    | .witness m _ => Json.mkObj [("witness", toJson m)]
    | .assert e => Json.mkObj [("assert", toJson e)]
    | .lookup l => Json.mkObj [("lookup", toJson l)]
    | .interact i => Json.mkObj [("interact", Json.mkObj [
      ("channel", toJson i.channel.name),
      ("multiplicity", toJson i.mult),
      ("message", toJson i.msg.toArray)])]

def NestedOperations.listToJson : List (NestedOperations F) → Array Json
  | [] => #[]
  | .single op :: ops => #[toJson op] ++ listToJson ops
  | .nested (name, ops') :: ops =>
    let obj := Json.mkObj [
      ("name", Json.str name),
      ("operations", Json.arr (listToJson ops'))]
    #[obj] ++ listToJson ops

instance : ToJson (NestedOperations F) where
  toJson
    | .single op => toJson op
    | .nested ⟨ name, ops ⟩ => Json.mkObj [
      ("name", Json.str name),
      ("operations", Json.arr (NestedOperations.listToJson ops))]

instance : ToJson (Operation F) where
  toJson
    | .witness m _ => Json.mkObj [("witness", toJson m)]
    | .assert e => Json.mkObj [("assert", toJson e)]
    | .lookup l => Json.mkObj [("lookup", toJson l)]
    | .subcircuit { ops, .. } => Json.mkObj [("subcircuit", toJson ops)]
    | .interact i => Json.mkObj [("interact", Json.mkObj [
      ("channel", toJson i.channel.name),
      ("multiplicity", toJson i.mult),
      ("message", toJson i.msg.toArray)])]

instance : ToJson (Operations F) where
  toJson ops := toJson ops.toList
