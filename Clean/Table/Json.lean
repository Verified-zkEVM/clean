import Clean.Table.Basic
import Clean.Circuit.Json

open Lean

variable {F : Type} {S : Type → Type} [ProvableType S] {W: ℕ+} {α: Type} [Field F] [ToJson F]

instance : ToJson (CellOffset W S) where
  toJson off := Json.mkObj [
    ("row", off.row),
    ("column", off.column)
  ]

instance : ToJson (Cell W S) where
  toJson
    | .input off => toJson off
    | .aux i => Json.mkObj [("aux", toJson i)]

instance : ToJson (CellAssignment W S) where
  toJson assignment := Json.mkObj [
    ("offset", toJson assignment.offset),
    ("aux_length", toJson assignment.aux_length),
    ("vars", toJson assignment.vars.toArray)
  ]


instance : ToJson (TableContext W S F) where
  toJson ctx := Json.mkObj [
    ("circuit", toJson ctx.circuit),
    ("assignment", toJson ctx.assignment)
  ]

instance : ToJson (TableConstraint W S F α) where
  toJson table := toJson (table .empty).2

instance : ToJson (TableOperation S F) where
  toJson
    | .Boundary i c => Json.mkObj [
      ("type", Json.str "Boundary"),
      ("row", toJson i),
      ("context", toJson c)
    ]
    | .EveryRow c => Json.mkObj [
      ("type", Json.str "EveryRow"),
      ("context", toJson c)
    ]
    | .EveryRowExceptLast c => Json.mkObj [
      ("type", Json.str "EveryRowExceptLast"),
      ("context", toJson c)
    ]
