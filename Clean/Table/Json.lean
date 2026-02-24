import Clean.Table.Basic
import Clean.Table.WitnessGeneration
import Clean.Circuit.Json

open Lean

instance : ToJson RowIndex where
  toJson
    | .fromStart i => toJson (i : Int)
    | .fromEnd i => toJson (-(↑i : Int) - 1)

variable {F : Type} {S : Type → Type} [ProvableType S] {W : ℕ+} {α : Type} [Field F] [ToJson F]

instance : ToJson (CellOffset W S) where
  toJson off := Json.mkObj [
    ("row", off.row),
    ("column", off.column)
  ]

instance : ToJson (CellAssignment W S) where
  toJson assignment :=
    let aux_map := buildAuxMap assignment
    -- Serialize each var to JSON, resolving aux cells to {"row": 1, "column": col}
    -- using the column index from buildAuxMap. We serialize directly to Json
    -- because aux columns can be >= size S, which cannot be represented as
    -- Fin (size S) in CellOffset.
    let vars : Array Json := (assignment.vars.mapIdx fun idx cell =>
      match cell with
      | Cell.input off => toJson off
      | Cell.aux _ =>
        let col := aux_map[idx]!
        Json.mkObj [("row", toJson (1 : Nat)), ("column", toJson col)]
    ).toArray

    Json.mkObj [
      ("offset", toJson assignment.offset),
      ("aux_length", toJson assignment.aux_length),
      ("vars", Json.arr vars),
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
    | .boundary i c => Json.mkObj [
      ("type", Json.str "Boundary"),
      ("row", toJson i),
      ("context", toJson c)
    ]
    | .everyRow c => Json.mkObj [
      ("type", Json.str "EveryRow"),
      ("context", toJson c)
    ]
    | .everyRowExceptLast c => Json.mkObj [
      ("type", Json.str "EveryRowExceptLast"),
      ("context", toJson c)
    ]
