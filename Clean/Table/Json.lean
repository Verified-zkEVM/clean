import Clean.Table.Basic
import Clean.Table.WitnessGeneration
import Clean.Circuit.Json

open Lean

variable {F : Type} {S : Type → Type} [ProvableType S] {W : ℕ+} {α : Type} [Field F] [ToJson F]

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
  toJson assignment :=
    let aux_map := buildAuxMap assignment
    -- iterate over the vars and convert aux cell to input cell with column from aux_map
    let vars := assignment.vars.mapIdx fun idx cell =>
      match cell with
      | Cell.input off => Cell.input off
      | Cell.aux _ =>
        let col := aux_map[idx]!
        if h: col < (size S)
          then Cell.input { row := 1, column := ⟨col, h⟩ }
          else cell -- todo: might be better to refactor the buildAuxMap to return Fin (size S) instead

    Json.mkObj [
      ("offset", toJson assignment.offset),
      ("aux_length", toJson assignment.aux_length),
      ("vars", toJson vars.toArray),
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
      ("row", reprStr i),
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
