module

public import Clean.Air.WitnessGeneration.State

@[expose] public section

/-!
# Assembling generated tables

Turns the generated rows of every component into the tables of an ensemble witness, checking the
facts that the witness type requires: row widths, table heights and fixed cells.
-/

namespace Air.Flat.WitnessGeneration

variable {F : Type} [FiniteField F]

structure AssembledTables (components : List (Component F)) where
  tables : List (Table F)
  same_length : components.length = tables.length
  same_circuits : ∀ index (hindex : index < components.length),
    components[index] = tables[index].component

def assembleTables :
    (components : List (Component F)) → List (ComponentState F) →
      Except GenerationError (AssembledTables components)
  | [], [] => .ok {
      tables := []
      same_length := rfl
      same_circuits := by simp
    }
  | component :: components, state :: states => do
      let rows := state.rows.map (·.values)
      if hlength : rows.length > UInt64.size then
        throw (.assembly s!"generated table for component '{component.circuit.name}' has more \
          than 2^64 rows")
      else if h : ∀ row ∈ rows, row.size = component.width then
        if hfixed : component.FixedRowsMatch rows then do
          let table : Table F := {
            component
            table := rows
            -- replaced by the ensemble's derived data in `generateValid`
            data := fun _ _ => #[]
            uniform_width := h
            length_le := Nat.le_of_not_lt hlength
            fixed_rows_match := hfixed
          }
          let rest ← assembleTables components states
          return {
            tables := table :: rest.tables
            same_length := by simp [rest.same_length]
            same_circuits := by
              intro index hindex
              cases index with
              | zero => rfl
              | succ index =>
                  simp only [List.getElem_cons_succ]
                  exact rest.same_circuits index (by simp at hindex; omega)
          }
        else
          throw (.assembly "generated table does not match its fixed columns")
      else
        throw (.assembly "generated table contains a row of the wrong width")
  | _, _ => .error (.assembly "generated-table count does not match ensemble component count")

end Air.Flat.WitnessGeneration
