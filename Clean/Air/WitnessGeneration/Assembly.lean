module

public import Clean.Air.WitnessGeneration.State

@[expose] public section

/-!
# Assembling generated tables

Turns the generated rows of every component into the tables of an ensemble witness, checking the
facts that the witness type requires: row widths, table heights, fixed columns and windows. The
window cells of two-row components are filled in here, once the rows are final.
-/

namespace Air.Flat.WitnessGeneration

variable {F : Type} [FiniteField F]

structure AssembledTables (components : List (Component F)) where
  tables : List (Table F)
  same_length : components.length = tables.length
  same_circuits : ∀ index (hindex : index < components.length),
    components[index] = tables[index].component

structure MatchedFixedRows (component : Component F) (rows : List (Array F)) where
  marker : Unit := ()
  property : component.FixedRowsMatch rows

def validateFixedRows (component : Component F) (rows : List (Array F)) :
    Except GenerationError (MatchedFixedRows component rows) :=
  match hcolumns : component.fixedColumns with
  | none => .ok ⟨(), by simp [Component.FixedRowsMatch, hcolumns]⟩
  | some fixed =>
      if hrows : FixedColumns.RowsMatch fixed rows then
        .ok ⟨(), by simpa [Component.FixedRowsMatch, hcolumns] using hrows⟩
      else
        .error (.assembly "generated table does not match its fixed columns")

structure MatchedWindows (component : Component F) (rows : List (Array F)) where
  marker : Unit := ()
  property : component.WindowsMatch rows

def validateWindows (component : Component F) (rows : List (Array F)) :
    Except GenerationError (MatchedWindows component rows) :=
  if hrows : component.WindowsMatch rows then .ok ⟨(), hrows⟩
  else .error (.assembly "generated table does not match its windows")

/-- The rows of a two-row component, with their window cells filled from the next rows and the
selectors. -/
def fillWindows (component : Component F) (rows : List (Array F)) : List (Array F) :=
  match component.window with
  | none => rows
  | some layout =>
      let width := layout.rowWidth
      rows.zipIdx.map fun (row, i) =>
        let next := rows[(i + 1) % rows.length]?.getD #[]
        let last := i + 1 = rows.length
        let selectors : Array F :=
          #[if i = 0 then 1 else 0, if last then 1 else 0, if last then 0 else 1]
        row.extract 0 width ++ next.extract 0 width ++ selectors ++
          row.extract (2 * width + 3) row.size

def assembleTables :
    (components : List (Component F)) → List (ComponentState F) →
      Except GenerationError (AssembledTables components)
  | [], [] => .ok {
      tables := []
      same_length := rfl
      same_circuits := by simp
    }
  | component :: components, state :: states => do
      let rows := fillWindows component (state.rows.map (·.values))
      if hlength : rows.length > UInt64.size then
        throw (.assembly s!"generated table for component '{component.circuit.name}' has more \
          than 2^64 rows")
      else if h : ∀ row ∈ rows, row.size = component.width then
        match validateFixedRows component rows, validateWindows component rows with
        | .error error, _ | _, .error error => .error error
        | .ok matched, .ok windows => do
          let table : Table F := {
            component
            table := rows
            -- replaced by the ensemble's derived data in `generateValid`
            data := fun _ _ => #[]
            uniform_width := h
            length_le := Nat.le_of_not_lt hlength
            fixed_rows_match := matched.property
            windows_match := windows.property
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
        throw (.assembly "generated table contains a row of the wrong width")
  | _, _ => .error (.assembly "generated-table count does not match ensemble component count")

end Air.Flat.WitnessGeneration
