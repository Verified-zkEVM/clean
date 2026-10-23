module

public import Clean.Air.FlatEnsemble

@[expose] public section

/-!
# Hints and prepared rows

Witness programs read hints, the views of the prover's private input that an ensemble's hint tables
describe, and prover data. The witness generator reads both for every row it completes. Both are
functions of a name and a width, so building them from the rows would cost time proportional to
the rows on every read. Instead, the generator prepares the rows once, and reads them with
`readNamedRows`.
-/

namespace Air.Flat

variable {F : Type} [FiniteField F]

/-- The hint tables `tables` take from the flattened private input `elements`. Like derived prover
data, rows are cut off or zero-padded at the requested width. -/
def HintTable.hint (tables : List HintTable) (elements : Array F) : ProverHint F := fun key width =>
  match tables.find? (·.key == key) with
  | none => #[]
  | some table => Array.ofFn fun (row : Fin table.rows) => rowPrefix width <|
      elements.extract (table.offset + row.val * table.width)
        (table.offset + (row.val + 1) * table.width)

namespace WitnessGeneration

/-- Rows that witness programs read as prover data or hints: at width `n`, every row is cut off or
padded with zeros. The rows at `width`, their usual read width, are prepared once, so that reads at
that width don't copy them. -/
structure PreparedRows (F : Type) [FiniteField F] where
  rows : Array (Array F)
  width : ℕ
  prepared : Array (Vector F width)
  prepared_eq : prepared = rows.map (rowPrefix width)

def PreparedRows.ofRows (rows : Array (Array F)) (width : ℕ) : PreparedRows F :=
  { rows, width, prepared := rows.map (rowPrefix width), prepared_eq := rfl }

def PreparedRows.read (rows : PreparedRows F) (n : ℕ) : Array (Vector F n) :=
  if h : rows.width = n then h ▸ rows.prepared else rows.rows.map (rowPrefix n)

lemma PreparedRows.read_eq (rows : PreparedRows F) (n : ℕ) :
    rows.read n = rows.rows.map (rowPrefix n) := by
  unfold read
  split
  · rename_i h
    subst h
    exact rows.prepared_eq
  · rfl

/-- Prepared rows under names, read like prover data or hints. -/
def readNamedRows (entries : List (String × PreparedRows F)) (name : String) (n : ℕ) :
    Array (Vector F n) :=
  match entries.find? (·.1 == name) with
  | some (_, rows) => rows.read n
  | none => #[]

/-- The hint tables prepared for reading, see `readNamedRows_prepareHint`. -/
def prepareHint (tables : List HintTable) (elements : Array F) :
    List (String × PreparedRows F) :=
  tables.map fun table =>
    (table.key, .ofRows (Array.ofFn fun (row : Fin table.rows) =>
      elements.extract (table.offset + row.val * table.width)
        (table.offset + (row.val + 1) * table.width)) table.width)

lemma readNamedRows_prepareHint (tables : List HintTable) (elements : Array F) :
    readNamedRows (prepareHint tables elements) = HintTable.hint tables elements := by
  funext key width
  simp only [readNamedRows, prepareHint, HintTable.hint, List.find?_map, Function.comp_def]
  cases tables.find? (fun table => table.key == key) <;>
    simp [PreparedRows.read_eq, PreparedRows.ofRows, Array.map_ofFn, Function.comp_def]

end WitnessGeneration

end Air.Flat
