import Clean.Circuit.Provable
variable {F: Type} [Field F] {α : Type} {n : ℕ}
variable {Row : TypeMap} [ProvableType Row]

/--
`Table` models a lookup table, by letting you specify a defining property `contains`
that all rows in the table must satisfy.

This representation is deliberately not very concrete, to allow for cases where e.g. the table
is only built after all lookups into it are defined.

In principle, the type allows you to define "impossible" tables, e.g. `contains _ := False`, and use
them in a circuit, yielding spurious correctness proofs. To avoid this, it is encouraged to only define
tables via auxiliary constructions like `StaticTable` or `LookupCircuit`, which guarantee the table
can be instantiated into a concrete table of field elements, such that `contains` can be proved to hold
for every row.
-/
structure Table (F : Type) (Row : TypeMap) [ProvableType Row] where
  name : String
  /--
  `contains` captures what it means to be in the table.
  -/
  Contains : Row F → Prop

  /--
  we allow to rewrite the `contains` property into two statements that are easier to work with
  in the context of soundness and completeness proofs.
  -/
  Soundness : Row F → Prop
  Completeness : Row F → Prop

  imply_soundness : ∀ row, Contains row → Soundness row
  implied_by_completeness : ∀ row, Completeness row → Contains row

/--
`RawTable` replaces the custom `Row` type with plain vector-valued entries, which
simplifies definitions and arguments in the core framework.

User-facing code should use `Table` instead.
-/
structure RawTable (F : Type) where
  name : String
  arity : ℕ
  Contains : Vector F arity → Prop
  Soundness : Vector F arity → Prop
  Completeness : Vector F arity → Prop
  imply_soundness : ∀ row, Contains row → Soundness row
  implied_by_completeness : ∀ row, Completeness row → Contains row

structure Lookup (F : Type) where
  table: RawTable F
  entry: Vector (Expression F) table.arity

instance [Repr F] : Repr (Lookup F) where
  reprPrec l _ := "(Lookup " ++ l.table.name ++ " " ++ repr l.entry ++ ")"

@[circuit_norm]
def Table.toRaw (table: Table F Row) : RawTable F where
  name := table.name
  arity := size Row
  Contains row := table.Contains (from_elements row)
  Soundness row := table.Soundness (from_elements row)
  Completeness row := table.Completeness (from_elements row)
  imply_soundness row := table.imply_soundness (from_elements row)
  implied_by_completeness row := table.implied_by_completeness (from_elements row)

variable {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]

structure StaticTable (F : Type) (Row : TypeMap) [ProvableType Row] where
  name: String
  length: ℕ
  row: Fin length → Row F
  -- TODO this would make sense if we had separate input and output types,
  -- and the lookup would automatically witness the output given the input.
  -- then we could weaken completeness to be `index input < length`!
  index: Row F → ℕ
  Soundness: Row F → Prop
  Completeness: Row F → Prop
  imply_soundness : ∀ t, (∃ i, t = row i) → Soundness t
  implied_by_completeness : ∀ t, Completeness t → ∃ i, t = row i

namespace StaticTable
def Contains (table: StaticTable F Row) (row: Row F) :=
  ∃ i : Fin table.length, row = table.row i

@[circuit_norm]
def toTable (table: StaticTable F Row) : Table F Row where
  name := table.name
  Contains := table.Contains
  Soundness := table.Soundness
  Completeness := table.Completeness
  imply_soundness := table.imply_soundness
  implied_by_completeness := table.implied_by_completeness
end StaticTable

@[circuit_norm]
def Table.fromStatic (table: StaticTable F Row) : Table F Row :=
  StaticTable.toTable table
