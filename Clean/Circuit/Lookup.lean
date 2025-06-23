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
  contains : Row F → Prop

  /--
  we allow to rewrite the `contains` property into two statements that are easier to work with
  in the context of soundness and completeness proofs.
  -/
  soundness : Row F → Prop
  completeness : Row F → Prop

  imply_soundness : ∀ row, contains row → soundness row
  implied_by_completeness : ∀ row, completeness row → contains row

/--
`RawTable` replaces the custom `Row` type with plain vector-valued entries, which
simplifies definitions and arguments in the core framework.

User-facing code should use `Table` instead.
-/
structure RawTable (F : Type) where
  name : String
  arity : ℕ
  contains : Vector F arity → Prop
  soundness : Vector F arity → Prop
  completeness : Vector F arity → Prop
  imply_soundness : ∀ row, contains row → soundness row
  implied_by_completeness : ∀ row, completeness row → contains row

structure Lookup (F : Type) where
  table: RawTable F
  entry: Vector (Expression F) table.arity

instance [Repr F] : Repr (Lookup F) where
  reprPrec l _ := "(Lookup " ++ l.table.name ++ " " ++ repr l.entry ++ ")"

@[circuit_norm]
def Table.toRaw (table: Table F Row) : RawTable F where
  name := table.name
  arity := size Row
  contains row := table.contains (from_elements row)
  soundness row := table.soundness (from_elements row)
  completeness row := table.completeness (from_elements row)
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
  soundness: Row F → Prop
  completeness: Row F → Prop
  imply_soundness : ∀ t, (∃ i, t = row i) → soundness t
  implied_by_completeness : ∀ t, completeness t → ∃ i, t = row i

namespace StaticTable
def contains (table: StaticTable F Row) (row: Row F) :=
  ∃ i : Fin table.length, row = table.row i

@[circuit_norm]
def toTable (table: StaticTable F Row) : Table F Row where
  name := table.name
  contains := table.contains
  soundness := table.soundness
  completeness := table.completeness
  imply_soundness := table.imply_soundness
  implied_by_completeness := table.implied_by_completeness
end StaticTable

@[circuit_norm]
def Table.fromStatic (table: StaticTable F Row) : Table F Row :=
  StaticTable.toTable table
