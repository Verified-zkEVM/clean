import Clean.Circuit.Provable
variable {F: Type} [Field F] {α : Type} {n : ℕ}

structure Table (F : Type) where
  name : String
  arity : ℕ
  /--
  `contains` captures what it means to be in the table.
  there should be a concrete way of instantiating the table where `contains` is proved to hold on every row.
  -/
  contains : Vector F arity → Prop

  /--
  we allow to rewrite the `contains` property into two statements that are easier to work with
  in the context of soundness and completeness proofs.
  -/
  soundness : Vector F arity → Prop
  completeness : Vector F arity → Prop

  imply_soundness : ∀ row, contains row → soundness row
  implied_by_completeness : ∀ row, completeness row → contains row

structure Lookup (F : Type) where
  table: Table F
  entry: Vector (Expression F) table.arity

instance [Repr F] : Repr (Lookup F) where
  reprPrec l _ := "(Lookup " ++ l.table.name ++ " " ++ repr l.entry ++ ")"

-- usually we want lookups to be properly typed, with input and output types.
variable {Row : TypeMap} [ProvableType Row]

structure TypedTable (F : Type) (Row : TypeMap) [ProvableType Row] where
  name : String
  contains : Row F → Prop
  soundness : Row F → Prop
  completeness : Row F → Prop
  imply_soundness : ∀ row, contains row → soundness row
  implied_by_completeness : ∀ row, completeness row → contains row

structure TypedLookup (F : Type) (Row : TypeMap) [ProvableType Row] where
  table: TypedTable F Row
  entry: Row (Expression F)

@[circuit_norm]
def TypedTable.toUntyped (table: TypedTable F Row) : Table F where
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
def toTable (table: StaticTable F Row) : TypedTable F Row where
  name := table.name
  contains := table.contains
  soundness := table.soundness
  completeness := table.completeness
  imply_soundness := table.imply_soundness
  implied_by_completeness := table.implied_by_completeness

end StaticTable
