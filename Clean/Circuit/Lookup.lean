import Clean.Circuit.Provable
variable {F : Type} [Field F] {α : Type} {n : ℕ}
variable {Row : TypeMap} [ProvableType Row]

/--
`Table` models a lookup table, by letting you specify a defining property `Contains`
that all rows in the table must satisfy.

This representation is deliberately not very concrete, to allow for cases where e.g. the table
is only built after all lookups into it are defined.

In principle, the type allows you to define "impossible" tables, e.g. `Contains _ := False`, and use
them in a circuit, yielding spurious correctness proofs. To avoid this, it is encouraged to only define
tables via auxiliary constructions like `StaticTable` or `LookupCircuit`, which guarantee the table
can be instantiated into a concrete table of field elements, such that `Contains` can be proved to hold
for every row.
-/
structure Table (F : Type) (Row : TypeMap) [ProvableType Row] where
  name : String
  /--
  `Contains` captures what it means to be in the table.
  -/
  Contains : Array (Row F) → Row F → Prop

  /--
  we allow to rewrite the `Contains` property into two statements that are easier to work with
  in the context of soundness and completeness proofs.
  -/
  Soundness : Array (Row F) → Row F → Prop := Contains
  Completeness : Array (Row F) → Row F → Prop := Contains

  imply_soundness : ∀ table row, Contains table row → Soundness table row
    := by intros; assumption
  implied_by_completeness : ∀ table row, Completeness table row → Contains table row
    := by intros; assumption

/--
`RawTable` replaces the custom `Row` type with plain vector-valued entries, which
simplifies definitions and arguments in the core framework.

User-facing code should use `Table` instead.
-/
structure RawTable (F : Type) where
  name : String
  arity : ℕ
  Contains : Array (Vector F arity) → Vector F arity → Prop
  Soundness : Array (Vector F arity) → Vector F arity → Prop
  Completeness : Array (Vector F arity) → Vector F arity → Prop
  imply_soundness : ∀ table row, Contains table row → Soundness table row
  implied_by_completeness : ∀ table row, Completeness table row → Contains table row

structure Lookup (F : Type) where
  table : RawTable F
  entry : Vector (Expression F) table.arity

instance [Repr F] : Repr (Lookup F) where
  reprPrec l _ := "(Lookup " ++ l.table.name ++ " " ++ repr l.entry ++ ")"

def Table.toRaw (table : Table F Row) : RawTable F where
  name := table.name
  arity := size Row
  Contains t row := table.Contains (t.map fromElements) (fromElements row)
  Soundness t row := table.Soundness (t.map fromElements) (fromElements row)
  Completeness t row := table.Completeness (t.map fromElements) (fromElements row)
  imply_soundness _ row := table.imply_soundness _ (fromElements row)
  implied_by_completeness _ row := table.implied_by_completeness _ (fromElements row)

def Environment.getTable (env : Environment F) {Row : TypeMap} [ProvableType Row]
  (table : Table F Row) : Array (Row F) :=
  env.tables table.name (size Row) |>.map fromElements

namespace Lookup
variable {F : Type} [Field F]

def Contains (lookup : Lookup F) (env : Environment F) : Prop :=
  lookup.table.Contains (env.tables lookup.table.name lookup.table.arity)
    (lookup.entry.map env)

def Soundness (lookup : Lookup F) (env : Environment F) : Prop :=
  lookup.table.Soundness (env.tables lookup.table.name lookup.table.arity)
    (lookup.entry.map env)

def Completeness (lookup : Lookup F) (env : Environment F) : Prop :=
  lookup.table.Completeness (env.tables lookup.table.name lookup.table.arity)
    (lookup.entry.map env)

@[circuit_norm]
lemma soundess_def {Row : TypeMap} [ProvableType Row]
  (table : Table F Row) (env : Environment F) (entry : Row (Expression F)) :
    let lookup : Lookup F := { table := table.toRaw, entry := toElements entry };
    lookup.Soundness env ↔ table.Soundness (env.getTable table) (eval env entry) := by
  rfl

@[circuit_norm]
lemma soundess_def_field {F : Type} [Field F]
  (table : Table F field) (env : Environment F) (entry : Expression F) :
    let lookup : Lookup F := { table := table.toRaw, entry := #v[entry] };
    lookup.Soundness env ↔ table.Soundness (env.getTable table) (entry.eval (F:=F) env) := by
  simp only [Soundness, Table.toRaw, id_eq, Vector.map_mk, List.map_toArray, List.map_cons,
    List.map_nil]
  rfl

@[circuit_norm]
lemma completeness_def {Row : TypeMap} [ProvableType Row]
  (table : Table F Row) (env : Environment F) (entry : Row (Expression F)) :
    let lookup : Lookup F := { table := table.toRaw, entry := toElements entry };
    lookup.Completeness env ↔ table.Completeness (env.getTable table) (eval env entry) := by
  rfl

@[circuit_norm]
lemma completeness_def_field {F : Type} [Field F]
  (table : Table F field) (env : Environment F) (entry : Expression F) :
    let lookup : Lookup F := { table := table.toRaw, entry := #v[entry] };
    lookup.Completeness env ↔ table.Completeness (env.getTable table) (entry.eval (F:=F) env) := by
  simp only [Completeness, Table.toRaw, id_eq, Vector.map_mk, List.map_toArray, List.map_cons,
    List.map_nil]
  rfl
end Lookup

variable {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]

structure StaticTable (F : Type) (Row : TypeMap) [ProvableType Row] where
  name : String
  length : ℕ
  row : Fin length → Row F
  -- TODO this would make sense if we had separate input and output types,
  -- and the lookup would automatically witness the output given the input.
  -- then we could weaken completeness to be `index input < length`!
  index : Row F → ℕ
  Spec : Row F → Prop
  contains_iff : ∀ t, (∃ i, t = row i) ↔ Spec t

namespace StaticTable
def Contains (table : StaticTable F Row) (row : Row F) :=
  ∃ i : Fin table.length, row = table.row i

@[circuit_norm]
def toTable (table : StaticTable F Row) : Table F Row where
  name := table.name
  Contains _ row := ∃ i, row = table.row i
  Soundness _ := table.Spec
  Completeness _ := table.Spec
  imply_soundness _ row := (table.contains_iff row).mp
  implied_by_completeness _ row := (table.contains_iff row).mpr
end StaticTable

@[circuit_norm]
def Table.fromStatic (table : StaticTable F Row) : Table F Row :=
  StaticTable.toTable table
