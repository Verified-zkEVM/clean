/-
The `TableContext`: a bundle of committed traces sharing one prover data object, together with
the derivation of `ProverData` from those traces.

Nothing here depends on how many rows an environment spans. `deriveProverData` is keyed on trace
*rows* -- a transition table is constrained on windows, but its data is still one input row per
row -- and every `TableContext` operation quantifies over each table's `envs`.
-/
import Clean.Air.TransitionComponent

namespace Air.Flat
variable {F : Type} [FiniteField F]

namespace Table

/--
Each named component is the source of its circuit-input rows in `ProverData`.

Keyed on rows, not environments: a transition table is constrained on windows, but its *data* is
still one input row per trace row, so this does not depend on `windowRows`.
-/
def deriveProverData : List (Table F) → ProverData F
  | [] => fun _ _ => #[]
  | table :: tables => fun name n =>
      if table.component.circuit.name = name then table.proverRows n
      else deriveProverData tables name n

lemma deriveProverData_eq_of_mem (tables : List (Table F))
    (hunique : (tables.map (fun table => table.component.circuit.name)).Nodup)
    {table : Table F} (hmem : table ∈ tables) (n : ℕ) :
    deriveProverData tables table.component.circuit.name n = table.proverRows n := by
  induction tables with
  | nil => simp at hmem
  | cons head tail ih =>
      simp only [List.map_cons, List.nodup_cons] at hunique
      obtain ⟨hhead, htail⟩ := hunique
      simp only [List.mem_cons] at hmem
      rcases hmem with rfl | hmem
      · simp [deriveProverData]
      · have hne : head.component.circuit.name ≠ table.component.circuit.name := by
          intro heq
          apply hhead
          rw [heq]
          exact List.mem_map.mpr ⟨table, hmem, rfl⟩
        simp [deriveProverData, hne, ih htail hmem]

/-- `DataConsistency` restated through the accessors, so it can be discharged uniformly. -/
lemma dataConsistency_iff (table : Table F) (data : ProverData F) :
    table.DataConsistency data ↔
      data table.component.circuit.name (size table.component.Input) =
        table.proverRows (size table.component.Input) := Iff.rfl

/--
Number of environments a table contributes, in terms of its row count.

A component with `windowRows = w` contributes `length + 1 - w` environments: one per row when
`w = 1`, one per adjacent pair (`length - 1`) when `w = 2`. This is what any bound on total
interaction count must use -- in particular the `< ringChar F` side condition carried by
`BalancedInteractions`, since a forged balance becomes possible if `p` copies of a push are
allowed to sum to zero.
-/
@[circuit_norm] lemma envs_length (table : Table F) (data : ProverData F) :
    (table.envs data).length =
      table.table.length + 1 - table.component.windowRows := by
  simp [Table.envs_eq, Table.windows_length]

end Table

/-- A table subset together with the shared prover-data environment used to interpret it.

Every operation below quantifies over each table's `envs`, so it applies uniformly to any
window size. -/
structure TableContext (F : Type) [FiniteField F] where
  tables : List (Table F)
  data : ProverData F
  data_consistent : ∀ table ∈ tables, table.DataConsistency data

namespace TableContext
def cons (table : Table F) (tables : TableContext F)
    (consistent : table.DataConsistency tables.data) : TableContext F where
  tables := table :: tables.tables
  data := tables.data
  data_consistent := by
    simp [consistent]
    apply tables.data_consistent

@[circuit_norm] lemma cons_tables {table : Table F} {tables : TableContext F} (consistent) :
  (cons table tables consistent).tables = table :: tables.tables := rfl

@[circuit_norm] lemma cons_data {table : Table F} {tables : TableContext F} (consistent) :
  (cons table tables consistent).data = tables.data := rfl

def induct {motive : TableContext F → Sort*}
  (nil : ∀ data, motive ⟨ [], data, by simp ⟩)
  (cons : ∀ table tables consistent, motive tables → motive (cons table tables consistent))
    (tables : TableContext F) : motive tables := by
  rcases tables with ⟨ ts, data, data_consistent ⟩
  induction ts with
  | nil => exact nil data
  | cons table ts ih =>
    have data_consistent' : ∀ table ∈ ts, table.DataConsistency data := by
      intro table h_table
      apply data_consistent
      simp [h_table]
    let tables : TableContext F := ⟨ ts, data, data_consistent' ⟩
    have consistent : table.DataConsistency tables.data := by
      simp [tables]
      exact data_consistent table (by simp)
    apply cons table tables consistent
    exact ih data_consistent'

def append (tables1 tables2 : TableContext F) (data_eq : tables1.data = tables2.data) : TableContext F where
  tables := tables1.tables ++ tables2.tables
  data := tables1.data
  data_consistent := by
    simp [or_imp, forall_and]
    constructor
    · apply tables1.data_consistent
    rw [data_eq]
    apply tables2.data_consistent

@[circuit_norm] lemma append_tables {tables1 tables2 : TableContext F} (data_eq : tables1.data = tables2.data) :
  (append tables1 tables2 data_eq).tables = tables1.tables ++ tables2.tables := rfl

@[circuit_norm] lemma append_data {tables1 tables2 : TableContext F} (data_eq : tables1.data = tables2.data) :
  (append tables1 tables2 data_eq).data = tables1.data := rfl

@[circuit_norm] lemma cons_append {table : Table F} {tables1 tables2 : TableContext F}
  (consistent : table.DataConsistency tables1.data) (data_eq : tables1.data = tables2.data) :
  (cons table tables1 consistent).append tables2 data_eq =
    cons table (append tables1 tables2 data_eq) consistent := rfl

@[circuit_norm]
abbrev components (tables : TableContext F) : List (Component F) :=
  tables.tables.map (·.component)

abbrev Constraints (tables : TableContext F) : Prop :=
  ∀ table ∈ tables.tables, table.Constraints tables.data

abbrev Assumptions (tables : TableContext F) : Prop :=
  ∀ table ∈ tables.tables, table.Assumptions tables.data

noncomputable abbrev interactionsWith (tables : TableContext F) (channel : RawChannel F) : List (Interaction F) :=
  tables.tables.flatMap (·.interactionsWith tables.data channel)

@[circuit_norm] lemma interactionsWith_cons {table : Table F} {tables : TableContext F}
  (consistent : table.DataConsistency tables.data) {channel : RawChannel F} :
  interactionsWith (cons table tables consistent) channel =
    table.interactionsWith tables.data channel ++ interactionsWith tables channel := by
  simp [interactionsWith, circuit_norm]

@[circuit_norm] lemma interactionsWith_append {tables1 tables2 : TableContext F}
  (data_eq : tables1.data = tables2.data) {channel : RawChannel F} :
  interactionsWith (append tables1 tables2 data_eq) channel =
    interactionsWith tables1 channel ++ interactionsWith tables2 channel := by
  simp only [interactionsWith, append, List.flatMap_append]
  rw [data_eq]
end TableContext

end Air.Flat
