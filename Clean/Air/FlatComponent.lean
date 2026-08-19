/-
AIR tables: a concrete trace for one component, checked on each window of its rows.

The `Component` structure itself, its `instantiate` transport lemmas, and every trace-level
predicate and interaction-collection definition live in `Clean/Air/Component.lean`. What is
specific to the trace is only:

* the `Table` itself, whose environments are the component's row *windows*, and
* `circuitAssumptions`, which supplies the fixed-row and derived-data facts at each row index.

There is a single `Table` type for both AIR styles. How many rows an environment spans is read
off `component.windowRows`, so a flat table (`windowRows = 1`) and a transition table
(`windowRows = 2`) differ only in that field -- not in their type, and not in a separate tag the
prover could reinterpret.
-/
import Clean.Air.Component

namespace Air.Flat
variable {F : Type} [FiniteField F]
variable {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]

namespace Component

/-- Width of a trace row: the component's committed cells per row. -/
abbrev width (component : Component F) : ℕ := component.rowWidth

end Component

/-- A concrete trace for one AIR component. Its data environment belongs to the ensemble. -/
structure Table (F : Type) [FiniteField F] where
  component : Component F
  table : List (Array F)
  uniform_width : ∀ row ∈ table, row.size = component.width
  /-- Connects the row-indexed fixed-column declaration to the concrete semantic rows. -/
  fixed_rows_match : component.fixedRowsMatch table := by
    simp [Component.fixedRowsMatch]

namespace Table

/--
The window starting at row `i`: `windowRows` consecutive rows laid side by side.

Cell `j` of the window is cell `j % rowWidth` of row `i + j / rowWidth`. For `windowRows = 1`
this is just the row; for `windowRows = 2` it is `curr ++ next`, where cell `rowWidth + j` is
`next[j]` -- so "next row" is an index offset, needing no new `Expression` node.
-/
def windowRow (t : Table F) (i : ℕ) : Array F :=
  ((List.range t.component.windowRows).map fun k => t.table[i + k]!).foldl (· ++ ·) #[]

/-- The environment of the window starting at row `i`. -/
@[circuit_norm]
def windowEnv (t : Table F) (i : ℕ) (data : ProverData F) : Environment F :=
  Environment.fromArray (t.windowRow i) data

/--
Every window of the trace, each tagged with the index of its *first* row.

There are `length - windowRows + 1` of them: a window needs `windowRows` rows to exist, so a
trace shorter than that is entirely unconstrained. For `windowRows = 1` this is every row; for
`windowRows = 2` it is every adjacent pair, matching `TableOperation.everyRowExceptLast`.

The index is carried explicitly rather than recovered from membership, because `FixedRowAt` and
`DataRowAt` are keyed on the first row's index.
-/
def windows (t : Table F) : List ℕ :=
  List.range (t.table.length + 1 - t.component.windowRows)

@[circuit_norm] lemma windows_length (t : Table F) :
    t.windows.length = t.table.length + 1 - t.component.windowRows := by
  simp [windows]

lemma mem_windows_iff {t : Table F} {i : ℕ} :
    i ∈ t.windows ↔ i + t.component.windowRows ≤ t.table.length := by
  simp only [windows, List.mem_range]
  omega

/-- The first row of any window is a row of the trace. -/
lemma lt_length_of_mem_windows {t : Table F} {i : ℕ} (h : i ∈ t.windows) :
    i < t.table.length := by
  rw [mem_windows_iff] at h
  have := t.component.windowRows_pos
  omega

end Table

/-- A table is checked once per window of its rows. -/
instance : RowEnvs F (Table F) where
  component table := table.component
  envs table data := table.windows.map (table.windowEnv · data)
  data_eq := by
    intro table data e he
    simp only [List.mem_map] at he
    obtain ⟨i, _, rfl⟩ := he
    rfl

@[circuit_norm] lemma Table.envs_eq (table : Table F) (data : ProverData F) :
    RowEnvs.envs table data = table.windows.map (table.windowEnv · data) := rfl

/-- A window of the trace is one of the environments the table is checked at. -/
lemma Table.mem_envs_of_mem_windows {table : Table F} {i : ℕ} (hi : i ∈ table.windows)
    {data : ProverData F} :
    table.windowEnv i data ∈ RowEnvs.envs (F:=F) table data := by
  simp only [Table.envs_eq, List.mem_map]
  exact ⟨i, hi, rfl⟩

/-- For a flat component the window at `i` is just row `i`. -/
lemma Table.windowRow_of_flat {table : Table F}
    (h : table.component.windowRows = 1) (i : ℕ) :
    table.windowRow i = table.table[i]! := by
  simp [Table.windowRow, h]

/-- A flat table is checked once per row, against that row alone. -/
lemma Table.envs_eq_of_flat (table : Table F) (data : ProverData F)
    (h : table.component.windowRows = 1) :
    RowEnvs.envs table data = table.table.map (Environment.fromArray · data) := by
  simp only [Table.envs_eq, Table.windowEnv, Table.windowRow_of_flat h]
  rw [show table.windows = List.range table.table.length by simp [Table.windows, h]]
  apply List.ext_getElem
  · simp
  intro i h₁ h₂
  simp only [List.getElem_map, List.getElem_range] at *
  congr 1
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using h₂)]; rfl

@[circuit_norm] lemma Table.component_eq (table : Table F) :
    RowEnvs.component (F:=F) table = table.component := rfl

/-- Each named component is the source of its circuit-input rows in `ProverData`. -/
def deriveProverData : List (Table F) → ProverData F
  | [] => fun _ _ => #[]
  | table :: tables => fun name n =>
      if table.component.circuit.name = name then table.component.proverRows table.table n
      else deriveProverData tables name n

lemma deriveProverData_eq_of_mem (tables : List (Table F))
    (hunique : (tables.map (fun table => table.component.circuit.name)).Nodup)
    {table : Table F} (hmem : table ∈ tables) (n : ℕ) :
    deriveProverData tables table.component.circuit.name n = table.component.proverRows table.table n := by
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

namespace Table
variable {table : Table F} {data : ProverData F} {channel : RawChannel F}

def proverRows (table : Table F) (n : ℕ) : Array (Vector F n) :=
  table.component.proverRows table.table n

def DataConsistency (table : Table F) (data : ProverData F) : Prop :=
  table.component.DataConsistency table.table data

abbrev length (t : Table F) : ℕ := t.table.length

theorem ext_iff {table1 table2 : Table F} :
    table1 = table2 ↔
    table1.component = table2.component ∧
    table1.table = table2.table := by
  cases table1
  cases table2
  simp only [mk.injEq]

/-
Trace-level predicates and interaction collection, stated exactly as they were before the shared
`RowEnvs` layer existed: quantified over the trace's *rows*, with each row read as
`Environment.fromArray row data`.

The shared layer quantifies over environments instead, because a transition table constrains a
*pair* of rows and so the two kinds have no common row type. For the flat kind that distinction is
invisible -- its environments are exactly its rows -- so the row-shaped statements are kept here as
the primary spelling, and `envs_iff` below is the single lemma relating the two. Everything proved
over `RowEnvs` is then re-exported in row-shaped form.
-/

/-- Quantifying over a *flat* table's environments is quantifying over its rows.

Only valid when `windowRows = 1`; a transition table's environments are pairs of rows, which have
no row-shaped spelling. Callers that only ever build flat tables (VM ensembles, for instance) use
this to keep reasoning about rows. -/
lemma envs_iff {motive : Environment F → Prop} (table : Table F) (data : ProverData F)
    (h : table.component.windowRows = 1) :
    (∀ env ∈ RowEnvs.envs (F:=F) table data, motive env) ↔
      ∀ row ∈ table.table, motive (Environment.fromArray row data) := by
  rw [envs_eq_of_flat table data h]
  simp only [List.mem_map, forall_exists_index, and_imp]
  constructor
  · intro h' row hrow; exact h' _ row hrow rfl
  · intro h' e row hrow heq; subst heq; exact h' row hrow

@[circuit_norm]
def channelsWithGuarantees (table : Table F) : List (RawChannel F) :=
  table.component.circuit.channelsWithGuarantees

@[circuit_norm]
def channelsWithRequirements (table : Table F) : List (RawChannel F) :=
  table.component.circuit.channelsWithRequirements

/-
The trace-level predicates are the shared `RowEnvs` ones, quantified over the table's *windows*.

Before the window generalization these were stated row-shaped, which is only correct when
`windowRows = 1`. They are now `abbrev`s over `RowEnvs`, exactly as the transition kind always
had them, so a flat and a transition table share one spelling; `envs_iff` above recovers the
row-shaped reading for flat callers.
-/

abbrev Constraints (table : Table F) (data : ProverData F) : Prop :=
  RowEnvs.Constraints (F:=F) table data

abbrev Assumptions (table : Table F) (data : ProverData F) : Prop :=
  RowEnvs.Assumptions (F:=F) table data

abbrev Guarantees (table : Table F) (data : ProverData F) : Prop :=
  RowEnvs.Guarantees (F:=F) table data

abbrev ChannelGuarantees (table : Table F) (data : ProverData F) (channel : RawChannel F) : Prop :=
  RowEnvs.ChannelGuarantees (F:=F) table data channel

abbrev InChannelsOrGuarantees (table : Table F) (data : ProverData F)
    (channels : List (RawChannel F)) : Prop :=
  RowEnvs.InChannelsOrGuarantees (F:=F) table data channels

abbrev Requirements (table : Table F) (data : ProverData F) : Prop :=
  RowEnvs.Requirements (F:=F) table data

abbrev ChannelRequirements (table : Table F) (data : ProverData F) (channel : RawChannel F) : Prop :=
  RowEnvs.ChannelRequirements (F:=F) table data channel

abbrev InChannelsOrRequirements (table : Table F) (data : ProverData F)
    (channels : List (RawChannel F)) : Prop :=
  RowEnvs.InChannelsOrRequirements (F:=F) table data channels

abbrev Spec (table : Table F) (data : ProverData F) : Prop :=
  RowEnvs.Spec (F:=F) table data

abbrev interactions (table : Table F) (data : ProverData F) : List (Interaction F) :=
  RowEnvs.interactions (F:=F) table data

noncomputable abbrev interactionsWith (table : Table F) (data : ProverData F)
    (channel : RawChannel F) : List (Interaction F) :=
  RowEnvs.interactionsWith (F:=F) table data channel

noncomputable abbrev interactionssWith (table : Table F) (data : ProverData F)
    (channel : RawChannel F) : List (List (Interaction F)) :=
  RowEnvs.interactionssWith (F:=F) table data channel

/-! The `RowEnvs` iff-lemmas, re-exported at `Table` so that call sites can `rw` against goals
stated through the abbreviations above. The abbreviations are reducible enough for elaboration but
not for `rw`, which matches syntactically. -/

lemma channelGuarantees_iff_forall (table : Table F) (data : ProverData F)
    (channel : RawChannel F) :
    table.ChannelGuarantees data channel ↔
    ∀ i ∈ table.interactionsWith data channel, i.Guarantees data :=
  RowEnvs.channelGuarantees_iff_forall table data channel

lemma guarantees_iff_channelGuarantees (table : Table F) (data : ProverData F) :
    table.Guarantees data ↔
    ∀ channel ∈ RowEnvs.channelsWithGuarantees (F:=F) table,
      table.ChannelGuarantees data channel :=
  RowEnvs.guarantees_iff_channelGuarantees table data

lemma channelRequirements_iff_forall (table : Table F) (data : ProverData F)
    (channel : RawChannel F) :
    table.ChannelRequirements data channel ↔
    ∀ i ∈ table.interactionsWith data channel, i.Requirements data :=
  RowEnvs.channelRequirements_iff_forall table data channel

/-- The row-level phrasing of `Constraints`, for flat tables. -/
lemma constraints_iff_forall_row {table : Table F} {data : ProverData F}
    (h : table.component.windowRows = 1) :
    table.Constraints data ↔ ∀ row ∈ table.table,
      table.component.operations.ConstraintsHold (Environment.fromArray row data) :=
  envs_iff table data h

omit [FiniteField F] in
/--
The window's first row is a row of the trace, and it is the row `windowRow` starts from.
-/
private lemma foldl_append_eq_append (init : Array F) (l : List (Array F)) :
    ∃ rest : Array F, l.foldl (· ++ ·) init = init ++ rest := by
  induction l generalizing init with
  | nil => exact ⟨#[], by simp⟩
  | cons a as ih =>
    obtain ⟨rest, hrest⟩ := ih (init ++ a)
    exact ⟨a ++ rest, by simp [hrest]⟩

lemma windowRow_eq_append {t : Table F} {i : ℕ} (h : i ∈ t.windows) :
    ∃ rest : Array F, t.windowRow i = t.table[i]'(t.lt_length_of_mem_windows h) ++ rest := by
  have hpos := t.component.windowRows_pos
  simp only [windowRow]
  cases hw : t.component.windowRows with
  | zero => omega
  | succ n =>
    rw [show List.range (n + 1) = 0 :: (List.range n).map (· + 1) by
      simp [List.range_succ_eq_map]]
    simp only [List.map_cons, List.foldl_cons, Nat.add_zero, List.getElem!_eq_getElem?_getD,
      List.getElem?_eq_getElem (t.lt_length_of_mem_windows h), Option.getD_some, Array.empty_append]
    exact foldl_append_eq_append _ _

/-- Any in-range row of the trace has the component's row width. -/
lemma row_size {t : Table F} {i : ℕ} (hi : i < t.table.length) :
    (t.table[i]!).size = t.component.rowWidth := by
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
  exact t.uniform_width _ (List.getElem_mem hi)

omit [FiniteField F] in
private lemma foldl_append_size (l : List (Array F)) (init : Array F) :
    (l.foldl (· ++ ·) init).size = init.size + (l.map Array.size).sum := by
  induction l generalizing init with
  | nil => simp
  | cons a as ih =>
    simp only [List.foldl_cons, ih, Array.size_append, List.map_cons, List.sum_cons]
    omega

/-- A window spans `windowRows` rows of `rowWidth` cells each. -/
lemma windowRow_size {t : Table F} {i : ℕ} (hi : i ∈ t.windows) :
    (t.windowRow i).size = t.component.windowRows * t.component.rowWidth := by
  rw [mem_windows_iff] at hi
  rw [windowRow, foldl_append_size]
  have hrows : ((List.range t.component.windowRows).map fun k => t.table[i + k]!).map Array.size
      = List.replicate t.component.windowRows t.component.rowWidth := by
    rw [List.map_map, List.eq_replicate_iff]
    refine ⟨by simp, ?_⟩
    intro s hs
    simp only [List.mem_map, List.mem_range, Function.comp_apply] at hs
    obtain ⟨k, hk, rfl⟩ := hs
    exact t.row_size (by omega)
  rw [hrows, List.sum_replicate, smul_eq_mul]
  simp

/--
Reading any type at offset `0` of the window at `i` is reading it at offset `0` of row `i`,
provided the read stays within one row. This generalizes `valueFromOffset_windowEnv` below
beyond the component's own `Input`.
-/
lemma valueFromOffset_windowEnv_curr {t : Table F} {i : ℕ} (hi : i ∈ t.windows)
    (data : ProverData F) (T : TypeMap) [ProvableType T]
    (hT : size T ≤ t.component.rowWidth) :
    valueFromOffset T 0 (t.windowEnv i data) =
      valueFromOffset T 0 (Environment.fromArray t.table[i]! data) := by
  obtain ⟨rest, hrest⟩ := windowRow_eq_append hi
  have hgetElem : t.table[i]'(t.lt_length_of_mem_windows hi) = t.table[i]! := by
    rw [List.getElem!_eq_getElem?_getD,
      List.getElem?_eq_getElem (t.lt_length_of_mem_windows hi)]
    rfl
  rw [hgetElem] at hrest
  simp only [valueFromOffset, windowEnv, Environment.fromArray, hrest]
  congr 1
  apply Vector.ext
  intro j hj
  simp only [Vector.getElem_mapRange, zero_add]
  rw [Array.getElem?_append_left (by
    rw [t.row_size (t.lt_length_of_mem_windows hi)]
    omega)]

/--
The window's input cells are read identically from its first row alone and from the whole window,
because they occupy the low `size Input` indices and `size Input ≤ rowWidth` (the component's
`input_le_rowWidth` law, which confines the input to the window's first row).

This is what lets the fixed-row and derived-data machinery, all of which is stated about a single
row, apply unchanged to a multi-row window.
-/
lemma valueFromOffset_windowEnv {t : Table F} {i : ℕ} (h : i ∈ t.windows)
    (data : ProverData F) :
    valueFromOffset t.component.Input 0 (t.windowEnv i data) =
      valueFromOffset t.component.Input 0
        (Environment.fromArray (t.table[i]'(t.lt_length_of_mem_windows h)) data) := by
  obtain ⟨rest, hrest⟩ := windowRow_eq_append h
  set row := t.table[i]'(t.lt_length_of_mem_windows h) with hrow
  have hsize : row.size = t.component.width :=
    t.uniform_width row (List.getElem_mem _)
  have hinput : size t.component.Input ≤ row.size := by
    rw [hsize]; exact t.component.input_le_rowWidth
  simp only [valueFromOffset, windowEnv, Environment.fromArray, hrest]
  congr 1
  apply Vector.ext
  intro j hj
  simp only [Vector.getElem_mapRange, zero_add]
  have hlt : j < row.size := lt_of_lt_of_le (by simpa using hj) hinput
  rw [Array.getElem?_append_left hlt]

lemma circuitAssumptions (table : Table F) (consistent : table.DataConsistency data)
    (assumptions : table.Assumptions data)
    (i : ℕ) (hi : i ∈ table.windows) :
    table.component.CircuitAssumptions (table.windowEnv i data) := by
  have hlt := table.lt_length_of_mem_windows hi
  show table.component.circuit.Assumptions
    (valueFromOffset table.component.Input 0 (table.windowEnv i data)) data
  rw [valueFromOffset_windowEnv hi]
  apply table.component.assumptions_imply_circuit i (table.table[i]'hlt) data
  · cases hcolumns : table.component.fixedColumns with
    | none => simp [FixedRowAt]
    | some fixed =>
      have hmatch := table.fixed_rows_match
      simp only [Component.fixedRowsMatch, hcolumns] at hmatch
      have hlength : table.table.length = fixed.height := by
        simpa using congrArg List.length hmatch
      refine ⟨by omega, ?_⟩
      have hprefix := congrArg (fun rows => rows[i]?) hmatch
      have hleft : i < (table.table.map
          (fun candidate => candidate.extract 0 fixed.width)).length := by
        simp only [List.length_map]; exact hlt
      have hright : i < ((List.range fixed.height).map fixed.row).length := by
        simp only [List.length_map, List.length_range]; omega
      rw [List.getElem?_eq_getElem hleft, List.getElem?_eq_getElem hright] at hprefix
      simp only [List.getElem_map, List.getElem_range, Option.some.injEq] at hprefix
      exact hprefix
  · simp only [DataRowAt]
    rw [consistent]
    simp [Component.proverRows, hlt]
  · have h := assumptions _ (mem_envs_of_mem_windows hi (data:=data))
    show table.component.Assumptions
      (valueFromOffset table.component.Input 0
        (Environment.fromArray (table.table[i]'hlt) data)) data
    rw [← valueFromOffset_windowEnv hi]
    exact h

/-- Every environment of a table satisfies the circuit's assumptions. -/
lemma circuitAssumptions_envs (table : Table F) (consistent : table.DataConsistency data)
    (assumptions : table.Assumptions data) :
    RowEnvs.CircuitAssumptions (F:=F) table data := by
  intro e he
  simp only [envs_eq, List.mem_map] at he
  obtain ⟨i, hi, rfl⟩ := he
  exact table.circuitAssumptions consistent assumptions i hi

/-- Circuit soundness, lifted to full table level. -/
theorem weakSoundness {table : Table F} (consistent : table.DataConsistency data) :
    table.Assumptions data → table.Constraints data → table.Guarantees data →
    table.Spec data ∧ table.Requirements data := by
  intro assumptions constraints guarantees
  exact RowEnvs.weakSoundness (table.circuitAssumptions_envs consistent assumptions)
    constraints guarantees

/-- A row of a *flat* trace is one of the environments the table is checked at. -/
lemma mem_envs_of_mem_table {table : Table F} {data : ProverData F}
    (h : table.component.windowRows = 1) {row : Array F} (hrow : row ∈ table.table) :
    Environment.fromArray row data ∈ RowEnvs.envs (F:=F) table data := by
  rw [envs_eq_of_flat table data h]
  simp only [List.mem_map]
  exact ⟨row, hrow, rfl⟩

/--
If we know constraints and _some_ of the guarantees unconditionally, we can remove them from the
per-window assumptions.

This lemma is tailored to VM-like channels where there remains a single channel that we need to
prove guarantees for.
-/
lemma requirements_of_partial_guarantees_of_constraints {table : Table F}
  {finished : List (RawChannel F)} {unfinished : RawChannel F} :
  table.DataConsistency data →
  table.Assumptions data →
  table.Constraints data →
  table.channelsWithGuarantees ⊆ unfinished :: finished →
  (∀ channel ∈ finished, table.ChannelGuarantees data channel) →
    ∀ env ∈ RowEnvs.envs (F:=F) table data,
      table.component.operations.ChannelGuarantees unfinished env →
      table.component.operations.ChannelRequirements unfinished env := by
  intro consistent assumptions constraints subset finished_grts env h_env
  exact RowEnvs.requirements_of_partial_guarantees_of_constraints
    (table.circuitAssumptions_envs consistent assumptions) constraints subset finished_grts
    _ h_env

end Table

end Air.Flat
