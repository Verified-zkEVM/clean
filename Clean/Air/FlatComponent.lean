/-
AIR tables: a concrete trace for one component, checked on each window of its rows.

The `Component` structure itself and its `instantiate` transport lemmas live in
`Clean/Air/Component.lean`. What lives here is the trace: the `Table`, whose environments are the
component's row *windows*; every trace-level predicate and interaction collection, stated once
over those environments; and `circuitAssumptions`, which supplies the fixed-row and derived-data
facts at each row index.

There is a single `Table` type for both AIR styles. How many rows an environment spans is read
off `component.windowRows`, so a flat table (`windowRows = 1`) and a transition table
(`windowRows = 2`) differ only in that field -- not in their type, and not in a separate tag the
prover could reinterpret. Consequently nothing below inspects an individual environment: the
predicates quantify over `envs`, and a wider window changes only how that list is produced.
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
variable {table : Table F} {data : ProverData F} {channel : RawChannel F}

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

/--
The environments at which the component's constraints are checked: one per window of the trace.

Indices are deliberately dropped here: only `circuitAssumptions` below needs them, and threading
them through this list would force an extra binder through every predicate stated over `envs`.
-/
def envs (t : Table F) (data : ProverData F) : List (Environment F) :=
  t.windows.map (t.windowEnv · data)

@[circuit_norm] lemma envs_eq (t : Table F) (data : ProverData F) :
    t.envs data = t.windows.map (t.windowEnv · data) := rfl

/-- Every environment carries the prover data it was built from. This is what lets the
interaction lemmas below bridge `AbstractInteraction.Guarantees _ env`, which reads `env.data`,
with `Interaction.Guarantees _ data`. -/
lemma data_eq_of_mem {e : Environment F} (h : e ∈ table.envs data) : e.data = data := by
  simp only [envs_eq, List.mem_map] at h
  obtain ⟨i, -, rfl⟩ := h
  rfl

/-- A window of the trace is one of the environments the table is checked at. -/
lemma mem_envs_of_mem_windows {table : Table F} {i : ℕ} (hi : i ∈ table.windows)
    {data : ProverData F} :
    table.windowEnv i data ∈ table.envs data := by
  simp only [envs_eq, List.mem_map]
  exact ⟨i, hi, rfl⟩

/-- For a flat component the window at `i` is just row `i`. -/
lemma windowRow_of_flat {table : Table F}
    (h : table.component.windowRows = 1) (i : ℕ) :
    table.windowRow i = table.table[i]! := by
  simp [Table.windowRow, h]

/-- A flat table is checked once per row, against that row alone. -/
lemma envs_eq_of_flat (table : Table F) (data : ProverData F)
    (h : table.component.windowRows = 1) :
    table.envs data = table.table.map (Environment.fromArray · data) := by
  simp only [envs_eq, Table.windowEnv, windowRow_of_flat h]
  rw [show table.windows = List.range table.table.length by simp [Table.windows, h]]
  apply List.ext_getElem
  · simp
  intro i h₁ h₂
  simp only [List.getElem_map, List.getElem_range] at *
  congr 1
  rw [getElem!_pos _ _ (by simpa using h₂)]

/-- A row of a *flat* trace is one of the environments the table is checked at. -/
lemma mem_envs_of_mem_table {table : Table F} {data : ProverData F}
    (h : table.component.windowRows = 1) {row : Array F} (hrow : row ∈ table.table) :
    Environment.fromArray row data ∈ table.envs data := by
  rw [envs_eq_of_flat table data h]
  simp only [List.mem_map]
  exact ⟨row, hrow, rfl⟩

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
Trace-level predicates. Each quantifies over `envs`; none inspects an individual environment,
which is exactly why they apply to any window size.
-/

def Constraints (table : Table F) (data : ProverData F) : Prop :=
  ∀ env ∈ table.envs data, table.component.operations.ConstraintsHold env

def Assumptions (table : Table F) (data : ProverData F) : Prop :=
  ∀ env ∈ table.envs data, table.component.RowAssumptions env

def CircuitAssumptions (table : Table F) (data : ProverData F) : Prop :=
  ∀ env ∈ table.envs data, table.component.CircuitAssumptions env

def Guarantees (table : Table F) (data : ProverData F) : Prop :=
  ∀ env ∈ table.envs data, table.component.operations.FullGuarantees env

def ChannelGuarantees (table : Table F) (data : ProverData F) (channel : RawChannel F) : Prop :=
  ∀ env ∈ table.envs data,
    table.component.operations.ChannelGuarantees channel env

def InChannelsOrGuarantees (table : Table F) (data : ProverData F)
    (channels : List (RawChannel F)) : Prop :=
  ∀ env ∈ table.envs data,
    table.component.operations.InChannelsOrGuaranteesFull channels env

def Requirements (table : Table F) (data : ProverData F) : Prop :=
  ∀ env ∈ table.envs data, table.component.operations.FullRequirements env

def ChannelRequirements (table : Table F) (data : ProverData F) (channel : RawChannel F) : Prop :=
  ∀ env ∈ table.envs data,
    table.component.operations.ChannelRequirements channel env

def InChannelsOrRequirements (table : Table F) (data : ProverData F)
    (channels : List (RawChannel F)) : Prop :=
  ∀ env ∈ table.envs data,
    table.component.operations.InChannelsOrRequirementsFull channels env

def Spec (table : Table F) (data : ProverData F) : Prop :=
  ∀ env ∈ table.envs data, table.component.Spec env

@[circuit_norm]
def channelsWithGuarantees (table : Table F) : List (RawChannel F) :=
  table.component.circuit.channelsWithGuarantees

@[circuit_norm]
def channelsWithRequirements (table : Table F) : List (RawChannel F) :=
  table.component.circuit.channelsWithRequirements

/-
Interaction collection. A component emits its interactions once per environment, so a transition
table of `n` rows contributes `n - 1` copies rather than `n`.

This matters for `BalancedInteractions`, which carries a side condition that the total interaction
count is below `ringChar F` -- without it, `p` copies of a push would sum to zero and forge
balance. Any bound on the total interaction count derived from table heights must therefore use
`n - 1` for transition entries, and note that a 0- or 1-row transition table emits nothing at all.
-/

def interactions (table : Table F) (data : ProverData F) : List (Interaction F) :=
  (table.envs data).flatMap fun env =>
    table.component.operations.interactionValues env

noncomputable def interactionsWith (table : Table F) (data : ProverData F)
    (channel : RawChannel F) : List (Interaction F) :=
  (table.envs data).flatMap fun env =>
    table.component.operations.interactionValuesWith channel env

noncomputable def interactionssWith (table : Table F) (data : ProverData F)
    (channel : RawChannel F) : List (List (Interaction F)) :=
  (table.envs data).map fun env =>
    table.component.operations.interactionValuesWith channel env

open Classical in lemma interactionsWith_eq_filter :
    table.interactionsWith data channel =
      (table.interactions data).filter (·.channel = channel) := by
  simp only [interactionsWith, interactions, List.filter_flatMap]
  congr
  funext env
  rw [Operations.interactionValuesWith_eq_filter]

lemma channel_eq_of_mem_interactionsWith {i : Interaction F} :
    i ∈ table.interactionsWith data channel → i.channel = channel := by
  intro h_mem
  simp only [interactionsWith, List.mem_flatMap] at h_mem
  rcases h_mem with ⟨env, h_env, hi⟩
  simp only [Operations.interactionValuesWith, List.mem_map] at hi
  rcases hi with ⟨i_abs, hi_abs, heq⟩
  rw [←heq]
  apply Operations.channel_eq_of_mem_interactionsWith hi_abs

lemma forall_interactions_iff (table : Table F) (data : ProverData F)
    (motive : Interaction F → Prop) :
    (∀ i ∈ table.interactions data, motive i) ↔
    ∀ env ∈ table.envs data, ∀ i ∈ table.component.operations.interactions,
      motive (i.eval env) := by
  simp only [interactions, Operations.interactionValues, List.mem_flatMap, List.mem_map,
    forall_exists_index, and_imp]
  constructor
  · intro h e h_e i hi
    exact h (i.eval e) e h_e i hi rfl
  · intro h i e h_e i' hi' h_eq
    rw [← h_eq]
    exact h e h_e i' hi'

lemma forall_interactionsWith_iff (table : Table F) (data : ProverData F) (channel : RawChannel F)
  (motive : Interaction F → Prop) :
    (∀ i ∈ table.interactionsWith data channel, motive i) ↔
    ∀ env ∈ table.envs data, ∀ i ∈ table.component.operations.interactions,
      (i.channel = channel → motive (i.eval env)) := by
  simp only [interactionsWith, Operations.interactionValuesWith_eq_map,
    Operations.interactionsWith, List.mem_flatMap, List.mem_map, List.mem_filter,
    decide_eq_true_eq, forall_exists_index, and_imp]
  constructor
  · intro h e h_e i hi h_channel
    exact h (i.eval e) e h_e i hi h_channel rfl
  · intro h i e h_e i' hi' h_channel h_eq
    rw [← h_eq]
    exact h e h_e i' hi' h_channel

lemma interactionsWith_nil_of_channel_not_mem :
    channel ∉ table.component.circuit.channels →
      table.interactionsWith data channel = [] := by
  contrapose!
  simp only [AbstractInteraction.eval_channel, interactionsWith_eq_filter, ne_eq, List.filter_eq_nil_iff,
    decide_eq_true_eq, forall_interactions_iff, not_forall, not_not, forall_exists_index]
  intro env env_mem i i_mem channel_eq
  symm at channel_eq; subst channel_eq
  simp only [Component.interactions_eq] at i_mem
  have h_subset := table.component.circuit.channels_subset
    table.component.rowInputVar table.component.rowOffset
  apply h_subset
  simp only [Operations.channels, List.mem_map]
  exists i

lemma guarantees_iff_forall (table : Table F) (data : ProverData F) :
    table.Guarantees data ↔
    ∀ i ∈ table.interactions data, i.Guarantees data := by
  simp only [Guarantees, circuit_norm, forall_interactions_iff]
  refine forall_congr' fun e => imp_congr_right fun h_e => ?_
  simp only [AbstractInteraction.Guarantees, Interaction.Guarantees, AbstractInteraction.eval,
    Interaction.msgVector, data_eq_of_mem (table:=table) h_e]

lemma channelGuarantees_iff_forall (table : Table F) (data : ProverData F)
    (channel : RawChannel F) :
    table.ChannelGuarantees data channel ↔
    ∀ i ∈ table.interactionsWith data channel, i.Guarantees data := by
  simp only [ChannelGuarantees, circuit_norm, forall_interactionsWith_iff]
  refine forall_congr' fun e => imp_congr_right fun h_e => ?_
  simp only [AbstractInteraction.Guarantees, Interaction.Guarantees, AbstractInteraction.eval,
    Interaction.msgVector, data_eq_of_mem (table:=table) h_e]

lemma guarantees_iff_channelGuarantees (table : Table F) (data : ProverData F) :
    table.Guarantees data ↔
    ∀ channel ∈ table.channelsWithGuarantees,
      table.ChannelGuarantees data channel := by
  simp only [Guarantees, ChannelGuarantees, channelsWithGuarantees]
  simp only [Component.guarantees_iff, Component.channelGuarantees_iff, Component.rowOperations]
  simp only [GeneralFormalCircuit.guarantees_iff]
  constructor <;> simp_all

lemma channelGuarantees_of_requirements (table : Table F) (data : ProverData F)
    {channel : RawChannel F} :
    table.Guarantees data → table.ChannelGuarantees data channel := by
  simp_all [Guarantees, ChannelGuarantees, circuit_norm]

lemma requirements_iff_forall (table : Table F) (data : ProverData F) :
    table.Requirements data ↔
    ∀ i ∈ table.interactions data, i.Requirements data := by
  simp only [Requirements, circuit_norm, forall_interactions_iff]
  refine forall_congr' fun e => imp_congr_right fun h_e => ?_
  simp only [AbstractInteraction.Requirements, Interaction.Requirements, AbstractInteraction.eval,
    Interaction.msgVector, data_eq_of_mem (table:=table) h_e]

lemma channelRequirements_iff_forall (table : Table F) (data : ProverData F)
    (channel : RawChannel F) :
    table.ChannelRequirements data channel ↔
    ∀ i ∈ table.interactionsWith data channel, i.Requirements data := by
  simp only [ChannelRequirements, circuit_norm, forall_interactionsWith_iff]
  refine forall_congr' fun e => imp_congr_right fun h_e => ?_
  simp only [AbstractInteraction.Requirements, Interaction.Requirements, AbstractInteraction.eval,
    Interaction.msgVector, data_eq_of_mem (table:=table) h_e]

lemma requirements_iff_channelRequirements_of_constraints (table : Table F)
    (data : ProverData F) :
    table.Constraints data →
    (table.Requirements data ↔
    ∀ channel ∈ table.channelsWithRequirements,
      table.ChannelRequirements data channel) := by
  intro h_constraints
  simp only [Requirements, ChannelRequirements, channelsWithRequirements]
  simp only [Component.requirements_iff, Component.channelRequirements_iff, Component.rowOperations]
  simp_rw [Constraints, table.component.constraintsHold_iff] at h_constraints
  constructor
  · intro h_reqs channel h_channel env h_env
    specialize h_reqs env h_env
    rw [table.component.circuit.requirements_iff_of_constraints
      (h_constraints env h_env)] at h_reqs
    exact h_reqs channel h_channel
  · intro h_reqs env h_env
    rw [table.component.circuit.requirements_iff_of_constraints (h_constraints env h_env)]
    intro channel h_channel
    exact h_reqs channel h_channel env h_env

lemma channelRequirements_of_requirements (table : Table F) (data : ProverData F)
    {channel : RawChannel F} :
    table.Requirements data → table.ChannelRequirements data channel := by
  simp_all [Requirements, ChannelRequirements, circuit_norm]

lemma inChannelsOrRequirements_of_constraints (table : Table F) (data : ProverData F) :
    table.Constraints data →
    table.InChannelsOrRequirements data (table.channelsWithRequirements) := by
  intro h_constraints
  simp only [InChannelsOrRequirements, channelsWithRequirements]
  intro env h_env
  exact table.component.inChannelsOrRequirements_of_constraints env
    (h_constraints env h_env)

lemma requirements_of_not_mem_of_constraints (table : Table F) (data : ProverData F)
    {channel : RawChannel F} :
    table.Constraints data →
    channel ∉ table.channelsWithRequirements →
      table.ChannelRequirements data channel := by
  intro h_constraints h_not_mem
  have h_in_or_req := table.inChannelsOrRequirements_of_constraints data h_constraints
  simp only [ChannelRequirements, InChannelsOrRequirements] at *
  intro env h_env
  specialize h_in_or_req env h_env
  apply Operations.requirements_of_not_mem _ (table.channelsWithRequirements)
  assumption
  assumption

lemma inChannelsOrGuarantees (table : Table F) (data : ProverData F) :
    table.InChannelsOrGuarantees data (table.channelsWithGuarantees) := by
  simp [InChannelsOrGuarantees, channelsWithGuarantees, Component.inChannelsOrGuarantees]

lemma guarantees_of_not_mem (table : Table F) (data : ProverData F) {channel : RawChannel F} :
    channel ∉ table.channelsWithGuarantees →
      table.ChannelGuarantees data channel := by
  intro h_not_mem
  have h_in_or_guar := table.inChannelsOrGuarantees data
  simp only [ChannelGuarantees, InChannelsOrGuarantees] at *
  intro env h_env
  specialize h_in_or_guar env h_env
  apply Operations.guarantees_of_not_mem _ (table.channelsWithGuarantees)
  assumption
  assumption

/--
Circuit soundness, lifted to full table level.

The hypothesis is `CircuitAssumptions`, the *circuit's* assumptions at every environment;
`circuitAssumptions_envs` below derives it from the ensemble-level `Assumptions` and
`DataConsistency`, and is the one place the window's row indices are needed. `weakSoundness`
packages the two together.
-/
theorem weakSoundness_of_circuitAssumptions {table : Table F} {data : ProverData F}
    (assumptions : table.CircuitAssumptions data) :
    table.Constraints data → table.Guarantees data →
    table.Spec data ∧ table.Requirements data := by
  intro constraints guarantees
  constructor
  · intro env h_env
    exact (Component.weakSoundness (assumptions env h_env)
      (constraints env h_env) (guarantees env h_env)).left
  · intro env h_env
    exact (Component.weakSoundness (assumptions env h_env)
      (constraints env h_env) (guarantees env h_env)).right

/--
If we know constraints and _some_ of the guarantees unconditionally, we can remove them from the
per-environment assumptions.

This lemma is tailored to VM-like channels where there remains a single channel that we need to
prove guarantees for. Like everything else here it never mentions how many rows an environment
spans.
-/
lemma requirements_of_partial_guarantees_of_constraints {table : Table F} {data : ProverData F}
  {finished : List (RawChannel F)} {unfinished : RawChannel F} :
  table.CircuitAssumptions data →
  table.Constraints data →
  table.channelsWithGuarantees ⊆ unfinished :: finished →
  (∀ channel ∈ finished, table.ChannelGuarantees data channel) →
    ∀ env ∈ table.envs data,
      table.component.operations.ChannelGuarantees unfinished env →
      table.component.operations.ChannelRequirements unfinished env := by
  intro assumptions constraints subset finished_grts env h_env channel_grts
  replace finished_grts channel hc := finished_grts channel hc env h_env
  suffices table.component.operations.FullRequirements env by
    simp only [circuit_norm] at this ⊢
    intro i hi _
    exact this i hi
  suffices table.component.operations.FullGuarantees env from
    Component.weakSoundness (assumptions env h_env) (constraints env h_env) this |>.right
  simp only [Component.guarantees_iff, Component.rowOperations]
  rw [GeneralFormalCircuit.guarantees_iff]
  intro channel channel_mem
  show table.component.rowOperations.ChannelGuarantees channel env
  rw [← Component.channelGuarantees_iff]
  replace channel_mem := subset channel_mem
  simp at channel_mem
  rcases channel_mem with rfl | channel_mem
  · exact channel_grts
  · exact finished_grts _ channel_mem

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
  rw [getElem!_pos t.table i hi]
  exact t.uniform_width _ (List.getElem_mem hi)

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
  have hgetElem : t.table[i]'(t.lt_length_of_mem_windows hi) = t.table[i]! :=
    (getElem!_pos t.table i (t.lt_length_of_mem_windows hi)).symm
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
    table.CircuitAssumptions data := by
  intro e he
  simp only [envs_eq, List.mem_map] at he
  obtain ⟨i, hi, rfl⟩ := he
  exact table.circuitAssumptions consistent assumptions i hi

/-- Circuit soundness, lifted to full table level. -/
theorem weakSoundness {table : Table F} (consistent : table.DataConsistency data) :
    table.Assumptions data → table.Constraints data → table.Guarantees data →
    table.Spec data ∧ table.Requirements data := by
  intro assumptions constraints guarantees
  exact weakSoundness_of_circuitAssumptions (table.circuitAssumptions_envs consistent assumptions)
    constraints guarantees

end Table

end Air.Flat
