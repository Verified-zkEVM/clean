import Clean.Air.Circuit

namespace Air.Flat
variable {F : Type} [FiniteField F]
variable {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]

/-- Public, index-addressed columns supplied by the verifier rather than committed by the prover.
The structured row program is evaluated identically in Lean and extracted backends; fixed-column
values are no longer stored or exported as a fully materialized trace. -/
structure FixedColumns (F : Type) where
  height : ℕ
  program : Witgen.RowProgram F
  valid : program.Valid .fixed

namespace FixedColumns

abbrev width (fixed : FixedColumns F) : ℕ := fixed.program.width

def row (fixed : FixedColumns F) (i : ℕ) : Array F :=
  (fixed.program.eval i).toArray

/-- The full semantic rows have exactly the declared fixed prefix at every row index. -/
abbrev RowsMatch (fixed : FixedColumns F) (rows : List (Array F)) : Prop :=
  rows.map (fun row => row.extract 0 fixed.width) =
    (List.range fixed.height).map fixed.row

end FixedColumns

/-- The fixed-column fact available while proving the circuit assumptions for row `i`. -/
def FixedRowAt (fixedColumns : Option (FixedColumns F)) (i : ℕ) (row : Array F) : Prop :=
  match fixedColumns with
  | none => True
  | some fixed => i < fixed.height ∧ row.extract 0 fixed.width = fixed.row i

def inputRow (Input : TypeMap) [ProvableType Input] (row : Array F) : Vector F (size Input) :=
  ⟨(List.ofFn (fun i : Fin (size Input) => row[i.val]?.getD 0)).toArray, by simp⟩

/-- The derived-data fact available while proving the circuit assumptions for row `i`. -/
def DataRowAt (name : String) (Input : TypeMap) [ProvableType Input]
    (i : ℕ) (row : Array F) (data : ProverData F) : Prop :=
  (data name (size Input))[i]? = some (inputRow Input row)

/--
A flat AIR component: one circuit whose constraints are checked independently on each row.
There are no direct adjacent-row constraints; communication with other rows/components is
expressed by channel interactions.
-/
structure Component (F : Type) [FiniteField F] where
  {Input : TypeMap} {Output : TypeMap}
  [provableInput : ProvableType Input] [provableOutput : ProvableType Output]
  circuit : GeneralFormalCircuit F Input Output
  /-- When present, identifies the fixed prefix available to the circuit on row `i`. -/
  fixedColumns : Option (FixedColumns F) := none
  /-- Assumptions still required from the enclosing ensemble after fixed-row and data facts. -/
  Assumptions : Input F → ProverData F → Prop := circuit.Assumptions
  /-- Fixed-row and derived-data facts, together with the residual assumptions, imply the
  assumptions of the underlying row circuit. -/
  assumptions_imply_circuit : ∀ i row data,
      FixedRowAt fixedColumns i row →
        DataRowAt circuit.name Input i row data →
        Assumptions (valueFromOffset Input 0 (Environment.fromArray row data)) data →
        circuit.Assumptions
          (valueFromOffset Input 0 (Environment.fromArray row data)) data := by simp
  fixed_width_le_input : (fixedColumns.map FixedColumns.width).getD 0 ≤ size Input := by simp

instance (t: Component F) : ProvableType t.Input := t.provableInput
instance (t: Component F) : ProvableType t.Output := t.provableOutput

namespace Component
def fixedWidth (component : Component F) : ℕ :=
  component.fixedColumns.map FixedColumns.width |>.getD 0

def fixedRowsMatch (component : Component F) (rows : List (Array F)) : Prop :=
  match component.fixedColumns with
  | none => True
  | some fixed => FixedColumns.RowsMatch fixed rows

def proverRows (component : Component F) (rows : List (Array F)) (n : ℕ) :
    Array (Vector F n) :=
  if h : size component.Input = n then
    h ▸ (rows.map (inputRow component.Input) |>.toArray)
  else
    #[]

def DataConsistency (component : Component F) (rows : List (Array F))
    (data : ProverData F) : Prop :=
  data component.circuit.name (size component.Input) =
    component.proverRows rows (size component.Input)

def operations (component : Component F) : Operations F :=
  component.circuit.instantiate.operations 0

def width (component : Component F) : ℕ := component.circuit.size

def committedWidth (component : Component F) : ℕ :=
  component.width - component.fixedWidth

def rowOffset (component : Component F) : ℕ := size component.Input

def rowInputVar (component : Component F): Var component.Input F :=
  varFromOffset component.Input 0

@[circuit_norm]
lemma rowOffset_mk (circuit : GeneralFormalCircuit F Input Output) :
  ({ circuit } : Component F).rowOffset = size Input := rfl

@[circuit_norm]
lemma rowInputVar_mk (circuit : GeneralFormalCircuit F Input Output) :
  ({ circuit } : Component F).rowInputVar = varFromOffset Input 0 := rfl

/-- first `size Input` elements of the environment are the input -/
@[circuit_norm]
def rowInput (component : Component F) (row : Environment F) : component.Input F :=
  valueFromOffset component.Input 0 row

/-- output is whatever the circuit computes on the row input -/
@[circuit_norm]
def rowOutput (component : Component F) (row : Environment F) : component.Output F :=
  let outputVar := (component.circuit component.rowInputVar).output component.rowOffset
  eval row outputVar

def rowOperations (component : Component F) : Operations F :=
  component.circuit.main (varFromOffset component.Input 0) |>.operations (size component.Input)

@[circuit_norm]
lemma rowOperations_mk (circuit : GeneralFormalCircuit F Input Output) :
  ({ circuit } : Component F).rowOperations =
    (circuit.main (varFromOffset Input 0)).operations (size Input) := rfl

def Spec (component : Component F) (row : Environment F) : Prop :=
  component.circuit.Spec (component.rowInput row) (component.rowOutput row) row.data

def CircuitAssumptions (component : Component F) (row : Environment F) : Prop :=
  component.circuit.Assumptions (component.rowInput row) row.data

/-- Residual assumptions not supplied by fixed-row or derived-data invariants. -/
def RowAssumptions (component : Component F) (row : Environment F) : Prop :=
  component.Assumptions (component.rowInput row) row.data

def exposedChannels (component : Component F) : List (ExposedChannel F) :=
  component.circuit.exposedChannels component.rowInputVar component.rowOffset

variable {component : Component F} {env : Environment F}

lemma constraints_eq : component.operations.constraints = component.rowOperations.constraints := by
  simp only [circuit_norm, rowOperations, witnessAny, GeneralFormalCircuit.instantiate, Component.operations,
    GeneralFormalCircuit.toSubcircuit, GeneralFormalCircuit.toWithHint,
    GeneralFormalCircuit.WithHint.toSubcircuit, Operations.toNested_toFlat]

lemma lookups_eq : component.operations.lookups = component.rowOperations.lookups := by
  simp only [circuit_norm, rowOperations, witnessAny, GeneralFormalCircuit.instantiate, Component.operations,
    GeneralFormalCircuit.toSubcircuit, GeneralFormalCircuit.toWithHint,
    GeneralFormalCircuit.WithHint.toSubcircuit, Operations.toNested_toFlat]

lemma interactions_eq : component.operations.interactions = component.rowOperations.interactions := by
  simp only [circuit_norm, rowOperations, witnessAny, GeneralFormalCircuit.instantiate, Component.operations,
    GeneralFormalCircuit.toSubcircuit, GeneralFormalCircuit.toWithHint,
    GeneralFormalCircuit.WithHint.toSubcircuit, Operations.toNested_toFlat]

lemma interactionsWith_eq {channel : RawChannel F} :
    component.operations.interactionsWith channel = component.rowOperations.interactionsWith channel := by
  simp only [Operations.interactionsWith, interactions_eq]

lemma interactionsValues_eq : component.operations.interactionValues env = component.rowOperations.interactionValues env := by
  simp only [Operations.interactionValues, interactions_eq]

lemma interactionsWith_of_exposedChannels {table : Component F} {channel : RawChannel F}
  {interactions : List (AbstractInteraction F)}
  (h_exposed : ⟨ channel, interactions ⟩ ∈ table.exposedChannels) :
    table.operations.interactionsWith channel = interactions := by
  rw [Component.interactionsWith_eq]
  simp only [circuit_norm, Component.exposedChannels] at *
  exact table.circuit.interactionsWith_eq_of_mem_exposedChannels _ _ _ h_exposed

lemma constraintsHold_iff (env : Environment F) :
    component.operations.ConstraintsHold env ↔ component.rowOperations.ConstraintsHold env := by
  simp only [circuit_norm, lookups_eq, constraints_eq]

lemma guarantees_iff (env : Environment F) :
    component.operations.FullGuarantees env ↔ component.rowOperations.FullGuarantees env := by
  simp only [circuit_norm, interactions_eq]

lemma requirements_iff (env : Environment F) :
    component.operations.FullRequirements env ↔ component.rowOperations.FullRequirements env := by
  simp only [circuit_norm, interactions_eq]

lemma channelGuarantees_iff (env : Environment F) (channel : RawChannel F) :
    component.operations.ChannelGuarantees channel env ↔ component.rowOperations.ChannelGuarantees channel env := by
  simp only [circuit_norm, interactions_eq]

lemma channelRequirements_iff (env : Environment F) (channel : RawChannel F) :
    component.operations.ChannelRequirements channel env ↔ component.rowOperations.ChannelRequirements channel env := by
  simp only [circuit_norm, interactions_eq]

lemma inChannelsOrRequirements_of_constraints (env : Environment F) :
    component.operations.ConstraintsHold env →
    component.operations.InChannelsOrRequirementsFull component.circuit.channelsWithRequirements env := by
  rw [constraintsHold_iff]
  intro h_constraints
  simp only [circuit_norm, interactions_eq]
  exact component.circuit.in_channels_or_requirements_full_of_constraints h_constraints

lemma inChannelsOrGuarantees (env : Environment F) :
    component.operations.InChannelsOrGuaranteesFull component.circuit.channelsWithGuarantees env := by
  have h := component.circuit.in_channels_or_guarantees_full
  simp only [circuit_norm, interactions_eq] at *
  exact h _ _ env

-- this is the circuit's soundness theorem, stated in "instantiated" form
theorem weakSoundness {component : Component F} {env : Environment F} :
    component.CircuitAssumptions env →
    component.operations.ConstraintsHold env →
    component.operations.FullGuarantees env →
      component.Spec env ∧ component.operations.FullRequirements env := by
  simp only [constraintsHold_iff, guarantees_iff, requirements_iff, rowOperations, Spec]
  intro h_assumptions h_constraints h_guarantees
  set inputVar := varFromOffset component.Input 0
  set ops := (component.circuit.main inputVar).operations (size component.Input)
  have h_assumptions' : component.circuit.Assumptions (eval env inputVar) env.data := by
    simpa only [CircuitAssumptions, rowInput, inputVar, eval_varFromOffset_valueFromOffset]
      using h_assumptions
  convert component.circuit.original_full_soundness _ _ _ h_assumptions' h_constraints h_guarantees
  simp only [rowInput, inputVar, eval_varFromOffset_valueFromOffset]
  rfl
end Component

/-- A concrete trace for one flat AIR component. Its data environment belongs to the ensemble. -/
structure Table (F : Type) [FiniteField F] where
  component : Component F
  table : List (Array F)
  uniform_width : ∀ row ∈ table, row.size = component.width
  /-- Connects the row-indexed fixed-column declaration to the concrete semantic rows. -/
  fixed_rows_match : component.fixedRowsMatch table := by
    simp [Component.fixedRowsMatch]

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

@[circuit_norm]
def channelsWithGuarantees (table : Table F) : List (RawChannel F) :=
  table.component.circuit.channelsWithGuarantees

@[circuit_norm]
def channelsWithRequirements (table : Table F) : List (RawChannel F) :=
  table.component.circuit.channelsWithRequirements

def Constraints (table : Table F) (data : ProverData F) : Prop :=
  ∀ row ∈ table.table,
    table.component.operations.ConstraintsHold (Environment.fromArray row data)

def Assumptions (table : Table F) (data : ProverData F) : Prop :=
  ∀ row ∈ table.table,
    table.component.RowAssumptions (Environment.fromArray row data)

lemma circuitAssumptions (table : Table F) (consistent : table.DataConsistency data)
    (assumptions : table.Assumptions data)
    (row : Array F) (hrow : row ∈ table.table) :
    table.component.CircuitAssumptions (Environment.fromArray row data) := by
  obtain ⟨i, hi⟩ := List.get_of_mem hrow
  apply table.component.assumptions_imply_circuit i.val row data
  · cases hcolumns : table.component.fixedColumns with
    | none => simp [FixedRowAt]
    | some fixed =>
      have hmatch := table.fixed_rows_match
      simp only [Component.fixedRowsMatch, hcolumns] at hmatch
      have hlength : table.table.length = fixed.height := by
        simpa using congrArg List.length hmatch
      refine ⟨by omega, ?_⟩
      have hprefix := congrArg (fun rows => rows[i.val]?) hmatch
      have hleft : i.val < (table.table.map
          (fun candidate => candidate.extract 0 fixed.width)).length := by
        simp only [List.length_map]
        exact i.isLt
      have hright : i.val < ((List.range fixed.height).map fixed.row).length := by
        simp only [List.length_map, List.length_range]
        omega
      rw [List.getElem?_eq_getElem hleft, List.getElem?_eq_getElem hright] at hprefix
      simp only [List.getElem_map, List.getElem_range, Option.some.injEq] at hprefix
      have hi' : table.table[i.val] = row := hi
      rw [hi'] at hprefix
      exact hprefix
  · simp only [DataRowAt]
    rw [consistent]
    have hi' : table.table[i.val] = row := hi
    simp [Component.proverRows, i.isLt, hi']
  · exact assumptions row hrow

def Guarantees (table : Table F) (data : ProverData F) : Prop :=
  ∀ row ∈ table.table,
    table.component.operations.FullGuarantees (Environment.fromArray row data)

def ChannelGuarantees (table : Table F) (data : ProverData F) (channel : RawChannel F) : Prop :=
  ∀ row ∈ table.table,
    table.component.operations.ChannelGuarantees channel (Environment.fromArray row data)

def InChannelsOrGuarantees (table : Table F) (data : ProverData F)
    (channels : List (RawChannel F)) : Prop :=
  ∀ row ∈ table.table,
    table.component.operations.InChannelsOrGuaranteesFull channels (Environment.fromArray row data)

def Requirements (table : Table F) (data : ProverData F) : Prop :=
  ∀ row ∈ table.table,
    table.component.operations.FullRequirements (Environment.fromArray row data)

def ChannelRequirements (table : Table F) (data : ProverData F) (channel : RawChannel F) : Prop :=
  ∀ row ∈ table.table,
    table.component.operations.ChannelRequirements channel (Environment.fromArray row data)

def InChannelsOrRequirements (table : Table F) (data : ProverData F)
    (channels : List (RawChannel F)) : Prop :=
  ∀ row ∈ table.table,
    table.component.operations.InChannelsOrRequirementsFull channels (Environment.fromArray row data)

def Spec (table : Table F) (data : ProverData F) : Prop :=
  ∀ row ∈ table.table,
    table.component.Spec (Environment.fromArray row data)

def interactions (table : Table F) (data : ProverData F) : List (Interaction F) :=
  table.table.flatMap fun row =>
    table.component.operations.interactionValues (Environment.fromArray row data)

noncomputable def interactionsWith (table : Table F) (data : ProverData F)
    (channel : RawChannel F) : List (Interaction F) :=
  table.table.flatMap fun row =>
    table.component.operations.interactionValuesWith channel (Environment.fromArray row data)

open Classical in lemma interactionsWith_eq_filter :
    table.interactionsWith data channel = (table.interactions data).filter (·.channel = channel) := by
  simp only [interactionsWith, interactions, List.filter_flatMap]
  congr
  funext row
  rw [Operations.interactionValuesWith_eq_filter]

noncomputable def interactionssWith (table : Table F) (data : ProverData F)
    (channel : RawChannel F) : List (List (Interaction F)) :=
  table.table.map fun row =>
    table.component.operations.interactionValuesWith channel (Environment.fromArray row data)

lemma channel_eq_of_mem_interactionsWith {i : Interaction F} :
    i ∈ table.interactionsWith data channel → i.channel = channel := by
  intro h_mem
  simp only [interactionsWith, List.mem_flatMap] at h_mem
  rcases h_mem with ⟨row, h_row, hi⟩
  simp only [Operations.interactionValuesWith, List.mem_map] at hi
  rcases hi with ⟨i_abs, hi_abs, heq⟩
  rw [←heq]
  apply Operations.channel_eq_of_mem_interactionsWith hi_abs

lemma forall_interactions_iff (table : Table F) (data : ProverData F)
    (motive : Interaction F → Prop) :
    (∀ i ∈ table.interactions data, motive i) ↔
    ∀ row ∈ table.table, ∀ i ∈ table.component.operations.interactions,
      motive (i.eval (Environment.fromArray row data)) := by
  simp only [interactions, Operations.interactionValues, List.mem_flatMap, List.mem_map,
    forall_exists_index, and_imp]
  constructor
  · intro h row h_row i hi
    set env := Environment.fromArray row data
    exact h (i.eval env) row h_row i hi rfl
  · intro h i row h_row i' hi' h_eq
    rw [← h_eq]
    exact h row h_row i' hi'

lemma forall_interactionsWith_iff (table : Table F) (data : ProverData F) (channel : RawChannel F)
  (motive : Interaction F → Prop) :
    (∀ i ∈ table.interactionsWith data channel, motive i) ↔
    ∀ row ∈ table.table, ∀ i ∈ table.component.operations.interactions,
      (i.channel = channel → motive (i.eval (Environment.fromArray row data))) := by
  simp only [interactionsWith, List.mem_flatMap, List.mem_map,
    forall_exists_index, and_imp, circuit_norm]
  constructor
  · intro h row h_row i hi h_channel
    set env := Environment.fromArray row data
    exact h (i.eval env) row h_row i hi h_channel rfl
  · intro h i row h_row i' hi' h_channel h_eq
    rw [← h_eq]
    exact h row h_row i' hi' h_channel

lemma interactionsWith_nil_of_channel_not_mem :
    channel ∉ table.component.circuit.channels → table.interactionsWith data channel = [] := by
  contrapose!
  simp only [AbstractInteraction.eval_channel, interactionsWith_eq_filter, ne_eq, List.filter_eq_nil_iff,
    decide_eq_true_eq, forall_interactions_iff, not_forall, not_not, forall_exists_index]
  intro component table_mem i i_mem channel_eq
  symm at channel_eq; subst channel_eq
  simp only [Component.interactions_eq] at i_mem
  have h_subset := table.component.circuit.channels_subset table.component.rowInputVar
    table.component.rowOffset
  apply h_subset
  simp only [Operations.channels, List.mem_map]
  exists i

lemma guarantees_iff_forall (table : Table F) (data : ProverData F) :
    table.Guarantees data ↔
    ∀ i ∈ table.interactions data, i.Guarantees data := by
  simp only [Table.Guarantees, circuit_norm, forall_interactions_iff]
  rfl

lemma channelGuarantees_iff_forall (table : Table F) (data : ProverData F)
    (channel : RawChannel F) :
    table.ChannelGuarantees data channel ↔
    ∀ i ∈ table.interactionsWith data channel, i.Guarantees data := by
  simp only [Table.ChannelGuarantees, circuit_norm, forall_interactionsWith_iff]
  rfl

lemma guarantees_iff_channelGuarantees (table : Table F) (data : ProverData F) :
    table.Guarantees data ↔
    ∀ channel ∈ table.channelsWithGuarantees, table.ChannelGuarantees data channel := by
  simp only [Table.Guarantees, Table.ChannelGuarantees, channelsWithGuarantees]
  simp only [Component.guarantees_iff, Component.channelGuarantees_iff, Component.rowOperations]
  simp only [GeneralFormalCircuit.guarantees_iff]
  constructor <;> simp_all

lemma channelGuarantees_of_requirements (table : Table F) (data : ProverData F)
    {channel : RawChannel F} :
    table.Guarantees data → table.ChannelGuarantees data channel := by
  simp_all [Table.Guarantees, Table.ChannelGuarantees, circuit_norm]

lemma requirements_iff_forall (table : Table F) (data : ProverData F) :
    table.Requirements data ↔
    ∀ i ∈ table.interactions data, i.Requirements data := by
  simp only [Table.Requirements, circuit_norm, forall_interactions_iff]
  rfl

lemma channelRequirements_iff_forall (table : Table F) (data : ProverData F)
    (channel : RawChannel F) :
    table.ChannelRequirements data channel ↔
    ∀ i ∈ table.interactionsWith data channel, i.Requirements data := by
  simp only [Table.ChannelRequirements, circuit_norm, forall_interactionsWith_iff]
  rfl

lemma requirements_iff_channelRequirements_of_constraints (table : Table F)
    (data : ProverData F) :
    table.Constraints data →
    (table.Requirements data ↔
    ∀ channel ∈ table.channelsWithRequirements, table.ChannelRequirements data channel) := by
  intro h_constraints
  simp only [Table.Requirements, Table.ChannelRequirements, channelsWithRequirements]
  simp only [Component.requirements_iff, Component.channelRequirements_iff, Component.rowOperations]
  simp_rw [Table.Constraints, table.component.constraintsHold_iff] at h_constraints
  constructor
  · intro h_reqs channel h_channel row h_row
    specialize h_reqs row h_row
    rw [table.component.circuit.requirements_iff_of_constraints (h_constraints row h_row)] at h_reqs
    exact h_reqs channel h_channel
  · intro h_reqs row h_row
    rw [table.component.circuit.requirements_iff_of_constraints (h_constraints row h_row)]
    intro channel h_channel
    exact h_reqs channel h_channel row h_row

lemma channelRequirements_of_requirements (table : Table F) (data : ProverData F)
    {channel : RawChannel F} :
    table.Requirements data → table.ChannelRequirements data channel := by
  simp_all [Table.Requirements, Table.ChannelRequirements, circuit_norm]

lemma inChannelsOrRequirements_of_constraints (table : Table F) (data : ProverData F) :
    table.Constraints data →
    table.InChannelsOrRequirements data table.channelsWithRequirements := by
  intro h_constraints
  simp only [InChannelsOrRequirements, channelsWithRequirements]
  intro row h_row
  exact table.component.inChannelsOrRequirements_of_constraints
    (Environment.fromArray row data) (h_constraints row h_row)

lemma requirements_of_not_mem_of_constraints (table : Table F) (data : ProverData F)
    {channel : RawChannel F} :
    table.Constraints data →
    channel ∉ table.channelsWithRequirements → table.ChannelRequirements data channel := by
  intro h_constraints h_not_mem
  have h_in_or_req := table.inChannelsOrRequirements_of_constraints data h_constraints
  simp only [ChannelRequirements, InChannelsOrRequirements] at *
  intro row h_row
  specialize h_in_or_req row h_row
  apply Operations.requirements_of_not_mem _ table.channelsWithRequirements
  assumption
  assumption

lemma inChannelsOrGuarantees (table : Table F) (data : ProverData F) :
    table.InChannelsOrGuarantees data table.channelsWithGuarantees := by
  simp [InChannelsOrGuarantees, channelsWithGuarantees, Component.inChannelsOrGuarantees]

lemma guarantees_of_not_mem (table : Table F) (data : ProverData F) {channel : RawChannel F} :
    channel ∉ table.channelsWithGuarantees → table.ChannelGuarantees data channel := by
  intro h_not_mem
  have h_in_or_guar := table.inChannelsOrGuarantees data
  simp only [ChannelGuarantees, InChannelsOrGuarantees] at *
  intro row h_row
  specialize h_in_or_guar row h_row
  apply Operations.guarantees_of_not_mem _ table.channelsWithGuarantees
  assumption
  assumption

/-- Circuit soundness, lifted to full table level. -/
theorem weakSoundness {table : Table F} (consistent : table.DataConsistency data) :
    table.Assumptions data → table.Constraints data → table.Guarantees data →
    table.Spec data ∧ table.Requirements data := by
  intro assumptions constraints guarantees
  constructor
  · intro row hrow
    exact (table.component.weakSoundness (table.circuitAssumptions consistent assumptions row hrow)
      (constraints row hrow) (guarantees row hrow)).left
  · intro row hrow
    exact (table.component.weakSoundness (table.circuitAssumptions consistent assumptions row hrow)
      (constraints row hrow) (guarantees row hrow)).right

/--
If we know constraints and _some_ of the guarantees unconditionally, we can remove them from the per-row assumptions.

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
    ∀ row ∈ table.table,
      table.component.operations.ChannelGuarantees unfinished (Environment.fromArray row data) →
      table.component.operations.ChannelRequirements unfinished (Environment.fromArray row data) := by
  intro consistent assumptions constraints subset finished_grts row h_row channel_grts
  replace finished_grts channel hc := finished_grts channel hc row h_row
  set env := Environment.fromArray row data
  suffices table.component.operations.FullRequirements env by
    simp only [circuit_norm] at this ⊢
    intro i hi _
    exact this i hi
  suffices table.component.operations.FullGuarantees env from
    table.component.weakSoundness (table.circuitAssumptions consistent assumptions row h_row)
      (constraints row h_row) this |>.right
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
end Table

/-- A table subset together with the shared prover-data environment used to interpret it. -/
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
  simp [interactionsWith, Table.interactionsWith, circuit_norm]

@[circuit_norm] lemma interactionsWith_append {tables1 tables2 : TableContext F}
  (data_eq : tables1.data = tables2.data) {channel : RawChannel F} :
  interactionsWith (append tables1 tables2 data_eq) channel =
    interactionsWith tables1 channel ++ interactionsWith tables2 channel := by
  simp only [interactionsWith, append, List.flatMap_append]
  rw [data_eq]
end TableContext

end Air.Flat
