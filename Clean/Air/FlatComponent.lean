module

public import Clean.Air.Circuit
public import Clean.Air.RowProgram
public import Clean.Air.Window
public import Clean.Air.WitnessGeneration.Generation

@[expose] public section

namespace Air.Flat
variable {F : Type}

/-- Verifier-known columns: `height` rows of type `Row`, computed from the row index. -/
structure FixedColumns (F : Type) extends Witgen.RowProgram F .fixed where
  height : UInt64

namespace FixedColumns
variable [FiniteField F]

/-- The fixed values of row `i`. -/
@[circuit_norm]
def values (fixed : FixedColumns F) (i : UInt64) : Array F :=
  (toElements (fixed.eval i)).toArray

/-- Every row starts with the fixed values of its index. -/
abbrev RowsMatch (fixed : FixedColumns F) (rows : List (Array F)) : Prop :=
  rows.map (fun row => row.extract 0 fixed.width) =
    (List.range fixed.height.toNat).map (fixed.values ∘ UInt64.ofNat)

end FixedColumns

variable [FiniteField F]
variable {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]

/-- The first `n` elements of a row, padded with zeros. -/
@[circuit_norm]
def rowPrefix (n : ℕ) (row : Array F) : Vector F n :=
  ⟨(List.ofFn (fun i : Fin n => row[i.val]?.getD 0)).toArray, by simp⟩

/-- The fixed-column fact about the input of row `i`: the row lies within the fixed height, and the
input's first elements are the row's fixed values. -/
@[circuit_norm]
def FixedInputAt (fixedColumns : Option (FixedColumns F)) (i : UInt64) (input : Input F) : Prop :=
  ∀ fixed ∈ fixedColumns,
    i < fixed.height ∧ (toElements input).toList.take fixed.width = (fixed.values i).toList

/-- The derived-data fact about the input of row `i`: it is row `i` of the component's `ProverData`
entry. -/
@[circuit_norm]
def DataInputAt (name : String) (i : UInt64) (input : Input F) (data : ProverData F) : Prop :=
  (data.getRows name Input)[i.toNat]? = some input

/-- The fact about the previous row available to a row of a two-row component: unless the row is
the first row, the previous row is a transition into it, and satisfies the circuit's spec. A row of
a single-row component knows nothing about other rows. -/
@[circuit_norm]
def PreviousRowAt (window : Option (WindowLayout Input))
    (circuit : GeneralFormalCircuit F Input Output) (input : Input F) (data : ProverData F) :
    Prop :=
  ∀ layout ∈ window, layout.isFirstRow input = 1 ∨
    ∃ previous output, layout.next previous = layout.current input ∧
      layout.isTransition previous = 1 ∧ circuit.Spec previous output data

lemma valueFromOffset_fromArray (row : Array F) (data : ProverData F) :
    valueFromOffset Input 0 (Environment.fromArray row data) =
      fromElements (rowPrefix (size Input) row) := by
  simp only [valueFromOffset]
  congr 1
  ext j hj
  simp [rowPrefix, Vector.getElem_mapRange]

/--
An AIR component: one circuit whose constraints are checked on each row. Communication with other
components is expressed by channel interactions.

The circuit of a single-row component reads only its row. The circuit of a two-row component reads a
`Window` of the trace, which adds the next row's input and the row's selectors to the row's own
input, see `Clean.Air.Window`.
-/
structure Component (F : Type) [FiniteField F] where
  {Input : TypeMap} {Output : TypeMap}
  [provableInput : ProvableType Input] [provableOutput : ProvableType Output]
  circuit : GeneralFormalCircuit F Input Output
  /-- Fixed columns, which form a prefix of the input. -/
  fixedColumns : Option (FixedColumns F) := none
  /-- For a two-row component, where the circuit input keeps the window cells: the next row's input
  and the row's selectors. -/
  window : Option (WindowLayout Input) := none
  /-- Assumptions the ensemble has to provide, beyond the fixed-row, data and previous-row facts. -/
  Assumptions : Input F → ProverData F → Prop := fun _ _ => True
  /-- Fixed-row, data and previous-row facts, together with `Assumptions`, imply the circuit's
  assumptions. -/
  circuit_assumptions_of_assumptions : ∀ (i : UInt64) (input : Input F) data,
      FixedInputAt fixedColumns i input → DataInputAt circuit.name i input data →
        PreviousRowAt window circuit input data →
        Assumptions input data → circuit.Assumptions input data := by intros; trivial
  /-- The fixed columns are a prefix of the row's own input. -/
  fixed_width_le_input :
      (fixedColumns.map (·.width)).getD 0 ≤ (window.map (·.rowWidth)).getD (size Input) := by
    simp <;> exact Nat.le_of_ble_eq_true rfl
  /-- How the prover builds the component's rows: preallocated if it has fixed columns, demand
  otherwise. See `Clean.Air.WitnessGeneration.Generation`. -/
  generation : WitnessGeneration.Generation F Input
  generation_preallocated : generation.isPreallocated = fixedColumns.isSome := by rfl

instance (t: Component F) : ProvableType t.Input := t.provableInput
instance (t: Component F) : ProvableType t.Output := t.provableOutput

namespace Component
def fixedWidth (component : Component F) : ℕ :=
  component.fixedColumns.map (·.width) |>.getD 0

def FixedRowsMatch (component : Component F) (rows : List (Array F)) : Prop :=
  match component.fixedColumns with
  | none => True
  | some fixed => FixedColumns.RowsMatch fixed rows

/-- The number of input cells that a row stores itself: all of them, except the window cells of a
two-row component. -/
def ownInputWidth (component : Component F) : ℕ :=
  (component.window.map (·.rowWidth)).getD (size component.Input)

/-- The number of input cells that only a two-row component has: the next row's input and the
selectors. -/
def windowWidth (component : Component F) : ℕ :=
  (component.window.map (·.windowWidth)).getD 0

/-- Whether a cell of a row is a window cell of a two-row component. -/
def isWindowCell (component : Component F) (cell : ℕ) : Bool :=
  match component.window with
  | none => false
  | some layout => layout.rowWidth ≤ cell && cell < 2 * layout.rowWidth + 3

/-- The input of a row. -/
def inputOf (component : Component F) (row : Array F) : component.Input F :=
  fromElements (rowPrefix (size component.Input) row)

/-- The window cells of every row of a two-row component hold the next row's own input, where the
next row of the last row is the first row, and the row's selectors. -/
def WindowsMatch (component : Component F) (rows : List (Array F)) : Prop :=
  match component.window with
  | none => True
  | some layout => ∀ i (hi : i < rows.length),
      layout.next (component.inputOf rows[i]) =
        layout.current (component.inputOf (rows[(i + 1) % rows.length]'(Nat.mod_lt _ (by omega))))
        ∧ layout.SelectorsAt (component.inputOf rows[i]) i rows.length

instance (component : Component F) (rows : List (Array F)) :
    Decidable (component.WindowsMatch rows) := by
  unfold WindowsMatch WindowLayout.SelectorsAt
  split <;> infer_instance

def operations (component : Component F) : Operations F :=
  component.circuit.instantiate.operations 0

def width (component : Component F) : ℕ := component.circuit.size

@[circuit_norm]
def rowOffset (component : Component F) : ℕ := size component.Input

@[circuit_norm]
def rowInputVar (component : Component F): Var component.Input F :=
  varFromOffset component.Input 0

/-- first `size Input` elements of the environment are the input -/
@[circuit_norm]
def rowInput (component : Component F) (row : Environment F) : component.Input F :=
  valueFromOffset component.Input 0 row

/-- output is whatever the circuit computes on the row input -/
@[circuit_norm]
def rowOutput (component : Component F) (row : Environment F) : component.Output F :=
  let outputVar := (component.circuit component.rowInputVar).output component.rowOffset
  eval row outputVar

@[circuit_norm]
def rowOperations (component : Component F) : Operations F :=
  component.circuit.main (varFromOffset component.Input 0) |>.operations (size component.Input)

lemma rowInput_fromArray (component : Component F) (row : Array F) (data : ProverData F) :
    component.rowInput (Environment.fromArray row data) = component.inputOf row :=
  valueFromOffset_fromArray row data

def Spec (component : Component F) (row : Environment F) : Prop :=
  component.circuit.Spec (component.rowInput row) (component.rowOutput row) row.data

def CircuitAssumptions (component : Component F) (row : Environment F) : Prop :=
  component.circuit.Assumptions (component.rowInput row) row.data

/-- The component's `Assumptions` on a row. -/
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

/-- Concrete rows and prover data for one flat AIR component. -/
structure Table (F : Type) [FiniteField F] where
  component : Component F
  table : List (Array F)
  data : ProverData F
  uniform_width : ∀ row ∈ table, row.size = component.width
  /-- Row indices are `u64` values. -/
  length_le : table.length ≤ UInt64.size
  /-- The rows start with the fixed columns. -/
  fixed_rows_match : component.FixedRowsMatch table
  /-- The window cells of a two-row component's rows match the next rows and the selectors. -/
  windows_match : component.WindowsMatch table

/-- The table's rows cut off at `n` elements. -/
def Table.proverRows (table : Table F) (n : ℕ) : Array (Vector F n) :=
  (table.table.map (rowPrefix n)).toArray

/-- The prover data of a list of tables: the input rows of each component, under its name. -/
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

/-- `deriveProverData` only reads the components and rows of the tables. -/
lemma deriveProverData_map_data (tables : List (Table F)) (data : ProverData F) :
    deriveProverData (tables.map fun table => { table with data }) = deriveProverData tables := by
  induction tables with
  | nil => rfl
  | cons table tables ih => rw [List.map_cons, deriveProverData, deriveProverData, ih]; rfl

/-- Gives every table the prover data derived from all of them. -/
def withDerivedData (tables : List (Table F)) : List (Table F) :=
  tables.map fun table => { table with data := deriveProverData tables }

@[circuit_norm] lemma withDerivedData_map_component (tables : List (Table F)) :
    (withDerivedData tables).map (·.component) = tables.map (·.component) := by
  simp [withDerivedData]

lemma withDerivedData_data (tables : List (Table F)) :
    ∀ table ∈ withDerivedData tables, table.data = deriveProverData (withDerivedData tables) := by
  simp [withDerivedData, deriveProverData_map_data]

namespace Table
variable {table : Table F} {channel : RawChannel F}

/-- The table's prover data contains its own component's circuit-input rows. -/
def DataConsistency (table : Table F) : Prop :=
  table.data table.component.circuit.name (size table.component.Input) =
    table.proverRows (size table.component.Input)

abbrev length (t : Table F) : ℕ := t.table.length

def environment (table : Table F) (row : Array F) :=
  Environment.fromArray row table.data

theorem ext_iff {table1 table2 : Table F} :
    table1 = table2 ↔
    table1.component = table2.component ∧
    table1.table = table2.table ∧
    table1.data = table2.data := by
  cases table1
  cases table2
  simp only [mk.injEq]

@[circuit_norm]
def channelsWithGuarantees (table : Table F) : List (RawChannel F) :=
  table.component.circuit.channelsWithGuarantees

@[circuit_norm]
def channelsWithRequirements (table : Table F) : List (RawChannel F) :=
  table.component.circuit.channelsWithRequirements

def Constraints (table : Table F) : Prop :=
  ∀ row ∈ table.table,
    table.component.operations.ConstraintsHold (table.environment row)

def Assumptions (table : Table F) : Prop :=
  ∀ row ∈ table.table,
    table.component.RowAssumptions (table.environment row)

/-- The circuit's assumptions on row `i`, from the facts about its input and the previous row. -/
lemma circuitAssumptions_at (table : Table F) (consistent : table.DataConsistency)
    (assumptions : table.Assumptions) (i : ℕ) (hi : i < table.length)
    (previous : PreviousRowAt table.component.window table.component.circuit
      (table.component.inputOf table.table[i]) table.data) :
    table.component.CircuitAssumptions (table.environment table.table[i]) := by
  unfold environment
  replace hi : i < table.table.length := hi
  obtain ⟨row, hi'⟩ : ∃ row, table.table[i] = row := ⟨_, rfl⟩
  rw [hi'] at previous ⊢
  have hindex : (UInt64.ofNat i).toNat = i :=
    UInt64.toNat_ofNat_of_lt' (Nat.lt_of_lt_of_le hi table.length_le)
  have hinput := table.component.rowInput_fromArray row table.data
  apply table.component.circuit_assumptions_of_assumptions (UInt64.ofNat i)
  · cases hcolumns : table.component.fixedColumns with
    | none => simp [FixedInputAt]
    | some fixed =>
      have hmatch := table.fixed_rows_match
      simp only [Component.FixedRowsMatch, hcolumns] at hmatch
      have hlength : table.table.length = fixed.height.toNat := by
        simpa using congrArg List.length hmatch
      have hprefix := congrArg (fun rows => rows[i]?) hmatch
      simp only [List.getElem?_map, List.getElem?_range (by omega : i < fixed.height.toNat),
        List.getElem?_eq_getElem hi, hi', Option.map_some, Option.some.injEq,
        Function.comp_apply] at hprefix
      have hsize : fixed.width ≤ row.size := by
        have := congrArg Array.size hprefix
        simp [FixedColumns.values] at this
        omega
      have hwidth : fixed.width ≤ size table.component.Input := by
        have := table.component.fixed_width_le_input
        cases hwindow : table.component.window with
        | none => simpa [hcolumns, hwindow] using this
        | some layout =>
          have := layout.size_eq
          simp [hcolumns, hwindow] at *
          omega
      rintro _ ⟨⟩
      refine ⟨by simp [UInt64.lt_iff_toNat_lt, hindex]; omega, ?_⟩
      rw [Component.rowInput, valueFromOffset_fromArray, ProvableType.toElements_fromElements,
        ← hprefix]
      apply List.ext_getElem
      · simp; omega
      · intro j hj _
        simp only [List.length_take, Vector.length_toList] at hj
        simp [rowPrefix, show j < row.size by omega]
  · simp only [DataInputAt, ProverData.getRows, Component.rowInput, valueFromOffset_fromArray,
      hindex]
    rw [consistent]
    simp [proverRows, hi, hi']
  · rw [hinput]
    exact previous
  · exact assumptions row (hi' ▸ List.getElem_mem hi)

/-- The circuit's assumptions on a row of a single-row component. -/
lemma circuitAssumptions_of_dataConsistency (table : Table F) (consistent : table.DataConsistency)
    (assumptions : table.Assumptions) (single_row : table.component.window = none)
    (row : Array F) (hrow : row ∈ table.table) :
    table.component.CircuitAssumptions (table.environment row) := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hrow
  exact table.circuitAssumptions_at consistent assumptions i hi
    (by simp [PreviousRowAt, single_row])

/-- Along a two-row table, every row's spec gives the next row's previous-row fact. -/
lemma previousRowAt_succ (table : Table F) (i : ℕ) (hi : i + 1 < table.table.length)
    (spec : table.component.Spec (table.environment table.table[i])) :
    PreviousRowAt table.component.window table.component.circuit
      (table.component.inputOf table.table[i + 1]) table.data := by
  intro layout hlayout
  have hmatch := table.windows_match
  rw [Option.mem_def] at hlayout
  simp only [Component.WindowsMatch, hlayout] at hmatch
  obtain ⟨hnext, -, -, htransition⟩ := hmatch i (by omega)
  right
  refine ⟨table.component.inputOf table.table[i],
    table.component.rowOutput (table.environment table.table[i]), ?_, ?_, ?_⟩
  · rw [hnext]
    simp only [Nat.mod_eq_of_lt hi]
  · simp [htransition, show i + 1 ≠ table.table.length by omega]
  · simpa only [Component.Spec, environment, Component.rowInput_fromArray] using spec

/-- The first row of a two-row table is the first row. -/
lemma previousRowAt_zero (table : Table F) (hi : 0 < table.table.length) :
    PreviousRowAt table.component.window table.component.circuit
      (table.component.inputOf table.table[0]) table.data := by
  intro layout hlayout
  have hmatch := table.windows_match
  rw [Option.mem_def] at hlayout
  simp only [Component.WindowsMatch, hlayout] at hmatch
  left
  simp [(hmatch 0 hi).2.1]

def Guarantees (table : Table F) : Prop :=
  ∀ row ∈ table.table,
    table.component.operations.FullGuarantees (table.environment row)

def ChannelGuarantees (table : Table F) (channel : RawChannel F) : Prop :=
  ∀ row ∈ table.table,
    table.component.operations.ChannelGuarantees channel (table.environment row)

def InChannelsOrGuarantees (table : Table F) (channels : List (RawChannel F)) : Prop :=
  ∀ row ∈ table.table,
    table.component.operations.InChannelsOrGuaranteesFull channels (table.environment row)

def Requirements (table : Table F) : Prop :=
  ∀ row ∈ table.table,
    table.component.operations.FullRequirements (table.environment row)

def ChannelRequirements (table : Table F) (channel : RawChannel F) : Prop :=
  ∀ row ∈ table.table,
    table.component.operations.ChannelRequirements channel (table.environment row)

def InChannelsOrRequirements (table : Table F) (channels : List (RawChannel F)) : Prop :=
  ∀ row ∈ table.table,
    table.component.operations.InChannelsOrRequirementsFull channels (table.environment row)

def Spec (table : Table F) : Prop :=
  ∀ row ∈ table.table,
    table.component.Spec (table.environment row)

def interactions (table : Table F) : List (Interaction F) :=
  table.table.flatMap fun row =>
    table.component.operations.interactionValues (table.environment row)

noncomputable def interactionsWith (table : Table F) (channel : RawChannel F) : List (Interaction F) :=
  table.table.flatMap fun row =>
    table.component.operations.interactionValuesWith channel (table.environment row)

open Classical in lemma interactionsWith_eq_filter :
    table.interactionsWith channel = table.interactions.filter (·.channel = channel) := by
  simp only [interactionsWith, interactions, List.filter_flatMap]
  congr
  funext row
  rw [Operations.interactionValuesWith_eq_filter]

noncomputable def interactionssWith (table : Table F) (channel : RawChannel F) : List
    (List (Interaction F)) :=
  table.table.map fun row =>
    table.component.operations.interactionValuesWith channel (table.environment row)

lemma channel_eq_of_mem_interactionsWith {i : Interaction F} :
    i ∈ table.interactionsWith channel → i.channel = channel := by
  intro h_mem
  simp only [interactionsWith, List.mem_flatMap] at h_mem
  rcases h_mem with ⟨row, h_row, hi⟩
  simp only [Operations.interactionValuesWith, List.mem_map] at hi
  rcases hi with ⟨i_abs, hi_abs, heq⟩
  rw [←heq]
  apply Operations.channel_eq_of_mem_interactionsWith hi_abs

lemma forall_interactions_iff (table : Table F) (motive : Interaction F → Prop) :
    (∀ i ∈ table.interactions, motive i) ↔
    ∀ row ∈ table.table, ∀ i ∈ table.component.operations.interactions,
      motive (i.eval (table.environment row)) := by
  simp only [interactions, Operations.interactionValues, List.mem_flatMap, List.mem_map,
    forall_exists_index, and_imp]
  constructor
  · intro h row h_row i hi
    set env := table.environment row
    exact h (i.eval env) row h_row i hi rfl
  · intro h i row h_row i' hi' h_eq
    rw [← h_eq]
    exact h row h_row i' hi'

lemma forall_interactionsWith_iff (table : Table F) (channel : RawChannel F)
  (motive : Interaction F → Prop) :
    (∀ i ∈ table.interactionsWith channel, motive i) ↔
    ∀ row ∈ table.table, ∀ i ∈ table.component.operations.interactions,
      (i.channel = channel → motive (i.eval (table.environment row))) := by
  simp only [interactionsWith, List.mem_flatMap, List.mem_map,
    forall_exists_index, and_imp, circuit_norm]
  constructor
  · intro h row h_row i hi h_channel
    set env := table.environment row
    exact h (i.eval env) row h_row i hi h_channel rfl
  · intro h i row h_row i' hi' h_channel h_eq
    rw [← h_eq]
    exact h row h_row i' hi' h_channel

lemma interactionsWith_nil_of_channel_not_mem :
    channel ∉ table.component.circuit.channels → table.interactionsWith channel = [] := by
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

lemma guarantees_iff_forall (table : Table F) :
    table.Guarantees ↔
    ∀ i ∈ table.interactions, i.Guarantees table.data := by
  simp only [Table.Guarantees, circuit_norm, forall_interactions_iff]
  rfl

lemma channelGuarantees_iff_forall (table : Table F) (channel : RawChannel F) :
    table.ChannelGuarantees channel ↔
    ∀ i ∈ table.interactionsWith channel, i.Guarantees table.data := by
  simp only [Table.ChannelGuarantees, circuit_norm, forall_interactionsWith_iff]
  rfl

lemma guarantees_iff_channelGuarantees (table : Table F) :
    table.Guarantees ↔
    ∀ channel ∈ table.channelsWithGuarantees, table.ChannelGuarantees channel := by
  simp only [Table.Guarantees, Table.ChannelGuarantees, channelsWithGuarantees]
  simp only [Component.guarantees_iff, Component.channelGuarantees_iff, Component.rowOperations]
  simp only [GeneralFormalCircuit.guarantees_iff]
  constructor <;> simp_all

lemma channelGuarantees_of_requirements (table : Table F) {channel : RawChannel F} :
    table.Guarantees → table.ChannelGuarantees channel := by
  simp_all [Table.Guarantees, Table.ChannelGuarantees, circuit_norm]

lemma requirements_iff_forall (table : Table F) :
    table.Requirements ↔
    ∀ i ∈ table.interactions, i.Requirements table.data := by
  simp only [Table.Requirements, circuit_norm, forall_interactions_iff]
  rfl

lemma channelRequirements_iff_forall (table : Table F) (channel : RawChannel F) :
    table.ChannelRequirements channel ↔
    ∀ i ∈ table.interactionsWith channel, i.Requirements table.data := by
  simp only [Table.ChannelRequirements, circuit_norm, forall_interactionsWith_iff]
  rfl

lemma requirements_iff_channelRequirements_of_constraints (table : Table F) :
    table.Constraints →
    (table.Requirements ↔
    ∀ channel ∈ table.channelsWithRequirements, table.ChannelRequirements channel) := by
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

lemma channelRequirements_of_requirements (table : Table F) {channel : RawChannel F} :
    table.Requirements → table.ChannelRequirements channel := by
  simp_all [Table.Requirements, Table.ChannelRequirements, circuit_norm]

lemma inChannelsOrRequirements_of_constraints (table : Table F) :
    table.Constraints →
    table.InChannelsOrRequirements table.channelsWithRequirements := by
  intro h_constraints
  simp only [InChannelsOrRequirements, channelsWithRequirements]
  intro row h_row
  exact table.component.inChannelsOrRequirements_of_constraints
    (table.environment row) (h_constraints row h_row)

lemma requirements_of_not_mem_of_constraints (table : Table F) {channel : RawChannel F} :
    table.Constraints →
    channel ∉ table.channelsWithRequirements → table.ChannelRequirements channel := by
  intro h_constraints h_not_mem
  have h_in_or_req := table.inChannelsOrRequirements_of_constraints h_constraints
  simp only [ChannelRequirements, InChannelsOrRequirements] at *
  intro row h_row
  specialize h_in_or_req row h_row
  apply Operations.requirements_of_not_mem _ table.channelsWithRequirements
  assumption
  assumption

lemma inChannelsOrGuarantees (table : Table F) :
    table.InChannelsOrGuarantees table.channelsWithGuarantees := by
  simp [InChannelsOrGuarantees, channelsWithGuarantees, Component.inChannelsOrGuarantees]

lemma guarantees_of_not_mem (table : Table F) {channel : RawChannel F} :
    channel ∉ table.channelsWithGuarantees → table.ChannelGuarantees channel := by
  intro h_not_mem
  have h_in_or_guar := table.inChannelsOrGuarantees
  simp only [ChannelGuarantees, InChannelsOrGuarantees] at *
  intro row h_row
  specialize h_in_or_guar row h_row
  apply Operations.guarantees_of_not_mem _ table.channelsWithGuarantees
  assumption
  assumption

/-- Circuit soundness, lifted to full table level. Along a two-row table, this is an induction:
each row's spec gives the next row's circuit assumptions. -/
theorem weakSoundness {table : Table F} (consistent : table.DataConsistency) :
    table.Assumptions → table.Constraints → table.Guarantees →
    table.Spec ∧ table.Requirements := by
  intro assumptions constraints guarantees
  have rows : ∀ i (hi : i < table.length),
      table.component.Spec (table.environment table.table[i]) ∧
        table.component.operations.FullRequirements (table.environment table.table[i]) := by
    intro i
    induction i with
    | zero =>
      intro hi
      exact table.component.weakSoundness
        (table.circuitAssumptions_at consistent assumptions 0 hi (table.previousRowAt_zero hi))
        (constraints _ (List.getElem_mem hi)) (guarantees _ (List.getElem_mem hi))
    | succ i ih =>
      intro hi
      exact table.component.weakSoundness
        (table.circuitAssumptions_at consistent assumptions (i + 1) hi
          (table.previousRowAt_succ i hi (ih (by omega)).left))
        (constraints _ (List.getElem_mem hi)) (guarantees _ (List.getElem_mem hi))
  constructor
  · intro row hrow
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hrow
    exact (rows i hi).left
  · intro row hrow
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hrow
    exact (rows i hi).right

/--
If we know constraints and _some_ of the guarantees unconditionally, we can remove them from the per-row assumptions.

This lemma is tailored to VM-like channels where there remains a single channel that we need to
prove guarantees for.
-/
lemma requirements_of_partial_guarantees_of_constraints {table : Table F}
  {finished : List (RawChannel F)} {unfinished : RawChannel F} :
  table.component.window = none →
  table.DataConsistency →
  table.Assumptions →
  table.Constraints →
  table.channelsWithGuarantees ⊆ unfinished :: finished →
  (∀ channel ∈ finished, table.ChannelGuarantees channel) →
    ∀ row ∈ table.table,
      table.component.operations.ChannelGuarantees unfinished (table.environment row) →
      table.component.operations.ChannelRequirements unfinished (table.environment row) := by
  intro single_row consistent assumptions constraints subset finished_grts row h_row channel_grts
  replace finished_grts channel hc := finished_grts channel hc row h_row
  set env := table.environment row
  suffices table.component.operations.FullRequirements env by
    simp only [circuit_norm] at this ⊢
    intro i hi _
    exact this i hi
  suffices table.component.operations.FullGuarantees env from
    table.component.weakSoundness
      (table.circuitAssumptions_of_dataConsistency consistent assumptions single_row row h_row)
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

/-- Light-weight package of multiple flat AIR tables sharing one prover data object. -/
structure Tables (F : Type) [FiniteField F] where
  tables : List (Table F)
  data : ProverData F
  same_data : ∀ table ∈ tables, table.data = data

namespace Tables
def cons (table : Table F) (tables : Tables F) (same_data : table.data = tables.data) : Tables F where
  tables := table :: tables.tables
  data := tables.data
  same_data := by
    simp [same_data]
    apply tables.same_data

@[circuit_norm] lemma cons_tables {table : Table F} {tables : Tables F} (same_data : table.data = tables.data) :
  (cons table tables same_data).tables = table :: tables.tables := rfl

@[circuit_norm] lemma cons_data {table : Table F} {tables : Tables F} (same_data : table.data = tables.data) :
  (cons table tables same_data).data = tables.data := rfl

def induct {motive : Tables F → Sort*}
  (nil : ∀ data, motive ⟨ [], data, by simp ⟩)
  (cons : ∀ table tables same_data, motive tables → motive (cons table tables same_data))
    (tables : Tables F) : motive tables := by
  rcases tables with ⟨ ts, data, same_data ⟩
  induction ts with
  | nil => exact nil data
  | cons table ts ih =>
    have same_data' : ∀ table ∈ ts, table.data = data := by
      intro table h_table
      apply same_data
      simp [h_table]
    let tables : Tables F := ⟨ ts, data, same_data' ⟩
    have same_data_table : table.data = tables.data := by
      simp [tables, same_data]
    apply cons table tables same_data_table
    exact ih same_data'

def append (tables1 tables2 : Tables F) (same_data : tables1.data = tables2.data) : Tables F where
  tables := tables1.tables ++ tables2.tables
  data := tables1.data
  same_data := by
    simp [or_imp, forall_and]
    constructor
    · apply tables1.same_data
    rw [same_data]
    apply tables2.same_data

@[circuit_norm] lemma append_tables {tables1 tables2 : Tables F} (same_data : tables1.data = tables2.data) :
  (append tables1 tables2 same_data).tables = tables1.tables ++ tables2.tables := rfl

@[circuit_norm] lemma append_data {tables1 tables2 : Tables F} (same_data : tables1.data = tables2.data) :
  (append tables1 tables2 same_data).data = tables1.data := rfl

@[circuit_norm] lemma cons_append {table : Table F} {tables1 tables2 : Tables F}
  (same_data1 : table.data = tables1.data) (same_data2 : tables1.data = tables2.data) :
  (cons table tables1 same_data1).append tables2 same_data2 =
    cons table (append tables1 tables2 same_data2) same_data1 := rfl

@[circuit_norm]
abbrev components (tables : Tables F) : List (Component F) :=
  tables.tables.map (·.component)

instance : Coe (Tables F) (List (Table F)) where
  coe tables := tables.tables

abbrev Constraints (tables : Tables F) : Prop :=
  ∀ table ∈ tables.tables, table.Constraints

abbrev Assumptions (tables : Tables F) : Prop :=
  ∀ table ∈ tables.tables, table.Assumptions

noncomputable abbrev interactionsWith (tables : Tables F) (channel : RawChannel F) : List (Interaction F) :=
  tables.tables.flatMap (·.interactionsWith channel)

@[circuit_norm] lemma interactionsWith_cons {table : Table F} {tables : Tables F}
  (same_data : table.data = tables.data) {channel : RawChannel F} :
  interactionsWith (cons table tables same_data) channel =
    table.interactionsWith channel ++ interactionsWith tables channel := by
  simp [interactionsWith, Table.interactionsWith, circuit_norm]

@[circuit_norm] lemma interactionsWith_append {tables1 tables2 : Tables F}
  (same_data : tables1.data = tables2.data) {channel : RawChannel F} :
  interactionsWith (append tables1 tables2 same_data) channel =
    interactionsWith tables1 channel ++ interactionsWith tables2 channel := by
  simp [interactionsWith, Table.interactionsWith, circuit_norm]
end Tables

end Air.Flat
