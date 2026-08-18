/-
Shared infrastructure for AIR components and their traces.

Each concrete table kind supplies only its `RowEnvs` instance and its own `circuitAssumptions`
lemma.
-/
import Clean.Air.Circuit

namespace Air.Flat
universe u
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
An AIR component: a row circuit together with its fixed columns and residual assumptions.

A component *does* say how many trace rows its environment spans, via `windowRows`: 1 for a flat
component checked against a single row, 2 for a transition component checked against two adjacent
rows laid side by side. Communication with other components is expressed by channel interactions.

The window is recorded here, on the object the verifier commits to, rather than as a separate tag
on the ensemble entry. `window_size` ties it to the circuit's own cell footprint, which is what
makes the reading of an environment derivable from the component instead of a prover choice.

For a transition component the layout is what makes both completeness and the spec work out:

    Input  = Row (width w)      cells [0, w)   -- row i,   prover-chosen via `witnessAny`
    main allocates w cells      cells [w, 2w)  -- row i+1, pinned by local-witness completeness

so the next row is the circuit's *output*, and `Spec input output` is the transition relation.
-/
structure Component (F : Type) [FiniteField F] where
  {Input : TypeMap} {Output : TypeMap}
  [provableInput : ProvableType Input] [provableOutput : ProvableType Output]
  circuit : GeneralFormalCircuit F Input Output
  /-- How many trace rows one instantiation's environment spans. 1 = flat, 2 = transition. -/
  windowRows : ℕ := 1
  /-- The width of a single trace row. The circuit's footprint spans `windowRows` of them. -/
  rowWidth : ℕ := circuit.size
  /-- The circuit's cells tile exactly `windowRows` rows. This is the law that makes the window
  derivable from the component, and it is why no separate `TableKind` tag is needed. -/
  window_size : circuit.size = windowRows * rowWidth := by simp
  windowRows_pos : 0 < windowRows := by simp
  /-- The circuit's input occupies the low cells of the window's *first* row.

  Not derivable from `window_size`: a component with `windowRows = 2`, `size Input = 10`,
  `localLength = 0` and `rowWidth = 5` satisfies the tiling yet has its input spill across both
  rows. The fixed-column and `ProverData` machinery are all stated about a single row's low
  indices (`FixedRowAt`, `DataRowAt`, `inputRow`), so that must be ruled out. -/
  input_le_rowWidth : size Input ≤ rowWidth := by simp [GeneralFormalCircuit.size_eq]
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

/-- The number of cells a single instantiation of the circuit commits: its input cells followed
by its witnessed cells.

This spans the component's whole window, so it is `windowRows` rows wide. For a flat component
that is exactly one trace row; for a transition component it is the two rows `curr ++ next`. -/
def envWidth (component : Component F) : ℕ := component.windowRows * component.rowWidth

/-- The circuit's footprint *is* its window. Restated from the `window_size` field so that callers
can rewrite in either direction without unfolding the structure. -/
@[circuit_norm] lemma envWidth_eq_size (component : Component F) :
    component.envWidth = component.circuit.size := component.window_size.symm

lemma envWidth_eq (component : Component F) :
    component.envWidth = component.windowRows * component.rowWidth := rfl

def committedWidth (component : Component F) : ℕ :=
  component.rowWidth - component.fixedWidth

def rowOffset (component : Component F) : ℕ := size component.Input

def rowInputVar (component : Component F): Var component.Input F :=
  varFromOffset component.Input 0

@[circuit_norm]
lemma rowWidth_mk (circuit : GeneralFormalCircuit F Input Output) :
  ({ circuit } : Component F).rowWidth = circuit.size := rfl

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

/-
The transport lemmas below relate the instantiated `operations` to the raw `rowOperations`. They
are facts about `GeneralFormalCircuit.instantiate` alone, and say nothing about how many rows an
environment spans -- which is why both table kinds share them.
-/

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

/--
A trace presented as the list of environments at which its component is checked.

This is the single point at which the two AIR component kinds differ:

* a flat table yields one environment per row, `Environment.fromArray row data`;
* a transition table yields one per *adjacent pair*, `Environment.fromArray (curr ++ next) data`,
  so a trace of `n` rows yields `n - 1` environments.

Every trace-level predicate and every interaction-collection definition below is stated once
against this interface, and is therefore shared by both kinds.
-/
class RowEnvs (F : Type) [FiniteField F] (T : Type u) where
  /-- The component whose circuit is checked at each environment. -/
  component : T → Component F
  /-- The environments at which the component's constraints are checked.

  Indices are deliberately *not* carried here: only each kind's own `circuitAssumptions` lemma
  needs them, and threading them through this list would force an extra binder through every
  shared proof below. -/
  envs : T → ProverData F → List (Environment F)
  /-- Every presented environment carries the prover data it was built from. Both kinds build
  their environments with `Environment.fromArray _ data`, so this holds by `rfl`; stating it
  lets the interaction lemmas below bridge `AbstractInteraction.Guarantees _ env`, which reads
  `env.data`, with `Interaction.Guarantees _ data`. -/
  data_eq : ∀ table data, ∀ e ∈ envs table data, Environment.data e = data

namespace RowEnvs
variable {T : Type u} [RowEnvs F T] {table : T} {data : ProverData F} {channel : RawChannel F}

lemma data_eq_of_mem {e : Environment F} (h : e ∈ envs (F:=F) table data) : e.data = data :=
  RowEnvs.data_eq table data e h

/-
Trace-level predicates. Each quantifies over `envs`; none inspects an individual environment,
which is exactly why they are shared.
-/

def Constraints (table : T) (data : ProverData F) : Prop :=
  ∀ env ∈ envs (F:=F) table data, (component (F:=F) table).operations.ConstraintsHold env

def Assumptions (table : T) (data : ProverData F) : Prop :=
  ∀ env ∈ envs (F:=F) table data, (component (F:=F) table).RowAssumptions env

def CircuitAssumptions (table : T) (data : ProverData F) : Prop :=
  ∀ env ∈ envs (F:=F) table data, (component (F:=F) table).CircuitAssumptions env

def Guarantees (table : T) (data : ProverData F) : Prop :=
  ∀ env ∈ envs (F:=F) table data, (component (F:=F) table).operations.FullGuarantees env

def ChannelGuarantees (table : T) (data : ProverData F) (channel : RawChannel F) : Prop :=
  ∀ env ∈ envs (F:=F) table data,
    (component (F:=F) table).operations.ChannelGuarantees channel env

def InChannelsOrGuarantees (table : T) (data : ProverData F)
    (channels : List (RawChannel F)) : Prop :=
  ∀ env ∈ envs (F:=F) table data,
    (component (F:=F) table).operations.InChannelsOrGuaranteesFull channels env

def Requirements (table : T) (data : ProverData F) : Prop :=
  ∀ env ∈ envs (F:=F) table data, (component (F:=F) table).operations.FullRequirements env

def ChannelRequirements (table : T) (data : ProverData F) (channel : RawChannel F) : Prop :=
  ∀ env ∈ envs (F:=F) table data,
    (component (F:=F) table).operations.ChannelRequirements channel env

def InChannelsOrRequirements (table : T) (data : ProverData F)
    (channels : List (RawChannel F)) : Prop :=
  ∀ env ∈ envs (F:=F) table data,
    (component (F:=F) table).operations.InChannelsOrRequirementsFull channels env

def Spec (table : T) (data : ProverData F) : Prop :=
  ∀ env ∈ envs (F:=F) table data, (component (F:=F) table).Spec env

@[circuit_norm]
def channelsWithGuarantees (table : T) : List (RawChannel F) :=
  (component (F:=F) table).circuit.channelsWithGuarantees

@[circuit_norm]
def channelsWithRequirements (table : T) : List (RawChannel F) :=
  (component (F:=F) table).circuit.channelsWithRequirements

/-
Interaction collection. A component emits its interactions once per environment, so a transition
table of `n` rows contributes `n - 1` copies rather than `n`.

This matters for `BalancedInteractions`, which carries a side condition that the total interaction
count is below `ringChar F` -- without it, `p` copies of a push would sum to zero and forge
balance. Any bound on the total interaction count derived from table heights must therefore use
`n - 1` for transition entries, and note that a 0- or 1-row transition table emits nothing at all.
-/

def interactions (table : T) (data : ProverData F) : List (Interaction F) :=
  (envs (F:=F) table data).flatMap fun env =>
    (component (F:=F) table).operations.interactionValues env

noncomputable def interactionsWith (table : T) (data : ProverData F)
    (channel : RawChannel F) : List (Interaction F) :=
  (envs (F:=F) table data).flatMap fun env =>
    (component (F:=F) table).operations.interactionValuesWith channel env

noncomputable def interactionssWith (table : T) (data : ProverData F)
    (channel : RawChannel F) : List (List (Interaction F)) :=
  (envs (F:=F) table data).map fun env =>
    (component (F:=F) table).operations.interactionValuesWith channel env

/-
Unfolding lemmas for the interaction collections. Downstream proofs reason about the underlying
`flatMap`/`map` structure, so these expose it without making the definitions themselves reducible.

Deliberately *not* `@[circuit_norm]`: as simp lemmas they fire ahead of `forall_interactions_iff`
and friends, which expect the collections still folded. Name them explicitly where the underlying
list structure is actually needed.
-/

lemma interactions_def (table : T) (data : ProverData F) :
    interactions (F:=F) table data = (envs (F:=F) table data).flatMap fun env =>
      (component (F:=F) table).operations.interactionValues env := rfl

lemma interactionsWith_def (table : T) (data : ProverData F)
    (channel : RawChannel F) :
    interactionsWith (F:=F) table data channel = (envs (F:=F) table data).flatMap fun env =>
      (component (F:=F) table).operations.interactionValuesWith channel env := rfl

lemma interactionssWith_def (table : T) (data : ProverData F)
    (channel : RawChannel F) :
    interactionssWith (F:=F) table data channel = (envs (F:=F) table data).map fun env =>
      (component (F:=F) table).operations.interactionValuesWith channel env := rfl

open Classical in lemma interactionsWith_eq_filter :
    interactionsWith (F:=F) table data channel =
      (interactions (F:=F) table data).filter (·.channel = channel) := by
  simp only [interactionsWith, interactions, List.filter_flatMap]
  congr
  funext env
  rw [Operations.interactionValuesWith_eq_filter]

lemma channel_eq_of_mem_interactionsWith {i : Interaction F} :
    i ∈ interactionsWith (F:=F) table data channel → i.channel = channel := by
  intro h_mem
  simp only [interactionsWith, List.mem_flatMap] at h_mem
  rcases h_mem with ⟨env, h_env, hi⟩
  simp only [Operations.interactionValuesWith, List.mem_map] at hi
  rcases hi with ⟨i_abs, hi_abs, heq⟩
  rw [←heq]
  apply Operations.channel_eq_of_mem_interactionsWith hi_abs

lemma forall_interactions_iff (table : T) (data : ProverData F)
    (motive : Interaction F → Prop) :
    (∀ i ∈ interactions (F:=F) table data, motive i) ↔
    ∀ env ∈ envs (F:=F) table data, ∀ i ∈ (component (F:=F) table).operations.interactions,
      motive (i.eval env) := by
  simp only [interactions, Operations.interactionValues, List.mem_flatMap, List.mem_map,
    forall_exists_index, and_imp]
  constructor
  · intro h e h_e i hi
    exact h (i.eval e) e h_e i hi rfl
  · intro h i e h_e i' hi' h_eq
    rw [← h_eq]
    exact h e h_e i' hi'

lemma forall_interactionsWith_iff (table : T) (data : ProverData F) (channel : RawChannel F)
  (motive : Interaction F → Prop) :
    (∀ i ∈ interactionsWith (F:=F) table data channel, motive i) ↔
    ∀ env ∈ envs (F:=F) table data, ∀ i ∈ (component (F:=F) table).operations.interactions,
      (i.channel = channel → motive (i.eval env)) := by
  simp only [interactionsWith, List.mem_flatMap, List.mem_map,
    forall_exists_index, and_imp, circuit_norm]
  constructor
  · intro h e h_e i hi h_channel
    exact h (i.eval e) e h_e i hi h_channel rfl
  · intro h i e h_e i' hi' h_channel h_eq
    rw [← h_eq]
    exact h e h_e i' hi' h_channel

lemma interactionsWith_nil_of_channel_not_mem :
    channel ∉ (component (F:=F) table).circuit.channels →
      interactionsWith (F:=F) table data channel = [] := by
  contrapose!
  simp only [AbstractInteraction.eval_channel, interactionsWith_eq_filter, ne_eq, List.filter_eq_nil_iff,
    decide_eq_true_eq, forall_interactions_iff, not_forall, not_not, forall_exists_index]
  intro env env_mem i i_mem channel_eq
  symm at channel_eq; subst channel_eq
  simp only [Component.interactions_eq] at i_mem
  have h_subset := (component (F:=F) table).circuit.channels_subset
    (component (F:=F) table).rowInputVar (component (F:=F) table).rowOffset
  apply h_subset
  simp only [Operations.channels, List.mem_map]
  exists i

lemma guarantees_iff_forall (table : T) (data : ProverData F) :
    Guarantees (F:=F) table data ↔
    ∀ i ∈ interactions (F:=F) table data, i.Guarantees data := by
  simp only [Guarantees, circuit_norm, forall_interactions_iff]
  refine forall_congr' fun e => imp_congr_right fun h_e => ?_
  simp only [AbstractInteraction.Guarantees, Interaction.Guarantees, AbstractInteraction.eval,
    Interaction.msgVector, data_eq_of_mem (table:=table) h_e]

lemma channelGuarantees_iff_forall (table : T) (data : ProverData F)
    (channel : RawChannel F) :
    ChannelGuarantees (F:=F) table data channel ↔
    ∀ i ∈ interactionsWith (F:=F) table data channel, i.Guarantees data := by
  simp only [ChannelGuarantees, circuit_norm, forall_interactionsWith_iff]
  refine forall_congr' fun e => imp_congr_right fun h_e => ?_
  simp only [AbstractInteraction.Guarantees, Interaction.Guarantees, AbstractInteraction.eval,
    Interaction.msgVector, data_eq_of_mem (table:=table) h_e]

lemma guarantees_iff_channelGuarantees (table : T) (data : ProverData F) :
    Guarantees (F:=F) table data ↔
    ∀ channel ∈ channelsWithGuarantees (F:=F) table,
      ChannelGuarantees (F:=F) table data channel := by
  simp only [Guarantees, ChannelGuarantees, channelsWithGuarantees]
  simp only [Component.guarantees_iff, Component.channelGuarantees_iff, Component.rowOperations]
  simp only [GeneralFormalCircuit.guarantees_iff]
  constructor <;> simp_all

lemma channelGuarantees_of_requirements (table : T) (data : ProverData F)
    {channel : RawChannel F} :
    Guarantees (F:=F) table data → ChannelGuarantees (F:=F) table data channel := by
  simp_all [Guarantees, ChannelGuarantees, circuit_norm]

lemma requirements_iff_forall (table : T) (data : ProverData F) :
    Requirements (F:=F) table data ↔
    ∀ i ∈ interactions (F:=F) table data, i.Requirements data := by
  simp only [Requirements, circuit_norm, forall_interactions_iff]
  refine forall_congr' fun e => imp_congr_right fun h_e => ?_
  simp only [AbstractInteraction.Requirements, Interaction.Requirements, AbstractInteraction.eval,
    Interaction.msgVector, data_eq_of_mem (table:=table) h_e]

lemma channelRequirements_iff_forall (table : T) (data : ProverData F)
    (channel : RawChannel F) :
    ChannelRequirements (F:=F) table data channel ↔
    ∀ i ∈ interactionsWith (F:=F) table data channel, i.Requirements data := by
  simp only [ChannelRequirements, circuit_norm, forall_interactionsWith_iff]
  refine forall_congr' fun e => imp_congr_right fun h_e => ?_
  simp only [AbstractInteraction.Requirements, Interaction.Requirements, AbstractInteraction.eval,
    Interaction.msgVector, data_eq_of_mem (table:=table) h_e]

lemma requirements_iff_channelRequirements_of_constraints (table : T)
    (data : ProverData F) :
    Constraints (F:=F) table data →
    (Requirements (F:=F) table data ↔
    ∀ channel ∈ channelsWithRequirements (F:=F) table,
      ChannelRequirements (F:=F) table data channel) := by
  intro h_constraints
  simp only [Requirements, ChannelRequirements, channelsWithRequirements]
  simp only [Component.requirements_iff, Component.channelRequirements_iff, Component.rowOperations]
  simp_rw [Constraints, (component (F:=F) table).constraintsHold_iff] at h_constraints
  constructor
  · intro h_reqs channel h_channel env h_env
    specialize h_reqs env h_env
    rw [(component (F:=F) table).circuit.requirements_iff_of_constraints
      (h_constraints env h_env)] at h_reqs
    exact h_reqs channel h_channel
  · intro h_reqs env h_env
    rw [(component (F:=F) table).circuit.requirements_iff_of_constraints (h_constraints env h_env)]
    intro channel h_channel
    exact h_reqs channel h_channel env h_env

lemma channelRequirements_of_requirements (table : T) (data : ProverData F)
    {channel : RawChannel F} :
    Requirements (F:=F) table data → ChannelRequirements (F:=F) table data channel := by
  simp_all [Requirements, ChannelRequirements, circuit_norm]

lemma inChannelsOrRequirements_of_constraints (table : T) (data : ProverData F) :
    Constraints (F:=F) table data →
    InChannelsOrRequirements (F:=F) table data (channelsWithRequirements (F:=F) table) := by
  intro h_constraints
  simp only [InChannelsOrRequirements, channelsWithRequirements]
  intro env h_env
  exact (component (F:=F) table).inChannelsOrRequirements_of_constraints env
    (h_constraints env h_env)

lemma requirements_of_not_mem_of_constraints (table : T) (data : ProverData F)
    {channel : RawChannel F} :
    Constraints (F:=F) table data →
    channel ∉ channelsWithRequirements (F:=F) table →
      ChannelRequirements (F:=F) table data channel := by
  intro h_constraints h_not_mem
  have h_in_or_req := inChannelsOrRequirements_of_constraints (F:=F) table data h_constraints
  simp only [ChannelRequirements, InChannelsOrRequirements] at *
  intro env h_env
  specialize h_in_or_req env h_env
  apply Operations.requirements_of_not_mem _ (channelsWithRequirements (F:=F) table)
  assumption
  assumption

lemma inChannelsOrGuarantees (table : T) (data : ProverData F) :
    InChannelsOrGuarantees (F:=F) table data (channelsWithGuarantees (F:=F) table) := by
  simp [InChannelsOrGuarantees, channelsWithGuarantees, Component.inChannelsOrGuarantees]

lemma guarantees_of_not_mem (table : T) (data : ProverData F) {channel : RawChannel F} :
    channel ∉ channelsWithGuarantees (F:=F) table →
      ChannelGuarantees (F:=F) table data channel := by
  intro h_not_mem
  have h_in_or_guar := inChannelsOrGuarantees (F:=F) table data
  simp only [ChannelGuarantees, InChannelsOrGuarantees] at *
  intro env h_env
  specialize h_in_or_guar env h_env
  apply Operations.guarantees_of_not_mem _ (channelsWithGuarantees (F:=F) table)
  assumption
  assumption

/--
Circuit soundness, lifted to full table level.

The hypothesis is `CircuitAssumptions`, the *circuit's* assumptions at every environment. Each
table kind derives that from its ensemble-level `Assumptions` and `DataConsistency` via its own
`circuitAssumptions` lemma, which is the one place the row-vs-pair reading matters.
-/
theorem weakSoundness {table : T} {data : ProverData F}
    (assumptions : CircuitAssumptions (F:=F) table data) :
    Constraints (F:=F) table data → Guarantees (F:=F) table data →
    Spec (F:=F) table data ∧ Requirements (F:=F) table data := by
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
prove guarantees for. Like everything else here it is kind-agnostic: it never mentions how many
rows an environment spans.
-/
lemma requirements_of_partial_guarantees_of_constraints {table : T} {data : ProverData F}
  {finished : List (RawChannel F)} {unfinished : RawChannel F} :
  CircuitAssumptions (F:=F) table data →
  Constraints (F:=F) table data →
  channelsWithGuarantees (F:=F) table ⊆ unfinished :: finished →
  (∀ channel ∈ finished, ChannelGuarantees (F:=F) table data channel) →
    ∀ env ∈ envs (F:=F) table data,
      (component (F:=F) table).operations.ChannelGuarantees unfinished env →
      (component (F:=F) table).operations.ChannelRequirements unfinished env := by
  intro assumptions constraints subset finished_grts env h_env channel_grts
  replace finished_grts channel hc := finished_grts channel hc env h_env
  suffices (component (F:=F) table).operations.FullRequirements env by
    simp only [circuit_norm] at this ⊢
    intro i hi _
    exact this i hi
  suffices (component (F:=F) table).operations.FullGuarantees env from
    Component.weakSoundness (assumptions env h_env) (constraints env h_env) this |>.right
  simp only [Component.guarantees_iff, Component.rowOperations]
  rw [GeneralFormalCircuit.guarantees_iff]
  intro channel channel_mem
  show (component (F:=F) table).rowOperations.ChannelGuarantees channel env
  rw [← Component.channelGuarantees_iff]
  replace channel_mem := subset channel_mem
  simp at channel_mem
  rcases channel_mem with rfl | channel_mem
  · exact channel_grts
  · exact finished_grts _ channel_mem
end RowEnvs

end Air.Flat
