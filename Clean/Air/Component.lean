/-
Shared infrastructure for AIR components.

A `Component` is a row circuit plus the window it spans; everything about a concrete *trace* of
one -- the `Table`, its windows, and the trace-level predicates -- lives in
`Clean/Air/FlatComponent.lean`.
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

The window is recorded here, on the object the verifier commits to, rather than alongside the
trace. `window_size` ties it to the circuit's own cell footprint, which is what makes the reading
of an environment derivable from the component instead of a prover choice: committing a
transition component as a flat trace is not merely forbidden, it is unstateable.

For a transition component the layout is what makes both completeness and the spec work out:

    Input  = Row (width w)      cells [0, w)   -- row i,   prover-chosen via `witnessAny`
    main allocates w cells      cells [w, 2w)  -- row i+1, pinned by local-witness completeness

so the next row is the circuit's *output*, and `Spec input output` is the transition relation.
This layout is a law, not a convention: `input_eq_rowWidth` forces the input of any multi-row
window to be its entire first row.
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
  derivable from the component rather than a separate, reinterpretable annotation. -/
  window_size : circuit.size = windowRows * rowWidth := by simp
  windowRows_pos : 0 < windowRows := by simp
  /-- The circuit's input occupies the low cells of the window's *first* row.

  Not derivable from `window_size`: a component with `windowRows = 2`, `size Input = 10`,
  `localLength = 0` and `rowWidth = 5` satisfies the tiling yet has its input spill across both
  rows. The fixed-column and `ProverData` machinery are all stated about a single row's low
  indices (`FixedRowAt`, `DataRowAt`, `inputRow`), so that must be ruled out. -/
  input_le_rowWidth : size Input ≤ rowWidth := by simp [GeneralFormalCircuit.size_eq]
  /-- For a multi-row window, the input is the *entire* first row.

  `input_le_rowWidth` alone would admit a transition component with `size Input < rowWidth`: a
  circuit that witnesses scratch cells `[size Input, rowWidth)` in its *own* row before the
  next-row block. That shape is sound -- constraints only read committed trace cells -- but it
  gives those scratch cells of row `i` two witnessing owners: window `i` (as own-row scratch)
  and window `i - 1` (as part of its next-row block), so ensemble completeness and witness
  generation would have to prove the two witness generators agree on them. With equality,
  ownership is single: every cell of row `i + 1` is witnessed exactly once, by window `i`, and
  read back freely (`witnessAny`) as window `i + 1`'s input.

  Nothing is lost: intermediate columns of a transition step are expressed as extra columns of
  the row type, witnessed by the *previous* window like every other column -- the classic AIR
  layout in which the transition constraint relates all of row `i` to all of row `i + 1`.

  Flat components (`windowRows = 1`) are untouched: their row is the input followed by a
  witness suffix, and only `input_le_rowWidth` applies. -/
  input_eq_rowWidth : 1 < windowRows → size Input = rowWidth := by simp
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

end Air.Flat
