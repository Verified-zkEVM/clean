module

public import Clean.Air.WitnessGeneration.PreparedRows
public import Clean.Air.WitnessGeneration.Tally
public import Clean.Air.WitnessGeneration.Validation
public import Clean.Circuit.WitnessGeneration

@[expose] public section

/-!
# Witness generation state

The state that `Clean.Air.WitnessGeneration` evolves: the tally of channel demand left to answer,
see `Clean.Air.WitnessGeneration.Tally`, and the rows of every component generated so far.
-/

namespace Air.Flat.WitnessGeneration

variable {F : Type} [FiniteField F]

/-! ### Rows -/

structure GeneratedRow (F : Type) where
  /-- The row's input, from which its witness programs compute the rest of the row. -/
  input : Array F
  /-- The full row. -/
  values : Array F

/-- One component's generation state. -/
structure ComponentState (F : Type) [FiniteField F] where
  component : Component F
  /-- The component's multiplicity cell, resolved by validation. -/
  multiplicity : Option MultiplicityColumn
  /-- The component's row operations, whose witness programs complete a row from its input. -/
  operations : List (FlatOperation F)
  /-- The component's channel interactions on a row. -/
  interactions : List (AbstractInteraction F)
  /-- The rows generated so far. -/
  rows : Array (GeneratedRow F) := #[]
  /-- The index of the first row whose counted interaction carries each message, see
  `countedMessage`. -/
  countedRows : Std.HashMap (Array F) ℕ := {}

def ComponentState.initial (component : Component F) (multiplicity : Option MultiplicityColumn) :
    ComponentState F :=
  let operations := component.rowOperations
  {
    component
    multiplicity
    operations := operations.toFlat
    interactions := operations.interactions
  }

/-- Complete a component row from its input with the component's witness programs. -/
def completeRow (state : ComponentState F) (input : Array F) (data : ProverData F)
    (hint : ProverHint F) : GeneratedRow F :=
  { input, values := FlatOperation.witgen data hint state.operations input }

def rowInteractions (state : ComponentState F) (row : GeneratedRow F) (data : ProverData F) :
    List (Interaction F) :=
  let environment := Environment.fromArray row.values data
  state.interactions.map (·.eval environment)

/-- The message of a row's counted interaction, if the component has a multiplicity cell. -/
def ComponentState.countedMessage (state : ComponentState F) (row : GeneratedRow F)
    (data : ProverData F) : Option (Array F) :=
  state.multiplicity.bind fun multiplicity =>
    state.interactions[multiplicity.interaction]?.map fun interaction =>
      (interaction.eval (Environment.fromArray row.values data)).msg

/-- Append a row, which counts its message if no earlier row does. -/
def ComponentState.pushRow (state : ComponentState F) (data : ProverData F)
    (row : GeneratedRow F) : ComponentState F :=
  let message := state.countedMessage row data
  let index := state.rows.size
  { state with
    rows := state.rows.push row
    countedRows := match message with
      | some message => state.countedRows.insertIfNew message index
      | none => state.countedRows }

/-- Replace the row at `index`, which must count the same message. -/
def ComponentState.setRow (state : ComponentState F) (index : ℕ) (row : GeneratedRow F) :
    ComponentState F :=
  { state with rows := state.rows.set! index row }

/-- The inputs of a preallocated or standalone component's rows, from its input program, with
multiplicity 0. -/
def initialInputs (state : ComponentState F) (hint : ProverHint F) : List (Array F) :=
  match state.component.generation with
  | .preallocated { height, input, .. } | .standalone { height, input } =>
      (List.range height.toNat).map fun row =>
        evalInput (input .idx) (rowEnvironment hint) row 0
  | .demand _ => []

/-! ### Errors -/

/-- A failure of witness generation. -/
inductive GenerationError where
  | validation (error : ValidationError)
  | unhandledImbalance (channels : List String)
  | ambiguousDemand (channel : String) (components : List String)
  | fuelExhausted
  | assembly (message : String)
deriving Repr

instance : ToString GenerationError where
  toString
    | .validation error => toString error
    | .unhandledImbalance channels =>
        s!"unhandled channel imbalance on: {String.intercalate ", " channels}"
    | .ambiguousDemand channel components =>
        s!"components {String.intercalate ", " components} all accept a message on channel \
          '{channel}'"
    | .fuelExhausted => "ensemble witness generation exhausted its fuel"
    | .assembly message => message

end Air.Flat.WitnessGeneration
