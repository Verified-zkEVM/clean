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
  /-- The input column of the component's multiplicity cell, found by validation. -/
  multiplicity : Option ℕ
  /-- The component's row operations, whose witness programs complete a row from its input. -/
  operations : List (FlatOperation F)
  /-- The component's channel interactions on a row. -/
  interactions : List (AbstractInteraction F)
  /-- The rows generated so far. -/
  rows : Array (GeneratedRow F) := #[]
  /-- The row created for each demanded message, in a demand component with a multiplicity cell. -/
  messageRows : Std.HashMap (Array F) ℕ := {}

def ComponentState.initial (component : Component F) (multiplicity : Option ℕ) :
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

def ComponentState.pushRow (state : ComponentState F) (row : GeneratedRow F) : ComponentState F :=
  { state with rows := state.rows.push row }

/-- Append a row created for the demanded `message`, which counts it. -/
def ComponentState.pushMessageRow (state : ComponentState F) (message : Array F)
    (row : GeneratedRow F) : ComponentState F :=
  { state with
    rows := state.rows.push row
    messageRows := state.messageRows.insert message state.rows.size }

/-- Replace the row at `index`. -/
def ComponentState.setRow (state : ComponentState F) (index : ℕ) (row : GeneratedRow F) :
    ComponentState F :=
  { state with rows := state.rows.set! index row }

/-- The inputs of a preallocated component's rows, from its input program, with multiplicity 0. -/
def initialInputs (state : ComponentState F) (hint : ProverHint F) : List (Array F) :=
  match state.component.generation with
  | .preallocated mode =>
      (List.range mode.height.toNat).map fun row =>
        evalInput (mode.input .idx) (rowEnvironment hint) row 0
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
