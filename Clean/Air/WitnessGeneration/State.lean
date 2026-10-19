module

public import Clean.Air.WitnessGeneration.Validation
public import Clean.Circuit.WitnessGeneration

@[expose] public section

/-!
# Witness generation state

The state that `Clean.Air.WitnessGeneration` evolves: the channel demand left to answer, and the
rows of every component generated so far.
-/

namespace Air.Flat.WitnessGeneration

variable {F : Type} [FiniteField F]

/-! ### Demand -/

/-- An unanswered channel message: its net multiplicity, pushes minus pulls, is nonzero. -/
structure Demand (F : Type) where
  channel : String
  message : Array F
  /-- The net multiplicity of the message, pushes minus pulls. -/
  multiplicity : F

namespace Demand

/-- Whether the message was pushed or pulled more often, and by how much. Multiplicities above half
the field order are read as negative. -/
def surplus (demand : Demand F) : Direction × ℕ :=
  if 2 * FiniteField.val demand.multiplicity ≤ FiniteField.size (F := F) then
    (.push, FiniteField.val demand.multiplicity)
  else
    (.pull, FiniteField.val (-demand.multiplicity))

def direction (demand : Demand F) : Direction := demand.surplus.1

def count (demand : Demand F) : ℕ := demand.surplus.2

/-- Add a multiplicity for a channel message, dropping the entry when it cancels to zero. -/
def add (channel : String) (message : Array F) (multiplicity : F) :
    List (Demand F) → List (Demand F)
  | [] => if multiplicity = 0 then [] else [{ channel, message, multiplicity }]
  | current :: rest =>
      if current.channel == channel && current.message == message then
        let total := current.multiplicity + multiplicity
        if total = 0 then rest else { current with multiplicity := total } :: rest
      else
        current :: add channel message multiplicity rest

def addInteractions (demands : List (Demand F)) (interactions : List (Interaction F)) :
    List (Demand F) :=
  interactions.foldl (fun demands interaction =>
    add interaction.channel.name interaction.msg interaction.mult demands) demands

def removeInteractions (demands : List (Demand F)) (interactions : List (Interaction F)) :
    List (Demand F) :=
  interactions.foldl (fun demands interaction =>
    add interaction.channel.name interaction.msg (-interaction.mult) demands) demands

end Demand

/-! ### Rows -/

/-- The demand that created a demand-generated row. A `byMessage` row is rebuilt from it when its
message is demanded again. -/
structure Origin (F : Type) where
  channel : String
  surplus : Direction
  message : Array F
  /-- The occurrences of the message the row answers. -/
  multiplicity : ℕ

structure GeneratedRow (F : Type) where
  /-- The row's input, from which its witness programs compute the rest of the row. -/
  input : Array F
  /-- The full row. -/
  values : Array F
  origin : Option (Origin F) := none

/-- One component's generation state. -/
structure ComponentState (F : Type) [FiniteField F] where
  component : Component F
  generation : Generation F
  /-- The counters of a preallocated component. -/
  counters : List Counter
  /-- The component's witness operations, which complete a row from its input. -/
  witgenOps : List (FlatOperation F)
  /-- The component's channel interactions on a row. -/
  interactions : List (AbstractInteraction F)
  /-- The rows generated so far. -/
  rows : List (GeneratedRow F) := []

def witnessOperationsOnly : List (FlatOperation F) → List (FlatOperation F)
  | [] => []
  | operation :: operations =>
      match operation with
      | .witness _ _ => operation :: witnessOperationsOnly operations
      | .assert _ | .lookup _ | .interact _ => witnessOperationsOnly operations

def ComponentState.initial (component : Component F) (generation : Generation F) :
    ComponentState F :=
  let operations := component.rowOperations
  {
    component
    generation
    counters := match generation with
      | .demand _ => []
      | .preallocated mode => (mode.counters component).toOption.getD []
    witgenOps := witnessOperationsOnly operations.toFlat
    interactions := operations.interactions
  }

def witgenStepWithData (data : ProverData F) (hint : ProverHint F)
    (acc : Array F) : FlatOperation F → Array F
  | .witness _ code =>
      let environment : ProverEnvironment F := {
        get index := acc[index]?.getD 0
        data
        hint
      }
      acc ++ (code.eval environment).toArray
  | .assert _ | .lookup _ | .interact _ => acc

def witgenWithData (data : ProverData F) (hint : ProverHint F)
    (ops : List (FlatOperation F)) (input : Array F) : Array F :=
  ops.foldl (witgenStepWithData data hint) input

/-- Complete a component row from its input with the component's witness programs. -/
def completeRow (state : ComponentState F) (input : Array F) (data : ProverData F)
    (hint : ProverHint F) (origin : Option (Origin F)) : GeneratedRow F :=
  { input, values := witgenWithData data hint state.witgenOps input, origin }

def rowInteractions (state : ComponentState F) (row : GeneratedRow F) (data : ProverData F) :
    List (Interaction F) :=
  let environment := Environment.fromArray row.values data
  state.interactions.map (·.eval environment)

/-- The prover data of the rows generated so far. -/
def generatedData (states : List (ComponentState F)) : ProverData F := fun name n =>
  match states.find? (·.component.circuit.name == name) with
  | some state => (state.rows.map (rowPrefix n ∘ (·.input))).toArray
  | none => #[]

/-- The inputs of a preallocated component's rows: per fixed row, its fixed values and the values of
the row program, with zeros inserted at the counter columns. -/
def initialInputs (state : ComponentState F) (hint : ProverHint F) : List (Array F) :=
  match state.component.fixedColumns, state.generation with
  | some fixed, .preallocated mode =>
      let counterColumns := (state.counters.map (·.column)).mergeSort
      (List.range fixed.height.toNat).map fun row =>
        let row := UInt64.ofNat row
        let input := fixed.values row ++ (toElements (mode.eval row hint)).toArray
        counterColumns.foldl (fun input column => input.insertIdx! column 0) input
  | _, _ => []

/-! ### Errors -/

/-- A failure of witness generation. -/
inductive GenerationError where
  | config (error : ConfigError)
  | unhandledImbalance (channels : List String)
  | noPreallocatedRow (component channel : String)
  | fuelExhausted
  | assembly (message : String)
deriving Repr

instance : ToString GenerationError where
  toString
    | .config error => toString error
    | .unhandledImbalance channels =>
        s!"unhandled channel imbalance on: {String.intercalate ", " channels}"
    | .noPreallocatedRow component channel =>
        s!"component '{component}' has no preallocated row for a message on channel '{channel}'"
    | .fuelExhausted => "ensemble witness generation exhausted its fuel"
    | .assembly message => message

end Air.Flat.WitnessGeneration
