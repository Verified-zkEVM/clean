module

public import Clean.Air.WitnessGeneration.Assembly

@[expose] public section

/-!
# Channel-driven witness generation

This file generates the witness of a flat AIR ensemble from its public input, the prover's private
input, and a `Config` that says how each component's rows come into existence.

## The chain reaction

Channel balance means that, for every channel message, pushes and pulls cancel out. The generator
keeps a tally of the messages that don't cancel yet: their *demand*. It starts with the
interactions of the verifier and of the preallocated rows, and then repeats one step: pick an
unanswered message, and let the component that handles it add or update a row that answers it.
The new row brings interactions of its own, which may create new demand, and so on, until the
tally is empty.

For example, the verifier of a VM pushes the initial state and pulls the final state. The pushed
initial state has no pull, so the VM gets a row that pulls it and pushes the next state. That state
is again unanswered, so the VM gets another row. Every row may also pull from other channels, which
creates rows in chips like an addition chip, or increments counters in a memory or a lookup table.
The reaction stops when a row pushes the final state, which the verifier pulls.

How a component answers is its generation mode, see `Clean.Air.WitnessGeneration.Config`:
- a `demand` component gets a new row for the message, or a higher multiplicity of an existing row,
- a `preallocated` component increments the counter of the row that carries the message.

Finally, demand-generated tables are padded to a power-of-two height. Padding rows can interact,
so the generator balances and pads again until no table grows.

## Limitations

TODO. Generation can still fail, because we hacked around non-termination with a `fuel` parameter
that can be exhausted, and because we don't yet prove that channels balance, so generation fails on
demand that no component handles.
-/

namespace Air.Flat.WitnessGeneration

variable {F : Type} [FiniteField F]
variable {PublicIO : TypeMap} [ProvableType PublicIO]

/-! ### Answering demand -/

/-- A component's changed rows: they leave the tally with their old interactions and enter it with
their new ones. -/
structure Mutation (F : Type) [FiniteField F] where
  state : ComponentState F
  removedRows : List (GeneratedRow F) := []
  addedRows : List (GeneratedRow F) := []

def DemandMode.handles (mode : DemandMode F) (demand : Demand F) : Bool :=
  mode.channel.name == demand.channel && mode.surplus == demand.direction

/-- A demand-generated row answering `multiplicity` occurrences of the demanded message. -/
def DemandMode.newRow (mode : DemandMode F) (state : ComponentState F) (demand : Demand F)
    (multiplicity : ℕ) (data : ProverData F) (hint : ProverHint F) : GeneratedRow F :=
  let origin : Origin F := {
    channel := mode.channel.name
    surplus := mode.surplus
    message := demand.message
    multiplicity
  }
  let input := (mode.input.map (·.eval demand.message multiplicity)).toArray
  completeRow state input data hint (some origin)

/-- Answer demand with new rows, or with a higher multiplicity of the row a `byMessage` component
already has for the message. -/
def DemandMode.answer (mode : DemandMode F) (state : ComponentState F) (demand : Demand F)
    (data : ProverData F) (hint : ProverHint F) : Mutation F :=
  match mode.aggregation with
  | .perOccurrence =>
      let rows := List.replicate demand.count (mode.newRow state demand 1 data hint)
      { state := { state with rows := state.rows ++ rows }, addedRows := rows }
  | .byMessage =>
      let existing := state.rows.zipIdx.findSome? fun (row, index) =>
        row.origin.bind fun origin =>
          if origin.channel == mode.channel.name && origin.surplus == mode.surplus &&
            origin.message == demand.message then some (row, origin, index) else none
      match existing with
      | none =>
          let row := mode.newRow state demand demand.count data hint
          { state := { state with rows := state.rows ++ [row] }, addedRows := [row] }
      | some (row, origin, index) =>
          let updated := mode.newRow state demand (origin.multiplicity + demand.count) data hint
          { state := { state with rows := state.rows.set index updated }
            removedRows := [row]
            addedRows := [updated] }

/-- The counters of a preallocated component that answer `demand`: counters only answer pulls. -/
def countersFor (state : ComponentState F) (demand : Demand F) : List Counter :=
  if demand.direction == .pull then
    state.counters.filter fun counter =>
      state.interactions[counter.interaction]?.any (·.channel.name == demand.channel)
  else []

/-- Answer demand by incrementing the counter of the first row whose counted interaction carries
the demanded message. Fails if there is no such row, for example when a memory read is out of
bounds. -/
def PreallocatedMode.answer (state : ComponentState F) (demand : Demand F) (data : ProverData F)
    (hint : ProverHint F) : Option (Mutation F) :=
  let found := (countersFor state demand).findSome? fun counter =>
    state.rows.zipIdx.findSome? fun (row, index) =>
      state.interactions[counter.interaction]?.bind fun interaction =>
        if (interaction.eval (Environment.fromArray row.values data)).msg == demand.message then
          some (counter, index, row)
        else none
  -- `Mutation` lives in a higher universe, so this matches instead of binding with `←`
  match found with
  | none => none
  | some (counter, index, row) =>
      let count := (row.input[counter.column]?.getD 0) + FiniteField.fromNat demand.count
      let updated := completeRow state (row.input.set! counter.column count) data hint none
      some {
        state := { state with rows := state.rows.set index updated }
        removedRows := [row]
        addedRows := [updated]
      }

def ComponentState.handles (state : ComponentState F) (demand : Demand F) : Bool :=
  match state.generation with
  | .demand mode => mode.handles demand
  | .preallocated _ => !(countersFor state demand).isEmpty

/-- The first demand that some component handles, with that component's index. Validation ensures
at most one component handles each channel and surplus. -/
def findHandler (states : List (ComponentState F)) :
    List (Demand F) → Option (Demand F × ℕ)
  | [] => none
  | demand :: demands =>
      match states.findIdx? (·.handles demand) with
      | some index => some (demand, index)
      | none => findHandler states demands

/-- Let the component at `index` answer `demand`, and update the tally with the changed rows. -/
def answer (states : List (ComponentState F)) (demands : List (Demand F)) (demand : Demand F)
    (index : ℕ) (data : ProverData F) (hint : ProverHint F) :
    Except GenerationError (List (ComponentState F) × List (Demand F)) := do
  let some state := states[index]? | return (states, demands)
  let mutation ← match state.generation with
    | .demand mode => pure (mode.answer state demand data hint)
    | .preallocated _ =>
        match PreallocatedMode.answer state demand data hint with
        | some mutation => pure mutation
        | none => throw (.noPreallocatedRow state.component.circuit.name demand.channel)
  let removed := mutation.removedRows.flatMap (rowInteractions state · data)
  let added := mutation.addedRows.flatMap (rowInteractions state · data)
  return (states.set index mutation.state,
    Demand.addInteractions (Demand.removeInteractions demands removed) added)

/-! ### The loop -/

/-- Answer demand until the tally is empty. -/
def generateLoop (data : ProverData F) (hint : ProverHint F) :
    ℕ → List (ComponentState F) → List (Demand F) →
      Except GenerationError (List (ComponentState F))
  | 0, _, _ => throw .fuelExhausted
  | fuel + 1, states, demands =>
      if demands.isEmpty then pure states else
      match findHandler states demands with
      | none => throw (.unhandledImbalance (demands.map (·.channel)))
      | some (demand, index) => do
          let (states, demands) ← answer states demands demand index data hint
          generateLoop data hint fuel states demands

/-- The padded height of a demand-generated table. Preallocated tables are never padded. -/
def ComponentState.targetHeight (state : ComponentState F) : ℕ :=
  match state.generation with
  | .demand mode => mode.padding.targetHeight state.rows.length
  | .preallocated _ => state.rows.length

/-- Pad every demand-generated table to its target height; returns the padded states and the
interactions of the padding rows. -/
def padTables (data : ProverData F) (hint : ProverHint F) (states : List (ComponentState F)) :
    List (ComponentState F) × List (Interaction F) :=
  let padded := states.map fun state =>
    match state.generation with
    | .preallocated _ => (state, [])
    | .demand mode =>
        let count := state.targetHeight - state.rows.length
        let rows := List.replicate count (completeRow state mode.padding.input data hint none)
        ({ state with rows := state.rows ++ rows }, rows.flatMap (rowInteractions state · data))
  (padded.map (·.1), padded.flatMap (·.2))

/-- Pad, then answer the demand of the padding rows, until no table grows. -/
def padAndBalance (data : ProverData F) (hint : ProverHint F) (fuel : ℕ) :
    ℕ → List (ComponentState F) → Except GenerationError (List (ComponentState F))
  | 0, _ => throw .fuelExhausted
  | rounds + 1, states => do
      let (states, added) := padTables data hint states
      let states ← generateLoop data hint fuel states (Demand.addInteractions [] added)
      if states.all fun state => state.rows.length == state.targetHeight then return states
      padAndBalance data hint fuel rounds states

/-! ### Generating a witness -/

/-- Generate an ensemble witness from a validated config. -/
def generateValid {ensemble : Ensemble F PublicIO} (config : ValidConfig ensemble)
    (publicInput : PublicIO F) (hint : ProverHint F) :
    Except GenerationError (EnsembleWitness ensemble) := do
  -- preallocate rows, and complete them with the prover data of all preallocated inputs
  let initial := (ensemble.tables.zip config.generations).map fun (component, generation) =>
    ComponentState.initial component generation
  let initial := initial.map fun state =>
    { state with rows := (initialInputs state hint).map fun input => { input, values := input } }
  let data := generatedData initial
  let initial := initial.map fun state =>
    { state with rows := state.rows.map fun row => completeRow state row.input data hint none }
  -- start the chain reaction from the verifier's and the preallocated rows' interactions
  let verifier := ensemble.verifierOperations.interactionValues (.fromInput publicInput data)
  let rows := initial.flatMap fun state => state.rows.flatMap (rowInteractions state · data)
  let demands := Demand.addInteractions [] (verifier ++ rows)
  let generated ← generateLoop data hint config.fuel initial demands
  let padded ← padAndBalance data hint config.fuel config.fuel generated
  let assembled ← assembleTables ensemble.tables padded
  return {
    tables := withDerivedData assembled.tables
    publicInput
    same_length := by simp [withDerivedData, assembled.same_length]
    same_circuits := by simp [withDerivedData, assembled.same_circuits]
    same_data := withDerivedData_data assembled.tables
  }

/-- Validate a config, then generate an ensemble witness from the public input and the prover's
private input. -/
def generate (ens : FormalEnsemble F PublicIO) (config : Config F) (publicInput : PublicIO F)
    (proverInput : ens.ProverInput F) : Except GenerationError (EnsembleWitness ens.ensemble) :=
  match config.validate ens.ensemble with
  | .error error => .error (.config error)
  | .ok config => generateValid config publicInput (ens.hint proverInput)

/-! ### Checking a witness -/

/-- Whether all constraints of a witness hold. Fails on tables with lookups. -/
def constraintsHold {ensemble : Ensemble F PublicIO} (witness : EnsembleWitness ensemble) : Bool :=
  witness.tables.all fun table =>
    table.table.all fun row =>
      table.component.operations.lookups.isEmpty &&
      table.component.operations.constraints.all fun constraint =>
        constraint.eval (Environment.fromArray row witness.data) == 0

/-- Whether all channels of a witness balance. -/
def channelsBalanced {ensemble : Ensemble F PublicIO} (witness : EnsembleWitness ensemble) : Bool :=
  (Demand.addInteractions [] witness.interactions).isEmpty

end Air.Flat.WitnessGeneration
