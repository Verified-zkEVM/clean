module

public import Clean.Air.WitnessGeneration.Assembly

@[expose] public section

/-!
# Channel-driven witness generation

This file generates the witness of a flat AIR ensemble from its public input and the prover's
private input. Each component says how its rows come into existence in its `generation`.

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

How a component answers is its generation mode, see `Clean.Air.WitnessGeneration.Generation`:
- a `demand` component gets a new row for the message, or a higher multiplicity of an existing row,
- a `preallocated` component increments the counter of the row that carries the message.

Exactly one component may accept each message: the demand components on its channel whose guard
holds, and the preallocated components that have a row for it.

Finally, demand-generated tables are padded to a power-of-two height. Padding rows can interact,
so the generator balances and pads again until no table grows.

## Assumptions

TODO. The generator makes assumptions about the AIRs it handles, which come from our examples
rather than from the idea. None of them is fundamental:
- Counters only answer unmatched pulls, so `byMessage` requires `trigger := .pull`.
- A counter is the whole multiplicity of exactly one interaction.
- The input of a demand-generated row consists of message elements and constants; its other cells
  are computed by the witness programs.
- Witness programs only read prover data from cells of preallocated components that aren't
  counters, see `Clean.Air.WitnessGeneration.Validation`.
- All padding rows of a component have the same input.

Generation can also fail, because we hacked around non-termination with a `fuel` parameter that can
be exhausted, and because we don't yet prove that channels balance, so generation fails on demand
that no component handles.
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

/-- Whether a demand component answers the demand: it is on the mode's channel and triggers it, and
the guard holds. -/
def DemandMode.accepts {Input : TypeMap} [ProvableType Input] (mode : DemandMode F Input)
    (demand : Demand F) (data : ProverData F) (hint : ProverHint F) : Bool :=
  mode.channel.name == demand.channel && mode.trigger == demand.direction &&
    mode.guardCondition.eval { env := .fromArray demand.message data hint }

/-- The counters that answer `demand`: those on its channel, if the message was pulled more often
than pushed. -/
def countersFor (state : ComponentState F) (demand : Demand F) : List Counter :=
  if demand.direction == .pull then state.counters.filter (·.channel == demand.channel) else []

/-- The first row whose counted interaction carries the demanded message, with the counter and the
row's index. -/
def findCountedRow (state : ComponentState F) (demand : Demand F) (data : ProverData F) :
    Option (Counter × ℕ × GeneratedRow F) :=
  (countersFor state demand).findSome? fun counter =>
    state.rows.zipIdx.findSome? fun (row, index) =>
      state.interactions[counter.interaction]?.bind fun interaction =>
        if (interaction.eval (Environment.fromArray row.values data)).msg == demand.message then
          some (counter, index, row)
        else none

/-- Add the demanded count to the counter of a row, and complete the row again. -/
def incrementCounter (state : ComponentState F) (demand : Demand F) (data : ProverData F)
    (hint : ProverHint F) : Counter × ℕ × GeneratedRow F → Mutation F
  | (counter, index, row) =>
      let count := (row.input[counter.column]?.getD 0) + FiniteField.fromNat demand.count
      let updated := completeRow state (row.input.set! counter.column count) data hint
      { state := { state with rows := state.rows.set index updated }
        removedRows := [row]
        addedRows := [updated] }

/-- A new row answering the demanded message, whose counter, if any, starts at the demanded
count. -/
def DemandMode.newRow (state : ComponentState F) (mode : DemandMode F state.component.Input)
    (demand : Demand F) (data : ProverData F) (hint : ProverHint F) : GeneratedRow F :=
  let cells := (mode.input.map (·.eval demand.message)).toArray
  completeRow state (insertCounters state (FiniteField.fromNat demand.count) cells) data hint

/-- Answer demand with one new row per occurrence, or, with `byMessage`, by counting it in the row
for the message, which is created if there is none yet. -/
def DemandMode.answer (state : ComponentState F) (mode : DemandMode F state.component.Input)
    (demand : Demand F) (data : ProverData F) (hint : ProverHint F) : Mutation F :=
  let addRows (rows : List (GeneratedRow F)) : Mutation F :=
    { state := { state with rows := state.rows ++ rows }, addedRows := rows }
  match mode.aggregation with
  | .perOccurrence => addRows (List.replicate demand.count (mode.newRow state demand data hint))
  | .byMessage _ =>
      match findCountedRow state demand data with
      | some found => incrementCounter state demand data hint found
      | none => addRows [mode.newRow state demand data hint]

/-- The component's answer to the demand, if it accepts it. A preallocated component accepts the
messages it has a row for. -/
def ComponentState.answer? (state : ComponentState F) (demand : Demand F) (data : ProverData F)
    (hint : ProverHint F) : Option (Mutation F) :=
  match state.component.generation with
  | .demand mode =>
      if mode.accepts demand data hint then some (mode.answer state demand data hint) else none
  | .preallocated _ =>
      (findCountedRow state demand data).map (incrementCounter state demand data hint)

/-- The answer to the first demand that some component accepts, with that component's index. Fails
if several components accept it. -/
def findAnswer (states : List (ComponentState F)) (data : ProverData F) (hint : ProverHint F) :
    List (Demand F) → Except GenerationError (Option (ℕ × Mutation F))
  | [] => pure none
  | demand :: demands =>
      let answers := states.zipIdx.filterMap fun (state, index) =>
        (state.answer? demand data hint).map (index, ·)
      match answers with
      | [] => findAnswer states data hint demands
      | [answer] => pure (some answer)
      | _ => throw (.ambiguousDemand demand.channel
          (answers.map fun (_, mutation) => mutation.state.component.circuit.name))

/-- Apply the answer of the component at `index`, and update the tally with the changed rows. -/
def applyAnswer (states : List (ComponentState F)) (demands : List (Demand F)) (index : ℕ)
    (mutation : Mutation F) (data : ProverData F) :
    List (ComponentState F) × List (Demand F) :=
  let removed := mutation.removedRows.flatMap (rowInteractions mutation.state · data)
  let added := mutation.addedRows.flatMap (rowInteractions mutation.state · data)
  (states.set index mutation.state,
    Demand.addInteractions (Demand.removeInteractions demands removed) added)

/-! ### The loop -/

/-- Answer demand until the tally is empty. -/
def generateLoop (data : ProverData F) (hint : ProverHint F) :
    ℕ → List (ComponentState F) → List (Demand F) →
      Except GenerationError (List (ComponentState F))
  | 0, _, _ => throw .fuelExhausted
  | fuel + 1, states, demands =>
      if demands.isEmpty then pure states else do
      match ← findAnswer states data hint demands with
      | none => throw (.unhandledImbalance (demands.map (·.channel)))
      | some (index, mutation) =>
          let (states, demands) := applyAnswer states demands index mutation data
          generateLoop data hint fuel states demands

/-- The padded height of a demand-generated table. Preallocated tables are never padded. -/
def ComponentState.targetHeight (state : ComponentState F) : ℕ :=
  match state.component.generation with
  | .demand _ => nextPowerOfTwo state.rows.length
  | .preallocated _ => state.rows.length

/-- Pad every demand-generated table to its target height; returns the padded states and the
interactions of the padding rows. -/
def padTables (data : ProverData F) (hint : ProverHint F) (states : List (ComponentState F)) :
    List (ComponentState F) × List (Interaction F) :=
  let padded := states.map fun state =>
    match state.component.generation with
    | .preallocated _ => (state, [])
    | .demand mode =>
        let count := state.targetHeight - state.rows.length
        let rows := List.replicate count (completeRow state mode.padding data hint)
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

/-- Generate an ensemble witness from an ensemble with validated generation, the public input and
the prover's private input. -/
def generateValid {ens : Ensemble F PublicIO} (valid : ValidGeneration ens) (fuel : ℕ)
    (publicInput : PublicIO F) (proverInput : ens.ProverInput F) :
    Except GenerationError (EnsembleWitness ens) := do
  let hint := ens.hint proverInput
  -- preallocate rows, and complete them with the prover data of all preallocated inputs
  let initial := (ens.tables.zip valid.counters).map fun (component, counters) =>
    ComponentState.initial component counters
  let initial := initial.map fun state =>
    { state with rows := (initialInputs state hint).map fun input => { input, values := input } }
  let data := generatedData initial
  let initial := initial.map fun state =>
    { state with rows := state.rows.map fun row => completeRow state row.input data hint }
  -- start the chain reaction from the verifier's and the preallocated rows' interactions
  let verifier := ens.verifierOperations.interactionValues (.fromInput publicInput data)
  let rows := initial.flatMap fun state => state.rows.flatMap (rowInteractions state · data)
  let demands := Demand.addInteractions [] (verifier ++ rows)
  let generated ← generateLoop data hint fuel initial demands
  let padded ← padAndBalance data hint fuel fuel generated
  let assembled ← assembleTables ens.tables padded
  return {
    tables := withDerivedData assembled.tables
    publicInput
    same_length := by simp [withDerivedData, assembled.same_length]
    same_circuits := by simp [withDerivedData, assembled.same_circuits]
    same_data := withDerivedData_data assembled.tables
  }

/-- Validate the generation of an ensemble, then generate a witness from the public input and the
prover's private input. `fuel` bounds the number of generation steps. -/
def generate (ens : Ensemble F PublicIO) (fuel : ℕ) (publicInput : PublicIO F)
    (proverInput : ens.ProverInput F) : Except GenerationError (EnsembleWitness ens) :=
  match validateGeneration ens with
  | .error error => .error (.validation error)
  | .ok valid => generateValid valid fuel publicInput proverInput

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
