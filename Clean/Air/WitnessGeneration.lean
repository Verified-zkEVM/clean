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
creates rows in chips like an addition chip, or increments multiplicities in a memory or a lookup
table. The reaction stops when a row pushes the final state, which the verifier pulls.

How a component answers is its generation mode, see `Clean.Air.WitnessGeneration.Generation`:
- a `demand` component gets a new row for the message, or changes the multiplicity cell of an
  existing row,
- a `preallocated` component changes the multiplicity cell of the row that carries the message.

Exactly one component may accept each message: the demand components on its channel whose guard
holds, and the preallocated components that have a row for it.

Finally, demand-generated tables are padded to a power-of-two height. Padding rows can interact,
so the generator balances and pads again until no table grows.

## Assumptions

TODO. The generator makes assumptions about the AIRs it handles, which come from our examples
rather than from the idea. None of them is fundamental:
- A multiplicity cell is the whole multiplicity of exactly one interaction, on the component's
  channel.
- Witness programs only read prover data from cells of preallocated components that aren't
  multiplicity cells, see `Clean.Air.WitnessGeneration.Validation`.
- All padding rows of a component have the same input.

Generation can also fail, because we hacked around non-termination with a `fuel` parameter that can
be exhausted, and because we don't yet prove that channels balance, so generation fails on demand
that no component handles.
-/

namespace Air.Flat.WitnessGeneration

variable {F : Type} [FiniteField F]
variable {PublicIO : TypeMap} [ProvableType PublicIO]

/-! ### Answering demand -/

/-- The rows a component adds or replaces to answer a demand. -/
inductive Change (F : Type) where
  | add (rows : List (GeneratedRow F))
  /-- The row at `index` is updated from `old` to `new`. -/
  | update (index : ℕ) (old new : GeneratedRow F)

/-- The rows that leave the tally with their interactions. -/
def Change.removedRows : Change F → List (GeneratedRow F)
  | .add _ => []
  | .update _ old _ => [old]

/-- The rows that enter the tally with their interactions. -/
def Change.addedRows : Change F → List (GeneratedRow F)
  | .add rows => rows
  | .update _ _ new => [new]

def ComponentState.applyChange (state : ComponentState F) (data : ProverData F) :
    Change F → ComponentState F
  | .add rows => rows.foldl (·.pushRow data) state
  | .update index _ new => state.setRow index new

/-- Whether a demand component answers the demand: it is on the mode's channel and triggers it, and
the guard holds. -/
def DemandMode.accepts {Input : TypeMap} [ProvableType Input] (mode : DemandMode F Input)
    (demand : Demand F) (data : ProverData F) (hint : ProverHint F) : Bool :=
  mode.channel.name == demand.channel && mode.trigger == demand.direction &&
    mode.guardCondition.eval { env := .fromArray demand.message data hint }

/-- Whether a preallocated component answers the demand: it is on the mode's channel and triggers
it. Answering also needs a row for the message. -/
def PreallocatedMode.accepts {Input : TypeMap} [ProvableType Input]
    (mode : PreallocatedMode F Input) (demand : Demand F) : Bool :=
  mode.channel.name == demand.channel && mode.trigger == demand.direction

/-- The row that counts the demanded message, with the multiplicity cell and the row's index. -/
def findCountedRow (state : ComponentState F) (demand : Demand F) :
    Option (MultiplicityColumn × ℕ × GeneratedRow F) :=
  state.multiplicity.bind fun multiplicity =>
    state.countedRows[demand.message]?.bind fun index =>
      state.rows[index]?.map fun row => (multiplicity, index, row)

/-- Cancel the demand in the multiplicity cell of a row, and complete the row again. -/
def incrementMultiplicity (state : ComponentState F) (demand : Demand F) (data : ProverData F)
    (hint : ProverHint F) : MultiplicityColumn × ℕ × GeneratedRow F → Change F
  | (multiplicity, index, row) =>
      let count := multiplicity.cancel (row.input[multiplicity.column]?.getD 0) demand.multiplicity
      .update index row (completeRow state (row.input.set! multiplicity.column count) data hint)

/-- A new row answering the demanded message, whose multiplicity cell, if any, cancels the
demand. -/
def DemandMode.newRow (state : ComponentState F) (mode : DemandMode F state.component.Input)
    (demand : Demand F) (data : ProverData F) (hint : ProverHint F) : GeneratedRow F :=
  let env := ProverEnvironment.fromArray demand.message data hint
  let count := (state.multiplicity.map (·.cancel 0 demand.multiplicity)).getD 0
  let input := evalInput (mode.input (varFromOffset mode.Message 0)) env 0 count
  completeRow state input data hint

/-- Answer demand with one new row per occurrence, or, with a multiplicity cell, by counting it in
the row for the message, which is created if there is none yet. -/
def DemandMode.answer (state : ComponentState F) (mode : DemandMode F state.component.Input)
    (demand : Demand F) (data : ProverData F) (hint : ProverHint F) : Change F :=
  match state.multiplicity with
  | none => .add (List.replicate demand.count (mode.newRow state demand data hint))
  | some _ =>
      match findCountedRow state demand with
      | some found => incrementMultiplicity state demand data hint found
      | none => .add [mode.newRow state demand data hint]

/-- The component's answer to the demand, if it accepts it. A preallocated component accepts the
messages it has a row for. -/
def ComponentState.answer? (state : ComponentState F) (demand : Demand F) (data : ProverData F)
    (hint : ProverHint F) : Option (Change F) :=
  match state.component.generation with
  | .demand mode =>
      if mode.accepts demand data hint then some (mode.answer state demand data hint) else none
  | .preallocated mode =>
      if mode.accepts demand then
        (findCountedRow state demand).map (incrementMultiplicity state demand data hint)
      else none

/-- The answers of all components that accept the demand, with their indices and names. -/
def answers (states : Array (ComponentState F)) (demand : Demand F) (data : ProverData F)
    (hint : ProverHint F) : List (ℕ × String × Change F) :=
  states.toList.zipIdx.filterMap fun (state, index) =>
    (state.answer? demand data hint).map (index, state.component.circuit.name, ·)

/-- The answer to the first demand that some component accepts, with that component's index. Fails
if several components accept it, or if no component accepts any demand. -/
def findAnswer (states : Array (ComponentState F)) (data : ProverData F) (hint : ProverHint F)
    (tally : Tally F) : Except GenerationError (ℕ × Change F) := do
  for (_, demand) in tally.byPosition do
    match answers states demand data hint with
    | [] => pure ()
    | [(index, _, change)] => return (index, change)
    | answers => throw (.ambiguousDemand demand.channel (answers.map (·.2.1)))
  throw (.unhandledImbalance (tally.demands.map (·.channel)))

/-- Apply the change of the component at `index`, and update the tally with the changed rows. -/
def applyAnswer (states : Array (ComponentState F)) (tally : Tally F) (index : ℕ)
    (change : Change F) (data : ProverData F) : Array (ComponentState F) × Tally F :=
  let (removed, added) := match states[index]? with
    | some state =>
        (change.removedRows.flatMap (rowInteractions state · data),
          change.addedRows.flatMap (rowInteractions state · data))
    | none => ([], [])
  (states.modify index (·.applyChange data change),
    (tally.removeInteractions removed).addInteractions added)

/-! ### The loop -/

/-- Answer demand until the tally is empty. -/
def generateLoop (data : ProverData F) (hint : ProverHint F) :
    ℕ → Array (ComponentState F) → Tally F → Except GenerationError (Array (ComponentState F))
  | 0, _, _ => throw .fuelExhausted
  | fuel + 1, states, tally =>
      if tally.isEmpty then pure states else
      match findAnswer states data hint tally with
      | .error error => throw error
      | .ok (index, change) =>
          let (states, tally) := applyAnswer states tally index change data
          generateLoop data hint fuel states tally

/-- The padded height of a demand-generated table. Preallocated tables are never padded. -/
def ComponentState.targetHeight (state : ComponentState F) : ℕ :=
  match state.component.generation with
  | .demand _ => nextPowerOfTwo state.rows.size
  | .preallocated _ => state.rows.size

/-- Pad a demand-generated table to its target height; returns the padded state and the
interactions of the padding rows. -/
def ComponentState.pad (state : ComponentState F) (data : ProverData F) (hint : ProverHint F) :
    ComponentState F × List (Interaction F) :=
  match state.component.generation with
  | .preallocated _ => (state, [])
  | .demand mode =>
      let row := completeRow state (toElements mode.padding).toArray data hint
      let rows := List.replicate (state.targetHeight - state.rows.size) row
      (rows.foldl (·.pushRow data) state, rows.flatMap (rowInteractions state · data))

/-- Pad, then answer the demand of the padding rows, until no table grows. -/
def padAndBalance (data : ProverData F) (hint : ProverHint F) (fuel : ℕ) :
    ℕ → Array (ComponentState F) → Except GenerationError (Array (ComponentState F))
  | 0, _ => throw .fuelExhausted
  | rounds + 1, states => do
      let padded := states.map (·.pad data hint)
      let tally := Tally.empty.addInteractions (padded.toList.flatMap (·.2))
      let states ← generateLoop data hint fuel (padded.map (·.1)) tally
      if states.all fun state => state.rows.size == state.targetHeight then return states
      padAndBalance data hint fuel rounds states

/-! ### Generating a witness -/

/-- The prover data of the preallocated rows' inputs, under their components' names. -/
def initialData (states : Array (ComponentState F)) (inputs : Array (List (Array F))) :
    List (String × PreparedRows F) :=
  (states.zip inputs).toList.map fun (state, inputs) =>
    (state.component.circuit.name, .ofRows inputs.toArray (size state.component.Input))

/-- Generate an ensemble witness from an ensemble with validated generation, the public input and
the prover's private input. -/
def generateValid {ens : Ensemble F PublicIO} (valid : ValidGeneration ens) (fuel : ℕ)
    (publicInput : PublicIO F) (proverInput : ens.ProverInput F) :
    Except GenerationError (EnsembleWitness ens) := do
  let hint : ProverHint F :=
    readNamedRows (prepareHint ens.hintTables (toElements proverInput).toArray)
  -- preallocate rows, and complete them with the prover data of all preallocated inputs
  let states := (ens.tables.zip valid.multiplicities).toArray.map fun (component, multiplicity) =>
    ComponentState.initial component multiplicity
  let inputs := states.map (initialInputs · hint)
  let data : ProverData F := readNamedRows (initialData states inputs)
  let states := (states.zip inputs).map fun (state, inputs) =>
    inputs.foldl (fun state input => state.pushRow data (completeRow state input data hint)) state
  -- start the chain reaction from the verifier's and the preallocated rows' interactions
  let verifier := ens.verifierOperations.interactionValues (.fromInput publicInput data)
  let rows := states.toList.flatMap fun state =>
    state.rows.toList.flatMap (rowInteractions state · data)
  let tally := Tally.empty.addInteractions (verifier ++ rows)
  let generated ← generateLoop data hint fuel states tally
  let padded ← padAndBalance data hint fuel fuel generated
  let assembled ← assembleTables ens.tables padded.toList
  have hunique : (assembled.tables.map fun table => table.component.circuit.name).Nodup := by
    simpa [← assembled.map_component, Function.comp_def] using ens.unique_names
  return {
    tables := withDerivedData assembled.tables hunique
    publicInput
    same_length := by simp [withDerivedData, assembled.same_length]
    same_circuits := by simp [withDerivedData, assembled.same_circuits]
    same_data := withDerivedData_data assembled.tables hunique
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
  (Tally.empty.addInteractions witness.interactions).isEmpty

/-- Whether the interactions with every channel pass a balance check, in a field of characteristic
`char`. -/
def balanceHolds {ensemble : Ensemble F PublicIO} (balance : Balance F) (char : ℕ)
    (witness : EnsembleWitness ensemble) : Bool :=
  ensemble.channels.all fun channel =>
    balance.isBalanced char (witness.interactions.filter (·.channel.name == channel.name))

end Air.Flat.WitnessGeneration
