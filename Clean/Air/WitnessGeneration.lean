module

public import Clean.Air.FlatEnsemble
public import Clean.Circuit.WitnessGeneration

@[expose] public section

/-!
# Channel-driven ensemble witness generation

This file contains the executable reference builder for flat AIR ensemble witnesses. Soundness
does not depend on this builder; generated rows still have to satisfy the component constraints
and the global channel-balance relation.

`Config.validate` checks generation metadata against an ensemble once. A `ValidConfig` carries
that check, and generation from it cannot hit structural errors. Its remaining failures are
semantic: channel imbalance that no component handles, a message no preallocated row matches,
and reaching as many interactions as the field has elements, beyond which channels cannot
balance.

The builder maintains the channel imbalance incrementally, as the net field multiplicity of each
channel message, the quantity channel balance is about. New rows add their interactions;
updated rows first remove their previous contribution and then add their new one.
-/

namespace Air.Flat.WitnessGeneration

variable {F : Type} [FiniteField F]
variable {PublicIO : TypeMap} [ProvableType PublicIO]

/-- Operational direction of a typed channel interaction. -/
inductive Direction where
  | pull
  | push
deriving Repr, DecidableEq, BEq

/-- How dynamically generated rows are allocated for repeated demand. -/
inductive Aggregation where
  | perOccurrence
  | byMessage
deriving Repr, DecidableEq, BEq

/-- A structured component-input cell derived from a triggering interaction. -/
inductive InputCell (F : Type) where
  | message (index : ℕ)
  | multiplicity
  | const (value : F)

namespace InputCell

def eval (message : Array F) (multiplicity : ℕ) : InputCell F → F
  | .message index => message[index]?.getD 0
  | .multiplicity => FiniteField.fromNat multiplicity
  | .const value => value

end InputCell

/-- Build one component input row from a channel message and an integer multiplicity. -/
structure InputTemplate (F : Type) where
  cells : List (InputCell F)

namespace InputTemplate

def eval (template : InputTemplate F) (message : Array F) (multiplicity : ℕ) : Array F :=
  (template.cells.map (InputCell.eval message multiplicity)).toArray

end InputTemplate

/-- Demand-driven row generation. -/
structure DemandMode (F : Type) where
  channel : RawChannel F
  direction : Direction
  aggregation : Aggregation
  input : InputTemplate F

/-- A channel handler for preallocated rows. The interaction is the component
interaction whose message selects a row; `column` is the generated multiplicity
input updated when the opposite demand arrives. -/
structure PreallocatedHandler where
  interaction : ℕ
  column : ℕ

/-- Rows allocated before channel balancing. Fixed columns, when present, are
prepended by the generic builder; `input` is an index-aware Witness IR program for
the prover-owned suffix. -/
structure PreallocatedMode (F : Type) where
  rows : UInt64
  input : Witgen.RowProgram F
  input_valid : input.Valid .prover
  handlers : List PreallocatedHandler

/-- The row-allocation modes needed by flat AIR ensembles. Fixed columns are an
orthogonal component property and are not themselves a generation mode. -/
inductive Mode (F : Type) where
  | demand (mode : DemandMode F)
  | preallocated (mode : PreallocatedMode F)

/-- A semantic row used to extend one component to a power-of-two trace height. -/
structure Padding (F : Type) where
  input : Array F
  minimumRows : UInt64 := 1

/-- How the generator builds the rows of one component. -/
structure Generation (F : Type) where
  mode : Mode F
  padding : Padding F

/-- Generation metadata keyed by component name; every ensemble component needs exactly one
entry. -/
structure Config (F : Type) where
  components : List (String × Generation F)

/-- A structural problem with generation metadata, found by `Config.validate`. -/
inductive ConfigError where
  | unknownComponent (name : String)
  | missingComponent (name : String)
  | duplicateComponent (name : String)
  | fixedDemandMode (component : String)
  | demandInputWidth (component : String) (expected actual : ℕ)
  | demandMessageIndex (component : String) (index arity : ℕ)
  | preallocatedRows (component : String) (expected actual : ℕ)
  | fixedPadding (component : String) (expected actual : ℕ)
  | paddingWidth (component : String) (expected actual : ℕ)
  | preallocatedWidth (component : String) (expected actual : ℕ)
  | preallocatedInteraction (component : String) (interaction : ℕ)
  | preallocatedColumn (component : String) (column fixedWidth inputWidth : ℕ)
  | duplicateHandler (channel : String) (direction : Direction)
  | unknownDataRead (component : String) (operation : ℕ) (key : String)
  | dataReadWidth (component : String) (operation : ℕ) (key : String) (expected actual : ℕ)
  | unstableDataRead (component : String) (operation : ℕ) (key : String) (column : ℕ)
deriving Repr, DecidableEq

def Direction.name : Direction → String
  | .pull => "pull"
  | .push => "push"

instance : ToString ConfigError where
  toString
    | .unknownComponent name => s!"generation config names unknown component '{name}'"
    | .missingComponent name => s!"component '{name}' has no generation config"
    | .duplicateComponent name => s!"component '{name}' has multiple generation configs"
    | .fixedDemandMode component =>
        s!"fixed-column component '{component}' must use preallocated generation"
    | .demandInputWidth component expected actual =>
        s!"demand input template of component '{component}' has width {actual}, expected {expected}"
    | .demandMessageIndex component index arity =>
        s!"demand input template of component '{component}' reads message element {index} of a \
          channel with arity {arity}"
    | .preallocatedRows component expected actual =>
        s!"component '{component}' has {actual} preallocated rows, expected {expected} fixed rows"
    | .fixedPadding component expected actual =>
        s!"fixed-column component '{component}' has height {actual}, expected {expected} after padding"
    | .paddingWidth component expected actual =>
        s!"padding input of component '{component}' has width {actual}, expected {expected}"
    | .preallocatedWidth component expected actual =>
        s!"preallocated input suffix of component '{component}' has width {actual}, expected {expected}"
    | .preallocatedInteraction component interaction =>
        s!"preallocated handler interaction {interaction} of component '{component}' is out of bounds"
    | .preallocatedColumn component column fixedWidth inputWidth =>
        s!"preallocated handler column {column} of component '{component}' is outside the mutable \
          input range [{fixedWidth}, {inputWidth})"
    | .duplicateHandler channel direction =>
        s!"multiple generation handlers for {direction.name} demand on channel '{channel}'"
    | .unknownDataRead component operation key =>
        s!"component '{component}' witness operation {operation} reads unknown prover-data component '{key}'"
    | .dataReadWidth component operation key expected actual =>
        s!"component '{component}' witness operation {operation} reads prover-data component '{key}' \
          with width {actual}, expected {expected}"
    | .unstableDataRead component operation key column =>
        s!"component '{component}' witness operation {operation} reads generated prover-data cell \
          '{key}' column {column}"

/-- The direction of demand a preallocated handler's interaction serves: a push serves pulls and
a pull serves pushes. -/
def handlerDirection (interaction : AbstractInteraction F) : Direction :=
  if interaction.assumeGuarantees then .push else .pull

/-- The channels and directions of demand a component's generation mode handles. -/
def Mode.handled (component : Component F) : Mode F → List (String × Direction)
  | .demand mode => [(mode.channel.name, mode.direction)]
  | .preallocated mode => mode.handlers.filterMap fun handler =>
      component.rowOperations.interactions[handler.interaction]?.map fun interaction =>
        (interaction.channel.name, handlerDirection interaction)

/-! ### Prover-data reads

Witness generation reads prover data from the rows initialized before channel balancing. That
snapshot equals the final derived data at every cell that balancing never changes, so witness
programs may read only the stable cells of preallocated components. -/

structure DataRead where
  key : String
  width : ℕ
  column : ℕ

mutual

def fexprDataReads : Witgen.FExpr F → List DataRead
  | .expr _ | .const _ | .localVar _ => []
  | .add left right | .mul left right => fexprDataReads left ++ fexprDataReads right
  | .inv value => fexprDataReads value
  | .ofU64 value => u64exprDataReads value
  | .ite condition thenValue elseValue =>
      bexprDataReads condition ++ fexprDataReads thenValue ++ fexprDataReads elseValue
  | .listGet values index => fexprListDataReads values ++ u64exprDataReads index
  | .dataGet key width row column =>
      { key, width, column := column.val } :: u64exprDataReads row
  | .hintGet _ _ row _ => u64exprDataReads row

def fexprListDataReads : List (Witgen.FExpr F) → List DataRead
  | [] => []
  | value :: values => fexprDataReads value ++ fexprListDataReads values

def u64exprDataReads : Witgen.U64Expr F → List DataRead
  | .const _ | .idx | .localVar _ => []
  | .val value => fexprDataReads value
  | .add left right | .mul left right | .div left right | .mod left right |
      .land left right | .lor left right | .lxor left right |
      .shiftL left right | .shiftR left right => u64exprDataReads left ++ u64exprDataReads right
  | .ite condition thenValue elseValue =>
      bexprDataReads condition ++ u64exprDataReads thenValue ++ u64exprDataReads elseValue

def bexprDataReads : Witgen.BExpr F → List DataRead
  | .true | .false => []
  | .feq left right | .flt left right => fexprDataReads left ++ fexprDataReads right
  | .neq left right | .lt left right => u64exprDataReads left ++ u64exprDataReads right
  | .bit value _ => fexprDataReads value
  | .not condition => bexprDataReads condition
  | .and left right => bexprDataReads left ++ bexprDataReads right

end

def vexprDataReads : {n : ℕ} → Witgen.VExpr F n → List DataRead
  | _, .lit values => values.toList.flatMap fexprDataReads
  | _, .mapRange _ body => fexprDataReads body
  | _, .envRange _ => []
  | _, .bitsOf value => fexprDataReads value
  | _, .append left right => vexprDataReads left ++ vexprDataReads right

def stepDataReads : Witgen.Step F → List DataRead
  | .letF value => fexprDataReads value
  | .letU value => u64exprDataReads value

def witnessDataReads : {n : ℕ} → Witgen.WitgenIR F n → List DataRead
  | _, .native _ => []
  | _, .ir steps output => steps.flatMap stepDataReads ++ vexprDataReads output

/-! ### Validation -/

/-- Look up the generation metadata of every ensemble component, in ensemble order. -/
def Config.align (config : Config F) (ensemble : Ensemble F PublicIO) :
    Except ConfigError (List (Generation F)) := do
  for (name, _) in config.components do
    unless ensemble.tables.any (·.circuit.name == name) do
      throw (.unknownComponent name)
  ensemble.tables.mapM fun component =>
    match config.components.filter (·.1 == component.circuit.name) with
    | [(_, generation)] => pure generation
    | [] => throw (.missingComponent component.circuit.name)
    | _ => throw (.duplicateComponent component.circuit.name)

def Padding.targetHeight (padding : Padding F) (rowCount : ℕ) : ℕ :=
  (max rowCount padding.minimumRows.toNat).nextPowerOfTwo

/-- Check one component's generation mode and padding against the component. -/
def validateGeneration (component : Component F) (generation : Generation F) :
    Except ConfigError Unit := do
  let name := component.circuit.name
  let fixedWidth := component.fixedWidth
  let inputWidth := component.rowOffset
  unless generation.padding.input.size = inputWidth do
    throw (.paddingWidth name inputWidth generation.padding.input.size)
  match component.fixedColumns, generation.mode with
  | none, _ => pure ()
  | some _, .demand _ => throw (.fixedDemandMode name)
  | some fixed, .preallocated preallocated =>
      unless preallocated.rows = fixed.height do
        throw (.preallocatedRows name fixed.height.toNat preallocated.rows.toNat)
      let paddedHeight := generation.padding.targetHeight fixed.height.toNat
      unless paddedHeight = fixed.height.toNat do
        throw (.fixedPadding name fixed.height.toNat paddedHeight)
  match generation.mode with
  | .demand mode =>
      unless mode.input.cells.length = inputWidth do
        throw (.demandInputWidth name inputWidth mode.input.cells.length)
      for cell in mode.input.cells do
        if let .message index := cell then
          unless index < mode.channel.arity do
            throw (.demandMessageIndex name index mode.channel.arity)
  | .preallocated preallocated =>
      unless fixedWidth + preallocated.input.width = inputWidth do
        throw (.preallocatedWidth name (inputWidth - fixedWidth) preallocated.input.width)
      for handler in preallocated.handlers do
        unless handler.interaction < component.rowOperations.interactions.length do
          throw (.preallocatedInteraction name handler.interaction)
        unless fixedWidth ≤ handler.column && handler.column < inputWidth do
          throw (.preallocatedColumn name handler.column fixedWidth inputWidth)

/-- Check that every prover-data read targets a stable cell of a preallocated component. -/
def validateDataReads (components : List (Component F)) (generations : List (Generation F)) :
    Except ConfigError Unit := do
  for component in components do
    for (operation, operationIndex) in component.rowOperations.toFlat.zipIdx do
      if let .witness _ code := operation then
        for read in witnessDataReads code do
          let some (target, generation) := (components.zip generations).find? fun (target, _) =>
              target.circuit.name == read.key
            | throw (.unknownDataRead component.circuit.name operationIndex read.key)
          unless read.width = target.rowOffset do
            throw (.dataReadWidth component.circuit.name operationIndex read.key target.rowOffset
              read.width)
          let unstable := match generation.mode with
            | .demand _ => true
            | .preallocated preallocated =>
                preallocated.handlers.any fun handler => handler.column = read.column
          if unstable then
            throw (.unstableDataRead component.circuit.name operationIndex read.key read.column)

/-- Check that no two components handle demand of the same channel and direction. -/
def validateHandlers (components : List (Component F)) (generations : List (Generation F)) :
    Except ConfigError Unit := do
  let handled := (components.zip generations).flatMap fun (component, generation) =>
    generation.mode.handled component
  for (entry, index) in handled.zipIdx do
    if (handled.take index).contains entry then
      throw (.duplicateHandler entry.1 entry.2)

/-- All structural checks of generation metadata aligned with an ensemble's components. -/
def validateGenerations (ensemble : Ensemble F PublicIO) (generations : List (Generation F)) :
    Except ConfigError Unit := do
  for (component, generation) in ensemble.tables.zip generations do
    validateGeneration component generation
  validateHandlers ensemble.tables generations
  validateDataReads ensemble.tables generations

/-- Generation metadata that passed `Config.validate` for `ensemble`. -/
structure ValidConfig (ensemble : Ensemble F PublicIO) where
  /-- The generation metadata of each component, in ensemble order. -/
  generations : List (Generation F)
  aligned : generations.length = ensemble.tables.length
  valid : validateGenerations ensemble generations = .ok ()

/-- Align generation metadata with an ensemble's components and check it. -/
def Config.validate (config : Config F) (ensemble : Ensemble F PublicIO) :
    Except ConfigError (ValidConfig ensemble) :=
  match config.align ensemble with
  | .error error => .error error
  | .ok generations =>
      if hlength : generations.length = ensemble.tables.length then
        match hvalid : validateGenerations ensemble generations with
        | .error error => .error error
        | .ok () => .ok { generations, aligned := hlength, valid := hvalid }
      else
        -- `align` produces one entry per component
        .error (.missingComponent "")

/-! ### Channel imbalance -/

/-- A nonzero net multiplicity of one channel message. -/
structure Demand (F : Type) where
  channel : String
  message : Array F
  multiplicity : F

namespace Demand

/-- The direction and size of a net multiplicity: pushes count positively and pulls negatively,
so values above half the field order are read as negative. -/
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

/-! ### Rows and tables -/

/-- How a dynamic row was triggered, retained for message-coalesced updates. -/
structure Origin (F : Type) where
  channel : String
  direction : Direction
  message : Array F
  multiplicity : ℕ

structure GeneratedRow (F : Type) where
  input : Array F
  values : Array F
  origin : Option (Origin F) := none

/-- One component's generation state: its operations, its validated generation metadata, and
the rows generated so far. -/
structure ComponentState (F : Type) [FiniteField F] where
  component : Component F
  witgenOps : List (FlatOperation F)
  interactions : List (AbstractInteraction F)
  generation : Generation F
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
    witgenOps := witnessOperationsOnly operations.toFlat
    interactions := operations.interactions
    generation
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

/-- The runtime view of the same complete circuit inputs used by `deriveProverData`. -/
def generatedData (states : List (ComponentState F)) : ProverData F := fun name n =>
  match states.find? (·.component.circuit.name == name) with
  | some state =>
      if h : size state.component.Input = n then
        h ▸ (state.rows.map (inputRow state.component.Input ∘ (·.input)) |>.toArray)
      else #[]
  | none => #[]

/-- Complete a component row from its input with the component's witness programs. -/
def completeRow (state : ComponentState F) (input : Array F) (data : ProverData F)
    (origin : Option (Origin F)) : GeneratedRow F :=
  { input, values := witgenWithData data (ProverHint.empty F) state.witgenOps input, origin }

def rowInteractions (state : ComponentState F) (row : GeneratedRow F) (data : ProverData F) :
    List (Interaction F) :=
  let environment := Environment.fromArray row.values data
  state.interactions.map (·.eval environment)

def fixedPrefix (component : Component F) (row : UInt64) : Array F :=
  match component.fixedColumns with
  | none => #[]
  | some fixed => fixed.row row

/-- The initial rows of a preallocated component: its fixed prefix followed by its row program. -/
def initialInputs (state : ComponentState F) (hint : ProverHint F) : List (Array F) :=
  match state.generation.mode with
  | .demand _ => []
  | .preallocated mode =>
      (List.range mode.rows.toNat).map fun row =>
        fixedPrefix state.component (UInt64.ofNat row) ++
          (mode.input.eval (UInt64.ofNat row) hint).toArray

/-! ### Handling demand -/

def PreallocatedHandler.handles (state : ComponentState F) (handler : PreallocatedHandler)
    (demand : Demand F) : Bool :=
  match state.interactions[handler.interaction]? with
  | none => false
  | some interaction =>
      interaction.channel.name == demand.channel &&
        handlerDirection interaction == demand.direction

def ComponentState.handles (state : ComponentState F) (demand : Demand F) : Bool :=
  match state.generation.mode with
  | .demand mode => mode.channel.name == demand.channel && mode.direction == demand.direction
  | .preallocated mode => mode.handlers.any fun handler => handler.handles state demand

/-- The first demand some component handles, with that component's index. Validation ensures
at most one component handles each channel and direction. -/
def findAction (states : List (ComponentState F)) :
    List (Demand F) → Option (Demand F × ℕ)
  | [] => none
  | demand :: demands =>
      match states.findIdx? (·.handles demand) with
      | some index => some (demand, index)
      | none => findAction states demands

def sameOrigin (origin : Origin F) (mode : DemandMode F) (demand : Demand F) : Bool :=
  origin.channel == mode.channel.name && origin.direction == mode.direction &&
    origin.message == demand.message

def createDemandRow (state : ComponentState F) (mode : DemandMode F)
    (demand : Demand F) (multiplicity : ℕ) (data : ProverData F) : GeneratedRow F :=
  let origin : Origin F := {
    channel := mode.channel.name
    direction := mode.direction
    message := demand.message
    multiplicity
  }
  completeRow state (mode.input.eval demand.message multiplicity) data (some origin)

/-- A component's new rows, and the rows they replaced. -/
structure Mutation (F : Type) [FiniteField F] where
  state : ComponentState F
  removedRows : List (GeneratedRow F) := []
  addedRows : List (GeneratedRow F) := []

def handleDemand (state : ComponentState F) (mode : DemandMode F)
    (demand : Demand F) (data : ProverData F) : Mutation F :=
  match mode.aggregation with
  | .perOccurrence =>
      let rows := List.replicate demand.count (createDemandRow state mode demand 1 data)
      { state := { state with rows := state.rows ++ rows }, addedRows := rows }
  | .byMessage =>
      let existing := state.rows.zipIdx.findSome? fun (row, index) =>
        row.origin.bind fun origin =>
          if sameOrigin origin mode demand then some (row, origin, index) else none
      match existing with
      | none =>
          let row := createDemandRow state mode demand demand.count data
          { state := { state with rows := state.rows ++ [row] }, addedRows := [row] }
      | some (row, origin, index) =>
          let updated :=
            createDemandRow state mode demand (origin.multiplicity + demand.count) data
          { state := { state with rows := state.rows.set index updated }
            removedRows := [row]
            addedRows := [updated] }

/-- The first preallocated row whose handled interaction carries the demanded message. -/
def findPreallocatedRow (state : ComponentState F) (handlers : List PreallocatedHandler)
    (demand : Demand F) (data : ProverData F) :
    Option (PreallocatedHandler × ℕ × GeneratedRow F) :=
  handlers.findSome? fun handler =>
    if handler.handles state demand then
      state.rows.zipIdx.findSome? fun (row, rowIndex) =>
        state.interactions[handler.interaction]?.bind fun abstract =>
          let interaction := abstract.eval (Environment.fromArray row.values data)
          if interaction.msg == demand.message then some (handler, rowIndex, row) else none
    else none

def handlePreallocated (state : ComponentState F) (handlers : List PreallocatedHandler)
    (demand : Demand F) (data : ProverData F) : Option (Mutation F) :=
  match findPreallocatedRow state handlers demand data with
  | none => none
  | some (handler, rowIndex, row) =>
      let value := (row.input[handler.column]?.getD 0) + FiniteField.fromNat demand.count
      let updated := completeRow state (row.input.set! handler.column value) data none
      some {
        state := { state with rows := state.rows.set rowIndex updated }
        removedRows := [row]
        addedRows := [updated]
      }

/-- A semantic failure of witness generation. -/
inductive GenerationError where
  | config (error : ConfigError)
  | unhandledImbalance (channels : List String)
  | noPreallocatedRow (component channel : String)
  | interactionBound
  | noProgress
  | assembly (message : String)
deriving Repr

instance : ToString GenerationError where
  toString
    | .config error => toString error
    | .unhandledImbalance channels =>
        s!"unhandled channel imbalance on: {String.intercalate ", " channels}"
    | .noPreallocatedRow component channel =>
        s!"component '{component}' has no preallocated row for a message on channel '{channel}'"
    | .interactionBound => "generation reached as many interactions as the field has elements"
    | .noProgress => "witness generation made no progress"
    | .assembly message => message

/-- The interactions a handled demand removes and adds. -/
structure Change (F : Type) where
  removed : List (Interaction F)
  added : List (Interaction F)

/-- Route one demand to the component at `index`. -/
def handle (states : List (ComponentState F)) (demand : Demand F) (index : ℕ)
    (data : ProverData F) : Except GenerationError (List (ComponentState F) × Change F) := do
  let some state := states[index]? | return (states, ⟨[], []⟩)
  let mutation ← match state.generation.mode with
    | .demand mode => pure (handleDemand state mode demand data)
    | .preallocated mode =>
        match handlePreallocated state mode.handlers demand data with
        | some mutation => pure mutation
        | none => throw (.noPreallocatedRow state.component.circuit.name demand.channel)
  return (states.set index mutation.state, {
    removed := mutation.removedRows.flatMap (rowInteractions state · data)
    added := mutation.addedRows.flatMap (rowInteractions state · data) })

/-- The state of channel balancing: component rows, the pending imbalance, and the number of
interactions of the verifier and all rows. -/
structure Balancing (F : Type) [FiniteField F] where
  states : List (ComponentState F)
  demands : List (Demand F)
  interactions : ℕ

/-- Balancing terminates: every step adds interactions, which the field size bounds, or keeps
them and settles one pending demand. -/
def Balancing.measure (balancing : Balancing F) : ℕ × ℕ :=
  (FiniteField.size (F := F) - balancing.interactions, balancing.demands.length)

def Balancing.apply (balancing : Balancing F) (states : List (ComponentState F))
    (change : Change F) : Balancing F where
  states
  demands := Demand.addInteractions (Demand.removeInteractions balancing.demands change.removed)
    change.added
  interactions := balancing.interactions + change.added.length - change.removed.length

/-- Handle demand until the channels balance. Balance requires fewer interactions than the field
size, so generation stops when that bound is reached. -/
def balance (data : ProverData F) (balancing : Balancing F) :
    Except GenerationError (Balancing F) :=
  if balancing.demands.isEmpty then .ok balancing
  else if FiniteField.size (F := F) ≤ balancing.interactions then .error .interactionBound
  else
    match findAction balancing.states balancing.demands with
    | none => .error (.unhandledImbalance (balancing.demands.map (·.channel)))
    | some (demand, index) =>
        match handle balancing.states demand index data with
        | .error error => .error error
        | .ok (states, change) =>
            let next := balancing.apply states change
            if _ : Prod.Lex (· < ·) (· < ·) next.measure balancing.measure then
              balance data next
            else .error .noProgress
termination_by balancing.measure
decreasing_by assumption

/-- Pad every component to its target height with its padding row; returns the padded states
and the interactions of the new rows. -/
def padTables (data : ProverData F) (states : List (ComponentState F)) :
    List (ComponentState F) × List (Interaction F) :=
  let padded := states.map fun state =>
    let padding := state.generation.padding
    let count := padding.targetHeight state.rows.length - state.rows.length
    let rows := List.replicate count (completeRow state padding.input data none)
    ({ state with rows := state.rows ++ rows }, rows.flatMap (rowInteractions state · data))
  (padded.map (·.1), padded.flatMap (·.2))

def tablesArePadded (states : List (ComponentState F)) : Bool :=
  states.all fun state =>
    state.rows.length == state.generation.padding.targetHeight state.rows.length

/-- Pad, then balance the interactions of the padding rows, until every component is padded. A
round that leaves a component unpadded added rows through demand, and with them interactions. -/
def padAndBalance (data : ProverData F) (balancing : Balancing F) :
    Except GenerationError (Balancing F) :=
  let (states, added) := padTables data balancing.states
  match balance data
      { balancing.apply states ⟨[], added⟩ with } with
  | .error error => .error error
  | .ok balanced =>
      if tablesArePadded balanced.states then .ok balanced
      else if _ : balancing.interactions < balanced.interactions ∧
          balanced.interactions < FiniteField.size (F := F) then
        padAndBalance data balanced
      else .error .noProgress
termination_by FiniteField.size (F := F) - balancing.interactions
decreasing_by omega

/-! ### Assembling the witness -/

structure AssembledTables (components : List (Component F)) where
  tables : List (Table F)
  same_length : components.length = tables.length
  same_circuits : ∀ index (hindex : index < components.length),
    components[index] = tables[index].component

structure MatchedFixedRows (component : Component F) (rows : List (Array F)) where
  marker : Unit := ()
  property : component.fixedRowsMatch rows

def validateFixedRows (component : Component F) (rows : List (Array F)) :
    Except GenerationError (MatchedFixedRows component rows) :=
  match hcolumns : component.fixedColumns with
  | none => .ok ⟨(), by simp [Component.fixedRowsMatch, hcolumns]⟩
  | some fixed =>
      if hrows : FixedColumns.RowsMatch fixed rows then
        .ok ⟨(), by simpa [Component.fixedRowsMatch, hcolumns] using hrows⟩
      else
        .error (.assembly "generated table does not match its fixed columns")

def assembleTables :
    (components : List (Component F)) → List (ComponentState F) →
      Except GenerationError (AssembledTables components)
  | [], [] => .ok {
      tables := []
      same_length := rfl
      same_circuits := by simp
    }
  | component :: components, state :: states => do
      let rows := state.rows.map (·.values)
      if hlength : rows.length > UInt64.size then
        throw (.assembly s!"generated table for component '{component.circuit.name}' has more \
          than 2^64 rows")
      else if h : ∀ row ∈ rows, row.size = component.width then
        match validateFixedRows component rows with
        | .error error => .error error
        | .ok matched => do
          let table : Table F := {
            component
            table := rows
            uniform_width := h
            length_le := Nat.le_of_not_lt hlength
            fixed_rows_match := matched.property
          }
          let rest ← assembleTables components states
          return {
            tables := table :: rest.tables
            same_length := by simp [rest.same_length]
            same_circuits := by
              intro index hindex
              cases index with
              | zero => rfl
              | succ index =>
                  simp only [List.getElem_cons_succ]
                  exact rest.same_circuits index (by simp at hindex; omega)
          }
      else
        throw (.assembly "generated table contains a row of the wrong width")
  | _, _ => .error (.assembly "generated-table count does not match ensemble component count")

/-- Execute channel-driven generation from validated metadata. `hint` is read only by the row
programs that initialize preallocated components; semantic `ProverData` is derived from the final
committed component rows. -/
def generateValid {ensemble : Ensemble F PublicIO} (config : ValidConfig ensemble)
    (publicInput : PublicIO F) (hint : ProverHint F) :
    Except GenerationError (EnsembleWitness ensemble) := do
  let initial := (ensemble.tables.zip config.generations).map fun (component, generation) =>
    ComponentState.initial component generation
  let initial := initial.map fun state =>
    { state with rows := (initialInputs state hint).map fun input =>
      { input, values := input } }
  let data := generatedData initial
  let initial := initial.map fun state =>
    { state with rows := state.rows.map fun row => completeRow state row.input data none }
  let verifier := ensemble.verifierOperations.interactionValues (.fromInput publicInput data)
  let rows := initial.flatMap fun state => state.rows.flatMap (rowInteractions state · data)
  let balanced ← balance data {
    states := initial
    demands := Demand.addInteractions [] (verifier ++ rows)
    interactions := (verifier ++ rows).length }
  let padded ← padAndBalance data balanced
  let assembled ← assembleTables ensemble.tables padded.states
  return {
    tables := assembled.tables
    publicInput
    same_length := assembled.same_length
    same_circuits := assembled.same_circuits
  }

/-- Validate generation metadata, then generate an ensemble witness. -/
def generate (ensemble : Ensemble F PublicIO) (config : Config F)
    (publicInput : PublicIO F) (hint : ProverHint F) :
    Except GenerationError (EnsembleWitness ensemble) :=
  match config.validate ensemble with
  | .error error => .error (.config error)
  | .ok config => generateValid config publicInput hint

/-- Executable constraint check for the no-legacy-lookup initial milestone. -/
def constraintsHold {ensemble : Ensemble F PublicIO} (witness : EnsembleWitness ensemble) : Bool :=
  witness.tables.all fun table =>
    table.table.all fun row =>
      table.component.operations.lookups.isEmpty &&
      table.component.operations.constraints.all fun constraint =>
        constraint.eval (Environment.fromArray row witness.data) == 0

/-- Executable balance check using the same net-multiplicity representation. -/
def channelsBalanced {ensemble : Ensemble F PublicIO} (witness : EnsembleWitness ensemble) : Bool :=
  (Demand.addInteractions [] witness.interactions).isEmpty

end Air.Flat.WitnessGeneration
