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
  /-- Input columns whose cells start undefined: the first read of a cell, in generation order,
  defines it as that read's proposal. -/
  lazyColumns : List ℕ := []

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
  | lazyColumn (component : String) (column fixedWidth inputWidth : ℕ)
  | lazyHandlerColumn (component : String) (column : ℕ)
  | lazyComponentRead (component : String) (operation : ℕ)
  | paddedDataRead (component : String) (operation : ℕ) (key : String)
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
    | .lazyColumn component column fixedWidth inputWidth =>
        s!"lazy column {column} of component '{component}' is outside the mutable input range \
          [{fixedWidth}, {inputWidth})"
    | .lazyHandlerColumn component column =>
        s!"column {column} of component '{component}' is both lazy and a handler column"
    | .paddedDataRead component operation key =>
        s!"component '{component}' witness operation {operation} reads prover-data component \
          '{key}', whose padding adds rows"
    | .lazyComponentRead component operation =>
        s!"component '{component}' has lazy columns, so its witness operation {operation} must not \
          read prover data with a read step"

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
programs may read only the stable cells of preallocated components. Read steps may also read the
lazy cells of preallocated components, which the first read defines. -/

structure DataRead where
  key : String
  width : ℕ
  column : ℕ
  /-- A read step, which may define a lazy cell, rather than an `FExpr.dataGet`. -/
  defining : Bool := false

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
  | .read key width row column proposal =>
      { key, width, column := column.val, defining := true } ::
        (u64exprDataReads row ++ fexprDataReads proposal)

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
      for column in preallocated.lazyColumns do
        unless fixedWidth ≤ column && column < inputWidth do
          throw (.lazyColumn name column fixedWidth inputWidth)
        if preallocated.handlers.any (·.column = column) then
          throw (.lazyHandlerColumn name column)

/-- The lazy columns of a component's generation mode. -/
def Mode.lazyColumns (mode : Mode F) : List ℕ :=
  match mode with
  | .demand _ => []
  | .preallocated allocation => allocation.lazyColumns

/-- Check that every prover-data read targets a stable cell of a preallocated component, or a
lazy cell through a read step, and that components with lazy cells do not read them. -/
def validateDataReads (components : List (Component F)) (generations : List (Generation F)) :
    Except ConfigError Unit := do
  for (component, ownGeneration) in components.zip generations do
    for (operation, operationIndex) in component.rowOperations.toFlat.zipIdx do
      if let .witness _ code := operation then
        if !ownGeneration.mode.lazyColumns.isEmpty &&
            (witnessDataReads code).any (·.defining) then
          throw (.lazyComponentRead component.circuit.name operationIndex)
        for read in witnessDataReads code do
          let some (target, generation) := (components.zip generations).find? fun (target, _) =>
              target.circuit.name == read.key
            | throw (.unknownDataRead component.circuit.name operationIndex read.key)
          unless read.width = target.rowOffset do
            throw (.dataReadWidth component.circuit.name operationIndex read.key target.rowOffset
              read.width)
          match generation.mode with
          | .demand _ =>
              throw (.unstableDataRead component.circuit.name operationIndex read.key read.column)
          | .preallocated preallocated =>
              if preallocated.handlers.any (·.column = read.column) ||
                  (!read.defining && preallocated.lazyColumns.contains read.column) then
                throw (.unstableDataRead component.circuit.name operationIndex read.key read.column)
              unless generation.padding.targetHeight preallocated.rows.toNat =
                  preallocated.rows.toNat do
                throw (.paddedDataRead component.circuit.name operationIndex read.key)

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
    | .interactionBound => "generation reached as many interactions as the field characteristic"
    | .noProgress => "witness generation made no progress"
    | .assembly message => message

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
  /-- The lazy input columns no read has defined yet. -/
  undefined : List ℕ := []

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

/-- A lazy cell defined by its first read: column `column` of row `row` of component `key`. -/
structure Definition (F : Type) where
  key : String
  row : ℕ
  column : ℕ
  value : F

/-- The generation-time value of a prover-data cell: a pending definition, else the cell of the
component's row, or `none` if the cell is still undefined. Missing rows read as 0, as in the
derived prover data; validation ensures rows that are read are never added later. -/
def readCell (states : List (ComponentState F)) (pending : List (Definition F)) (key : String)
    (width row column : ℕ) : Option F :=
  match pending.find? fun definition =>
      definition.key == key && definition.row == row && definition.column == column with
  | some definition => some definition.value
  | none =>
      match states.find? (·.component.circuit.name == key) with
      | none => some 0
      | some state =>
          if state.component.rowOffset = width then
            match state.rows[row]? with
            | none => some 0
            | some generated =>
                if generated.undefined.contains column then none
                else some (generated.input[column]?.getD 0)
          else some 0

/-- Run `let`-steps like `Witgen.evalSteps`, except that a read step of an undefined cell defines
it as its proposal. Returns the locals and the pending definitions. -/
def runSteps (states : List (ComponentState F)) (env : ProverEnvironment F) :
    List (Witgen.Step F) → Array (F ⊕ UInt64) → List (Definition F) →
      Array (F ⊕ UInt64) × List (Definition F)
  | [], locals, pending => (locals, pending)
  | .letF value :: steps, locals, pending =>
      runSteps states env steps (locals.push (.inl (value.eval { env, locals }))) pending
  | .letU value :: steps, locals, pending =>
      runSteps states env steps (locals.push (.inr (value.eval { env, locals }))) pending
  | .read key width row column proposal :: steps, locals, pending =>
      let index := (row.eval { env, locals }).toNat
      match readCell states pending key width index column.val with
      | some value => runSteps states env steps (locals.push (.inl value)) pending
      | none =>
          let value := proposal.eval { env, locals }
          runSteps states env steps (locals.push (.inl value))
            (pending ++ [{ key, row := index, column := column.val, value }])

def witgenStep (states : List (ComponentState F)) (data : ProverData F) (hint : ProverHint F)
    (acc : Array F × List (Definition F)) : FlatOperation F → Array F × List (Definition F)
  | .witness _ code =>
      let environment : ProverEnvironment F := {
        get index := acc.1[index]?.getD 0
        data
        hint
      }
      match code with
      | .native compute => (acc.1 ++ (compute environment).toArray, acc.2)
      | .ir steps output =>
          let (locals, pending) := runSteps states environment steps #[] acc.2
          (acc.1 ++ (output.eval { env := environment, locals }).toArray, pending)
  | .assert _ | .lookup _ | .interact _ => acc

/-- Run a component's witness programs on an input row. -/
def witgen (states : List (ComponentState F)) (data : ProverData F) (hint : ProverHint F)
    (ops : List (FlatOperation F)) (input : Array F) (pending : List (Definition F)) :
    Array F × List (Definition F) :=
  ops.foldl (witgenStep states data hint) (input, pending)

/-- The runtime view of the same complete circuit inputs used by `deriveProverData`. -/
def generatedData (states : List (ComponentState F)) : ProverData F := fun name n =>
  match states.find? (·.component.circuit.name == name) with
  | some state =>
      if h : size state.component.Input = n then
        h ▸ (state.rows.map (inputRow state.component.Input ∘ (·.input)) |>.toArray)
      else #[]
  | none => #[]

/-- Complete a component row from its input with the component's witness programs, reading
prover data from `states` and the pending definitions. -/
def completeRow (states : List (ComponentState F)) (pending : List (Definition F))
    (state : ComponentState F) (input : Array F) (data : ProverData F) (hint : ProverHint F)
    (origin : Option (Origin F)) (undefined : List ℕ) : GeneratedRow F × List (Definition F) :=
  let (values, pending) := witgen states data hint state.witgenOps input pending
  ({ input, values, origin, undefined }, pending)

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

def createDemandRow (states : List (ComponentState F)) (state : ComponentState F)
    (mode : DemandMode F) (demand : Demand F) (multiplicity : ℕ) (data : ProverData F) (hint : ProverHint F) :
    GeneratedRow F × List (Definition F) :=
  let origin : Origin F := {
    channel := mode.channel.name
    direction := mode.direction
    message := demand.message
    multiplicity
  }
  completeRow states [] state (mode.input.eval demand.message multiplicity) data hint (some origin) []

/-- A component's new rows, the rows they replaced, and the lazy cells their reads defined. -/
structure Mutation (F : Type) [FiniteField F] where
  state : ComponentState F
  removedRows : List (GeneratedRow F) := []
  addedRows : List (GeneratedRow F) := []
  definitions : List (Definition F) := []

def handleDemand (states : List (ComponentState F)) (state : ComponentState F)
    (mode : DemandMode F) (demand : Demand F) (data : ProverData F) (hint : ProverHint F) : Mutation F :=
  match mode.aggregation with
  | .perOccurrence =>
      let (row, definitions) := createDemandRow states state mode demand 1 data hint
      let rows := List.replicate demand.count row
      { state := { state with rows := state.rows ++ rows }, addedRows := rows, definitions }
  | .byMessage =>
      match state.rows.zipIdx.findSome? fun (row, index) =>
          row.origin.bind fun origin =>
            if sameOrigin origin mode demand then some (row, origin, index) else none with
      | none =>
          let (row, definitions) := createDemandRow states state mode demand demand.count data hint
          { state := { state with rows := state.rows ++ [row] }, addedRows := [row], definitions }
      | some (row, origin, index) =>
          let (updated, definitions) :=
            createDemandRow states state mode demand (origin.multiplicity + demand.count) data hint
          { state := { state with rows := state.rows.set index updated }
            removedRows := [row]
            addedRows := [updated]
            definitions }

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

def handlePreallocated (states : List (ComponentState F)) (state : ComponentState F)
    (handlers : List PreallocatedHandler) (demand : Demand F) (data : ProverData F) (hint : ProverHint F) :
    Option (Mutation F) :=
  match findPreallocatedRow state handlers demand data with
  | none => none
  | some (handler, rowIndex, row) =>
      let value := (row.input[handler.column]?.getD 0) + FiniteField.fromNat demand.count
      let (updated, definitions) :=
        completeRow states [] state (row.input.set! handler.column value) data hint none row.undefined
      some {
        state := { state with rows := state.rows.set rowIndex updated }
        removedRows := [row]
        addedRows := [updated]
        definitions
      }

/-- The interactions a handled demand removes and adds. -/
structure Change (F : Type) where
  removed : List (Interaction F)
  added : List (Interaction F)

def Change.append (change change' : Change F) : Change F where
  removed := change.removed ++ change'.removed
  added := change.added ++ change'.added

/-- Set the defined lazy cells in their rows, completing each defined row again. -/
def define (data : ProverData F) (hint : ProverHint F) :
    List (ComponentState F) → List (Definition F) → List (ComponentState F) × Change F
  | states, [] => (states, ⟨[], []⟩)
  | states, definition :: definitions =>
      match states.findIdx? (·.component.circuit.name == definition.key) with
      | none => define data hint states definitions
      | some index =>
          match states[index]? with
          | none => define data hint states definitions
          | some state =>
              match state.rows[definition.row]? with
              | none => define data hint states definitions
              | some row =>
                  let (updated, _) := completeRow states [] state
                    (row.input.set! definition.column definition.value) data hint row.origin
                    (row.undefined.erase definition.column)
                  let states := states.set index
                    { state with rows := state.rows.set definition.row updated }
                  let (states, change) := define data hint states definitions
                  (states, Change.append
                    ⟨rowInteractions state row data, rowInteractions state updated data⟩ change)

/-- Route one demand to the component at `index`. -/
def handle (states : List (ComponentState F)) (demand : Demand F) (index : ℕ)
    (data : ProverData F) (hint : ProverHint F) : Except GenerationError (List (ComponentState F) × Change F) := do
  let some state := states[index]? | return (states, ⟨[], []⟩)
  let mutation ← match state.generation.mode with
    | .demand mode => pure (handleDemand states state mode demand data hint)
    | .preallocated mode =>
        match handlePreallocated states state mode.handlers demand data hint with
        | some mutation => pure mutation
        | none => throw (.noPreallocatedRow state.component.circuit.name demand.channel)
  let (states, defined) := define data hint (states.set index mutation.state) mutation.definitions
  return (states, Change.append {
    removed := mutation.removedRows.flatMap (rowInteractions state · data)
    added := mutation.addedRows.flatMap (rowInteractions state · data) } defined)

/-- The state of channel balancing: component rows, the pending imbalance, and the number of
interactions of the verifier and all rows. -/
structure Balancing (F : Type) [FiniteField F] where
  states : List (ComponentState F)
  demands : List (Demand F)
  interactions : ℕ

/-- Balancing terminates: every step adds interactions, which the field characteristic bounds, or keeps
them and settles one pending demand. -/
def Balancing.measure (balancing : Balancing F) : ℕ × ℕ :=
  (FiniteField.char F - balancing.interactions, balancing.demands.length)

def Balancing.apply (balancing : Balancing F) (states : List (ComponentState F))
    (change : Change F) : Balancing F where
  states
  demands := Demand.addInteractions (Demand.removeInteractions balancing.demands change.removed)
    change.added
  interactions := balancing.interactions + change.added.length - change.removed.length

/-- Handle demand until the channels balance. Balance requires fewer interactions than the field
characteristic, so generation stops when that bound is reached. -/
def balance (data : ProverData F) (hint : ProverHint F) (balancing : Balancing F) :
    Except GenerationError (Balancing F) :=
  if balancing.demands.isEmpty then .ok balancing
  else if FiniteField.char F ≤ balancing.interactions then .error .interactionBound
  else
    match findAction balancing.states balancing.demands with
    | none => .error (.unhandledImbalance (balancing.demands.map (·.channel)))
    | some (demand, index) =>
        match handle balancing.states demand index data hint with
        | .error error => .error error
        | .ok (states, change) =>
            let next := balancing.apply states change
            if _ : Prod.Lex (· < ·) (· < ·) next.measure balancing.measure then
              balance data hint next
            else .error .noProgress
termination_by balancing.measure
decreasing_by assumption

/-- Append padding rows up to a component's target height; returns the padded state, the
interactions of the new rows, and the pending definitions extended by their reads. -/
def padState (data : ProverData F) (hint : ProverHint F) (view : List (ComponentState F)) (state : ComponentState F)
    (pending : List (Definition F)) :
    ComponentState F × List (Interaction F) × List (Definition F) :=
  let padding := state.generation.padding
  let count := padding.targetHeight state.rows.length - state.rows.length
  if count = 0 then (state, [], pending)
  else
    let (row, pending) := completeRow view pending state padding.input data hint none []
    let rows := List.replicate count row
    ({ state with rows := state.rows ++ rows }, rows.flatMap (rowInteractions state · data),
      pending)

/-- Pad every component in order, threading the pending definitions. -/
def padStates (data : ProverData F) (hint : ProverHint F) (view : List (ComponentState F)) :
    List (ComponentState F) → List (Definition F) →
      List (ComponentState F) × List (Interaction F) × List (Definition F)
  | [], pending => ([], [], pending)
  | state :: states, pending =>
      let (state, added, pending) := padState data hint view state pending
      let (states, added', pending) := padStates data hint view states pending
      (state :: states, added ++ added', pending)

/-- Pad every component to its target height with its padding row. -/
def padTables (data : ProverData F) (hint : ProverHint F) (states : List (ComponentState F)) :
    List (ComponentState F) × Change F :=
  let (padded, added, pending) := padStates data hint states states []
  let (padded, defined) := define data hint padded pending
  (padded, Change.append ⟨[], added⟩ defined)

def tablesArePadded (states : List (ComponentState F)) : Bool :=
  states.all fun state =>
    state.rows.length == state.generation.padding.targetHeight state.rows.length

/-- Pad, then balance the interactions of the padding rows, until every component is padded. A
round that leaves a component unpadded added rows through demand, and with them interactions. -/
def padAndBalance (data : ProverData F) (hint : ProverHint F) (balancing : Balancing F) :
    Except GenerationError (Balancing F) :=
  let (states, change) := padTables data hint balancing.states
  match balance data hint (balancing.apply states change) with
  | .error error => .error error
  | .ok balanced =>
      if tablesArePadded balanced.states then .ok balanced
      else if _ : balancing.interactions < balanced.interactions ∧
          balanced.interactions < FiniteField.char F then
        padAndBalance data hint balanced
      else .error .noProgress
termination_by FiniteField.char F - balancing.interactions
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

/-- Complete rows in order, threading the pending definitions. -/
def completeRows (data : ProverData F) (hint : ProverHint F) (view : List (ComponentState F))
    (state : ComponentState F) :
    List (GeneratedRow F) → List (Definition F) → List (GeneratedRow F) × List (Definition F)
  | [], pending => ([], pending)
  | row :: rows, pending =>
      let (row, pending) := completeRow view pending state row.input data hint row.origin row.undefined
      let (rows, pending) := completeRows data hint view state rows pending
      (row :: rows, pending)

/-- Complete the rows of every component in order, threading the pending definitions. -/
def completeStates (data : ProverData F) (hint : ProverHint F) (view : List (ComponentState F)) :
    List (ComponentState F) → List (Definition F) → List (ComponentState F) × List (Definition F)
  | [], pending => ([], pending)
  | state :: states, pending =>
      let (rows, pending) := completeRows data hint view state state.rows pending
      let (states, pending) := completeStates data hint view states pending
      ({ state with rows } :: states, pending)

/-- The components with their initial rows completed, and the prover data the rows derive. -/
def initialStates {ensemble : Ensemble F PublicIO} (config : ValidConfig ensemble)
    (hint : ProverHint F) : List (ComponentState F) × ProverData F :=
  let initial := (ensemble.tables.zip config.generations).map fun (component, generation) =>
    ComponentState.initial component generation
  let initial := initial.map fun state =>
    { state with rows := (initialInputs state hint).map fun input =>
      { input, values := input, undefined := state.generation.mode.lazyColumns } }
  let data := generatedData initial
  let (completed, pending) := completeStates data hint initial initial []
  ((define data hint completed pending).1, data)

/-- Execute channel-driven generation from validated metadata. `hint` is read by the row programs
that initialize preallocated components and by the witness programs of all rows, for example for
the proposals of read steps; semantic `ProverData` is derived from the final committed component
rows. -/
def generateValid {ensemble : Ensemble F PublicIO} (config : ValidConfig ensemble)
    (publicInput : PublicIO F) (hint : ProverHint F) :
    Except GenerationError (EnsembleWitness ensemble) := do
  let (initial, data) := initialStates config hint
  let verifier := ensemble.verifierOperations.interactionValues (.fromInput publicInput data)
  let rows := initial.flatMap fun state => state.rows.flatMap (rowInteractions state · data)
  let balanced ← balance data hint {
    states := initial
    demands := Demand.addInteractions [] (verifier ++ rows)
    interactions := (verifier ++ rows).length }
  let padded ← padAndBalance data hint balanced
  let assembled ← assembleTables ensemble.tables padded.states
  let witness : EnsembleWitness ensemble := {
    tables := assembled.tables
    publicInput
    same_length := assembled.same_length
    same_circuits := assembled.same_circuits
  }
  if witness.interactions.length < FiniteField.char F then return witness
  throw .interactionBound

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
