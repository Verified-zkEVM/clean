module

public import Clean.Air.WitnessGeneration.Config

@[expose] public section

/-!
# Validating a witness generation config

TODO. Generation starts with `Config.validate`, which rejects configs that don't fit the ensemble,
for example a demand input of the wrong width. Most of these checks should become types or proof
obligations of the config instead.
-/

namespace Air.Flat.WitnessGeneration

variable {F : Type} [FiniteField F]
variable {PublicIO : TypeMap} [ProvableType PublicIO]

/-- A problem with a generation config, found by `Config.validate`. -/
inductive ConfigError where
  | unknownComponent (name : String)
  | missingComponent (name : String)
  | duplicateComponent (name : String)
  | demandWithFixedColumns (component : String)
  | preallocatedWithoutFixedColumns (component : String)
  | demandInputWidth (component : String) (expected actual : ℕ)
  | demandMessageIndex (component : String) (index arity : ℕ)
  | paddingWidth (component : String) (expected actual : ℕ)
  | preallocatedHeight (component : String) (height : ℕ)
  | preallocatedWidth (component : String) (expected actual : ℕ)
  | counterInteractions (component channel : String) (count : ℕ)
  | counterMultiplicity (component channel : String)
  | counterMessage (component channel : String)
  | byMessagePush (component : String)
  | duplicateHandler (channel : String) (surplus : Direction)
  | unknownDataRead (component : String) (operation : ℕ) (key : String)
  | dataReadWidth (component : String) (operation : ℕ) (key : String) (expected actual : ℕ)
  | unstableDataRead (component : String) (operation : ℕ) (key : String) (column : ℕ)
deriving Repr, DecidableEq

instance : ToString ConfigError where
  toString
    | .unknownComponent name => s!"generation config names unknown component '{name}'"
    | .missingComponent name => s!"component '{name}' has no generation config"
    | .duplicateComponent name => s!"component '{name}' has multiple generation configs"
    | .demandWithFixedColumns component =>
        s!"component '{component}' has fixed columns, so it must be preallocated"
    | .preallocatedWithoutFixedColumns component =>
        s!"component '{component}' has no fixed columns, so it can't be preallocated"
    | .demandInputWidth component expected actual =>
        s!"demand input of component '{component}' has width {actual}, expected {expected}"
    | .demandMessageIndex component index arity =>
        s!"demand input of component '{component}' reads message element {index} of a channel \
          with arity {arity}"
    | .paddingWidth component expected actual =>
        s!"padding input of component '{component}' has width {actual}, expected {expected}"
    | .preallocatedHeight component height =>
        s!"preallocated component '{component}' has {height} fixed rows, which is not a power of \
          two"
    | .preallocatedWidth component expected actual =>
        s!"row program of component '{component}' has width {actual}, expected {expected}"
    | .counterInteractions component channel count =>
        s!"component '{component}' has {count} interactions on channel '{channel}', expected \
          one to count"
    | .counterMultiplicity component channel =>
        s!"the multiplicity of the interaction of component '{component}' on channel \
          '{channel}' is not a non-fixed input variable"
    | .counterMessage component channel =>
        s!"the message of the interaction of component '{component}' on channel '{channel}' \
          reads a cell other than a non-counter input cell"
    | .byMessagePush component =>
        s!"component '{component}' aggregates by message, so it can only answer pull surplus"
    | .duplicateHandler channel surplus =>
        s!"multiple components handle {surplus.name} surplus on channel '{channel}'"
    | .unknownDataRead component operation key =>
        s!"component '{component}' witness operation {operation} reads unknown prover-data \
          component '{key}'"
    | .dataReadWidth component operation key expected actual =>
        s!"component '{component}' witness operation {operation} reads prover-data component \
          '{key}' with width {actual}, expected {expected}"
    | .unstableDataRead component operation key column =>
        s!"component '{component}' witness operation {operation} reads cell {column} of \
          '{key}', which generation changes"

/-! ### Counters -/

/-- A counter, resolved from the channel it counts on. -/
structure Counter where
  /-- The position of the counted interaction among the component's row interactions. -/
  interaction : ℕ
  /-- The input column holding the interaction's multiplicity. -/
  column : ℕ

/-- The cells an expression reads. -/
def expressionCells : Expression F → List ℕ
  | .var cell => [cell.index]
  | .const _ => []
  | .add left right | .mul left right => expressionCells left ++ expressionCells right

/-- The counter of a component on `channel`: its unique interaction on that channel, whose
multiplicity must be an input variable after the fixed columns. -/
def Counter.resolve (component : Component F) (channel : RawChannel F) :
    Except ConfigError Counter :=
  let name := component.circuit.name
  match component.rowOperations.interactions.zipIdx.filter (·.1.channel.name == channel.name) with
  | [(interaction, index)] =>
      match interaction.mult with
      | .var cell =>
          if component.fixedWidth ≤ cell.index && cell.index < component.rowOffset then
            .ok { interaction := index, column := cell.index }
          else .error (.counterMultiplicity name channel.name)
      | _ => .error (.counterMultiplicity name channel.name)
  | found => .error (.counterInteractions name channel.name found.length)

/-- The counters of a component's generation: one per channel of a preallocated component, and one
on the channel of a `byMessage` demand component. -/
def Generation.counters (component : Component F) : Generation F → Except ConfigError (List Counter)
  | .demand mode => match mode.aggregation with
    | .perOccurrence => pure []
    | .byMessage => return [← Counter.resolve component mode.channel]
  | .preallocated mode => mode.channels.mapM (Counter.resolve component)

/-- The channels a component's generation handles, with the surplus it answers there. A counter
only grows the pushes of its interaction, so it answers pull surplus. -/
def Generation.handled : Generation F → List (String × Direction)
  | .demand mode => [(mode.channel.name, mode.surplus)]
  | .preallocated mode => mode.channels.map (·.name, .pull)

/-- Check that counting never changes which message a row answers: the messages of counted
interactions only read input cells that aren't counters. -/
def validateCounters (component : Component F) (counters : List Counter) :
    Except ConfigError Unit := do
  let interactions := component.rowOperations.interactions
  for counter in counters do
    let some interaction := interactions[counter.interaction]? | continue
    let cells := interaction.msg.toList.flatMap expressionCells
    unless cells.all fun cell => cell < component.rowOffset && counters.all (·.column ≠ cell) do
      throw (.counterMessage component.circuit.name interaction.channel.name)

/-! ### Prover-data reads

TODO. Witness programs read prover data from a snapshot of the rows initialized before channel
balancing, which only agrees with the final prover data on cells that balancing doesn't change. So
for now, reads are restricted to such cells: the non-counter cells of preallocated components. -/

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

/-- Look up the generation of every ensemble component, in ensemble order. -/
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

/-- Check one component's generation against the component. -/
def validateGeneration (component : Component F) (generation : Generation F) :
    Except ConfigError Unit := do
  let name := component.circuit.name
  let fixedWidth := component.fixedWidth
  let inputWidth := component.rowOffset
  let counters ← generation.counters component
  validateCounters component counters
  match component.fixedColumns, generation with
  | some _, .demand _ => throw (.demandWithFixedColumns name)
  | none, .preallocated _ => throw (.preallocatedWithoutFixedColumns name)
  | _, .demand mode =>
      if mode.aggregation == .byMessage && mode.surplus == .push then
        throw (.byMessagePush name)
      unless mode.input.length + counters.length = inputWidth do
        throw (.demandInputWidth name (inputWidth - counters.length) mode.input.length)
      for cell in mode.input do
        if let .message index := cell then
          unless index < mode.channel.arity do
            throw (.demandMessageIndex name index mode.channel.arity)
      unless mode.padding.input.size = inputWidth do
        throw (.paddingWidth name inputWidth mode.padding.input.size)
  | some fixed, .preallocated mode =>
      unless nextPowerOfTwo fixed.height.toNat = fixed.height.toNat do
        throw (.preallocatedHeight name fixed.height.toNat)
      unless fixedWidth + counters.length + mode.width = inputWidth do
        throw (.preallocatedWidth name (inputWidth - fixedWidth - counters.length) mode.width)

/-- Check that every prover-data read targets a cell of a preallocated component that generation
doesn't change. -/
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
          match generation with
          | .demand _ =>
              throw (.unstableDataRead component.circuit.name operationIndex read.key read.column)
          | .preallocated _ =>
              let counters ← generation.counters target
              if counters.any (·.column = read.column) then
                throw (.unstableDataRead component.circuit.name operationIndex read.key read.column)

/-- Check that no two components answer the same surplus on the same channel. -/
def validateHandlers (generations : List (Generation F)) : Except ConfigError Unit := do
  let handled := generations.flatMap (·.handled)
  for (entry, index) in handled.zipIdx do
    if (handled.take index).contains entry then
      throw (.duplicateHandler entry.1 entry.2)

/-- All checks of the generations aligned with an ensemble's components. -/
def validateGenerations (ensemble : Ensemble F PublicIO) (generations : List (Generation F)) :
    Except ConfigError Unit := do
  for (component, generation) in ensemble.tables.zip generations do
    validateGeneration component generation
  validateHandlers generations
  validateDataReads ensemble.tables generations

/-- A config that passed `Config.validate` for `ensemble`. -/
structure ValidConfig (ensemble : Ensemble F PublicIO) where
  /-- The generation of each component, in ensemble order. -/
  generations : List (Generation F)
  aligned : generations.length = ensemble.tables.length
  valid : validateGenerations ensemble generations = .ok ()
  fuel : ℕ

/-- Align a config with an ensemble's components and check it. -/
def Config.validate (config : Config F) (ensemble : Ensemble F PublicIO) :
    Except ConfigError (ValidConfig ensemble) :=
  match config.align ensemble with
  | .error error => .error error
  | .ok generations =>
      if hlength : generations.length = ensemble.tables.length then
        match hvalid : validateGenerations ensemble generations with
        | .error error => .error error
        | .ok () => .ok { generations, aligned := hlength, valid := hvalid, fuel := config.fuel }
      else
        -- `align` produces one entry per component
        .error (.missingComponent "")

end Air.Flat.WitnessGeneration
