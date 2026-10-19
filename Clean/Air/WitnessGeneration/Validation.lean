module

public import Clean.Air.WitnessGeneration.Counter

@[expose] public section

/-!
# Validating the generation of an ensemble

TODO. Generation starts with `validateGeneration`, which rejects component generations
that don't fit their components, for example a demand input of the wrong width. Most of these
checks should become types or proof obligations of the generation instead.
-/

namespace Air.Flat.WitnessGeneration

variable {F : Type} [FiniteField F]
variable {PublicIO : TypeMap} [ProvableType PublicIO]

/-- A problem with the generation of an ensemble, found by `validateGeneration`. -/
inductive ValidationError where
  | demandInputWidth (component : String) (expected actual : ℕ)
  | demandMessageIndex (component : String) (index arity : ℕ)
  | paddingWidth (component : String) (expected actual : ℕ)
  | preallocatedHeight (component : String) (height : ℕ)
  | preallocatedWidth (component : String) (expected actual : ℕ)
  | counter (component : String) (error : CounterError)
  | byMessagePush (component : String)
  | byMessageChannel (component counted demanded : String)
  | duplicateHandler (channel : String) (surplus : Direction)
  | unknownDataRead (component : String) (operation : ℕ) (key : String)
  | dataReadWidth (component : String) (operation : ℕ) (key : String) (expected actual : ℕ)
  | unstableDataRead (component : String) (operation : ℕ) (key : String) (column : ℕ)
deriving Repr, DecidableEq

instance : ToString ValidationError where
  toString
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
    | .counter component error => s!"component '{component}' {error}"
    | .byMessagePush component =>
        s!"component '{component}' aggregates by message, so it can only answer pull surplus"
    | .byMessageChannel component counted demanded =>
        s!"component '{component}' counts on channel '{counted}' but answers demand on channel \
          '{demanded}'"
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

/-- The channels a component handles, with the surplus it answers there. A counter only grows the
pushes of its interaction, so it answers pull surplus. -/
def handledChannels (component : Component F) (counters : List Counter) :
    List (String × Direction) :=
  match component.generation with
  | .demand mode => [(mode.channel.name, mode.surplus)]
  | .preallocated _ => counters.map (·.channel, .pull)

/-- Check a component's generation against the component, and resolve its counters. -/
def validateComponent (component : Component F) : Except ValidationError (List Counter) := do
  let name := component.circuit.name
  let fixedWidth := component.fixedWidth
  let inputWidth := component.rowOffset
  let counters ← (resolveCounters component).mapError (.counter name)
  match component.generation with
  | .demand mode =>
      if let .byMessage _ := mode.aggregation then
        if mode.surplus == .push then throw (.byMessagePush name)
        for counter in counters do
          unless counter.channel == mode.channel.name do
            throw (.byMessageChannel name counter.channel mode.channel.name)
      unless mode.input.length + counters.length = inputWidth do
        throw (.demandInputWidth name (inputWidth - counters.length) mode.input.length)
      for cell in mode.input do
        if let .message index := cell then
          unless index < mode.channel.arity do
            throw (.demandMessageIndex name index mode.channel.arity)
      unless mode.padding.input.size = inputWidth do
        throw (.paddingWidth name inputWidth mode.padding.input.size)
  | .preallocated mode =>
      let height := (component.fixedColumns.map (·.height.toNat)).getD 0
      unless nextPowerOfTwo height = height do
        throw (.preallocatedHeight name height)
      unless fixedWidth + counters.length + mode.width = inputWidth do
        throw (.preallocatedWidth name (inputWidth - fixedWidth - counters.length) mode.width)
  return counters

/-- Check that every prover-data read targets a cell of a preallocated component that generation
doesn't change. -/
def validateDataReads (components : List (Component F)) (counters : List (List Counter)) :
    Except ValidationError Unit := do
  let targets := components.zip counters
  for component in components do
    for (operation, operationIndex) in component.rowOperations.toFlat.zipIdx do
      if let .witness _ code := operation then
        for read in witnessDataReads code do
          let some (target, targetCounters) := targets.find? fun (target, _) =>
              target.circuit.name == read.key
            | throw (.unknownDataRead component.circuit.name operationIndex read.key)
          unless read.width = target.rowOffset do
            throw (.dataReadWidth component.circuit.name operationIndex read.key target.rowOffset
              read.width)
          match target.generation with
          | .demand _ =>
              throw (.unstableDataRead component.circuit.name operationIndex read.key read.column)
          | .preallocated _ =>
              if targetCounters.any (·.column = read.column) then
                throw (.unstableDataRead component.circuit.name operationIndex read.key read.column)

/-- Check that no two components answer the same surplus on the same channel. -/
def validateHandlers (components : List (Component F)) (counters : List (List Counter)) :
    Except ValidationError Unit := do
  let handled := (components.zip counters).flatMap fun (component, counters) =>
    handledChannels component counters
  for (entry, index) in handled.zipIdx do
    if (handled.take index).contains entry then
      throw (.duplicateHandler entry.1 entry.2)

/-- All checks of the components' generations; returns the counters of every component. -/
def validateComponents (components : List (Component F)) :
    Except ValidationError (List (List Counter)) := do
  let counters ← components.mapM validateComponent
  validateHandlers components counters
  validateDataReads components counters
  return counters

/-- An ensemble whose generation passed `validateGeneration`, with the counters of every
component, in ensemble order. -/
structure ValidGeneration (ens : Ensemble F PublicIO) where
  counters : List (List Counter)
  valid : validateComponents ens.tables = .ok counters

/-- Check the generation of every component of an ensemble, and resolve its counters. -/
def validateGeneration (ens : Ensemble F PublicIO) :
    Except ValidationError (ValidGeneration ens) :=
  match hvalid : validateComponents ens.tables with
  | .error error => .error error
  | .ok counters => .ok { counters, valid := hvalid }

end Air.Flat.WitnessGeneration
