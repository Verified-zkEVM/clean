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

/-- A program of a component that reads prover data. -/
inductive DataReader where
  /-- The witness program of the component's operation at this index. -/
  | witness (operation : ℕ)
  /-- The guard of the component's demand mode. -/
  | guard
deriving Repr, DecidableEq

instance : ToString DataReader where
  toString
    | .witness operation => s!"witness operation {operation}"
    | .guard => "guard"

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
  | unguardedHandler (component channel : String) (trigger : Direction)
  | unknownDataRead (component : String) (reader : DataReader) (key : String)
  | dataReadWidth (component : String) (reader : DataReader) (key : String) (expected actual : ℕ)
  | unstableDataRead (component : String) (reader : DataReader) (key : String) (column : ℕ)
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
        s!"component '{component}' aggregates by message, so it can only answer unmatched pulls"
    | .byMessageChannel component counted demanded =>
        s!"component '{component}' counts on channel '{counted}' but answers demand on channel \
          '{demanded}'"
    | .unguardedHandler component channel trigger =>
        s!"component '{component}' is triggered by unmatched {trigger.name} interactions on \
          channel '{channel}' without a guard, but other components are too"
    | .unknownDataRead component reader key =>
        s!"component '{component}' {reader} reads unknown prover-data component '{key}'"
    | .dataReadWidth component reader key expected actual =>
        s!"component '{component}' {reader} reads prover-data component '{key}' with width \
          {actual}, expected {expected}"
    | .unstableDataRead component reader key column =>
        s!"component '{component}' {reader} reads cell {column} of '{key}', which generation \
          changes"

/-! ### Prover-data reads

TODO. Witness programs read prover data from a snapshot of the rows initialized before channel
balancing, which only agrees with the final prover data on cells that balancing doesn't change. So
for now, reads of witness programs and guards are restricted to such cells: the non-counter cells
of preallocated components. -/

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

/-- A channel and the unmatched interactions on it that a component answers. -/
structure Handler where
  channel : String
  trigger : Direction
  /-- Whether the component answers only some messages: those its guard holds for, or, for a
  preallocated component, those it has a row for. -/
  selective : Bool

/-- The channels a component answers demand on. A counter only grows the pushes of its interaction,
so it answers unmatched pulls. -/
def handlers (component : Component F) (counters : List Counter) : List Handler :=
  match component.generation with
  | .demand mode =>
      [{ channel := mode.channel.name, trigger := mode.trigger, selective := mode.guard.isSome }]
  | .preallocated _ =>
      counters.map fun counter =>
        { channel := counter.channel, trigger := .pull, selective := true }

/-- The programs of a component that read prover data, with their reads. -/
def dataReaders (component : Component F) : List (DataReader × List DataRead) :=
  let witnesses := component.rowOperations.toFlat.zipIdx.filterMap fun (operation, index) =>
    match operation with
    | .witness _ code => some (.witness index, witnessDataReads code)
    | _ => none
  let guard := match component.generation with
    | .demand mode => (mode.guardCondition.map fun guard => (.guard, bexprDataReads guard)).toList
    | .preallocated _ => []
  witnesses ++ guard

/-- Check a component's generation against the component, and resolve its counters. -/
def validateComponent (component : Component F) : Except ValidationError (List Counter) := do
  let name := component.circuit.name
  let fixedWidth := component.fixedWidth
  let inputWidth := component.rowOffset
  let counters ← (resolveCounters component).mapError (.counter name)
  match component.generation with
  | .demand mode =>
      if let .byMessage _ := mode.aggregation then
        if mode.trigger == .push then throw (.byMessagePush name)
        for counter in counters do
          unless counter.channel == mode.channel.name do
            throw (.byMessageChannel name counter.channel mode.channel.name)
      unless mode.input.length + counters.length = inputWidth do
        throw (.demandInputWidth name (inputWidth - counters.length) mode.input.length)
      for cell in mode.input do
        if let .message index := cell then
          unless index < size mode.Message do
            throw (.demandMessageIndex name index (size mode.Message))
      unless mode.padding.size = inputWidth do
        throw (.paddingWidth name inputWidth mode.padding.size)
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
    let name := component.circuit.name
    for (reader, reads) in dataReaders component do
      for read in reads do
        let some (target, targetCounters) := targets.find? fun (target, _) =>
            target.circuit.name == read.key
          | throw (.unknownDataRead name reader read.key)
        unless read.width = target.rowOffset do
          throw (.dataReadWidth name reader read.key target.rowOffset read.width)
        match target.generation with
        | .demand _ => throw (.unstableDataRead name reader read.key read.column)
        | .preallocated _ =>
            if targetCounters.any (·.column = read.column) then
              throw (.unstableDataRead name reader read.key read.column)

/-- Check that a component without a guard is the only one with its channel and trigger. Whether
selective components overlap is only found out during generation, when two of them accept the same
message. -/
def validateHandlers (components : List (Component F)) (counters : List (List Counter)) :
    Except ValidationError Unit := do
  let handled := (components.zip counters).flatMap fun (component, counters) =>
    (handlers component counters).map (component.circuit.name, ·)
  for (name, handler) in handled do
    let shared := handled.filter fun (_, other) =>
      other.channel == handler.channel && other.trigger == handler.trigger
    unless handler.selective || shared.length ≤ 1 do
      throw (.unguardedHandler name handler.channel handler.trigger)

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
