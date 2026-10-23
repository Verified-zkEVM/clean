module

public import Clean.Air.WitnessGeneration.Multiplicity

@[expose] public section

/-!
# Validating the generation of an ensemble

TODO. Generation starts with `validateGeneration`, which rejects component generations
that don't fit their components, for example a multiplicity cell that isn't the multiplicity of an
interaction. Most of these checks should become types or proof obligations of the generation
instead.
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
  /-- The input program of the component's demand mode. -/
  | input
deriving Repr, DecidableEq

instance : ToString DataReader where
  toString
    | .witness operation => s!"witness operation {operation}"
    | .guard => "guard"
    | .input => "demand input"

/-- A problem with the generation of an ensemble, found by `validateGeneration`. -/
inductive ValidationError where
  | preallocatedHeight (component : String) (height : ℕ)
  | rowProgram (component : String)
  | demandFixedCell (component : String)
  | multiplicity (component : String) (error : MultiplicityError)
  | unguardedHandler (component channel : String) (trigger : Direction)
  | unknownDataRead (component : String) (reader : DataReader) (key : String)
  | dataReadWidth (component : String) (reader : DataReader) (key : String) (expected actual : ℕ)
  | unstableDataRead (component : String) (reader : DataReader) (key : String) (column : ℕ)
deriving Repr, DecidableEq

instance : ToString ValidationError where
  toString
    | .preallocatedHeight component height =>
        s!"preallocated component '{component}' has {height} rows, which is not a power of two"
    | .rowProgram component =>
        s!"input program of preallocated component '{component}' reads prover data, or reads the \
          hint outside of witness cells"
    | .demandFixedCell component =>
        s!"demand input of component '{component}' has a fixed cell"
    | .multiplicity component error => s!"component '{component}' {error}"
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
for now, reads of witness programs, guards and demand inputs are restricted to such cells: the
non-multiplicity cells of preallocated components. -/

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

/-- The demand a component answers. A preallocated component answers both directions on its
channel, with its multiplicity cell. -/
def handlers (component : Component F) : List Handler :=
  match component.generation with
  | .demand mode =>
      let selective := match mode.guardCondition with
        | .true => false
        | _ => true
      [{ channel := mode.channel.name, trigger := mode.trigger, selective }]
  | .preallocated mode =>
      [.pull, .push].map fun trigger => { channel := mode.channel.name, trigger, selective := true }

def cellDataReads : Cell F → List DataRead
  | .fixed value | .witness value => fexprDataReads value
  | .multiplicity => []

/-- The programs of a component that read prover data, with their reads. -/
def dataReaders (component : Component F) : List (DataReader × List DataRead) :=
  let witnesses := component.rowOperations.toFlat.zipIdx.filterMap fun (operation, index) =>
    match operation with
    | .witness _ code => some (.witness index, witnessDataReads code)
    | _ => none
  let demand := match component.generation with
    | .demand mode =>
        let (cells, steps) := component.generation.cells
        [(.guard, bexprDataReads mode.guardCondition),
          (.input, steps.flatMap stepDataReads ++ cells.toList.flatMap cellDataReads)]
    | .preallocated _ => []
  witnesses ++ demand

/-- Whether the input program of a preallocated row is computed from the row index, except for its
witness cells, which may also read the hint. -/
def rowProgramValid (steps : List (Witgen.Step F)) (cells : List (Cell F)) : Bool :=
  steps.all (·.validForRow .fixed) && cells.all fun
    | .fixed value => value.validForRow .fixed
    | .witness value => value.validForRow .prover
    | .multiplicity => true

/-- Check a component's generation against the component, and resolve its multiplicity cell. -/
def validateComponent (component : Component F) :
    Except ValidationError (Option MultiplicityColumn) := do
  let name := component.circuit.name
  let multiplicity ← (resolveMultiplicity component).mapError (.multiplicity name)
  let (cells, steps) := component.generation.cells
  match component.generation with
  | .demand mode =>
      if cells.toList.any (·.isFixed) then throw (.demandFixedCell name)
  | .preallocated mode =>
      let height := mode.height.toNat
      unless nextPowerOfTwo height = height do
        throw (.preallocatedHeight name height)
      unless rowProgramValid steps cells.toList do
        throw (.rowProgram name)
  return multiplicity

/-- Check that every prover-data read targets a cell of a preallocated component that generation
doesn't change. -/
def validateDataReads (components : List (Component F))
    (multiplicities : List (Option MultiplicityColumn)) : Except ValidationError Unit := do
  let targets := components.zip multiplicities
  for component in components do
    let name := component.circuit.name
    for (reader, reads) in dataReaders component do
      for read in reads do
        let some (target, targetMultiplicity) := targets.find? fun (target, _) =>
            target.circuit.name == read.key
          | throw (.unknownDataRead name reader read.key)
        unless read.width = target.rowOffset do
          throw (.dataReadWidth name reader read.key target.rowOffset read.width)
        match target.generation with
        | .demand _ => throw (.unstableDataRead name reader read.key read.column)
        | .preallocated _ =>
            if targetMultiplicity.any (·.column = read.column) then
              throw (.unstableDataRead name reader read.key read.column)

/-- Check that a component whose guard is `true` is the only one with its channel and trigger.
Whether selective components overlap is only found out during generation, when two of them accept
the same message. -/
def validateHandlers (components : List (Component F)) : Except ValidationError Unit := do
  let handled := components.flatMap fun component =>
    (handlers component).map (component.circuit.name, ·)
  for (name, handler) in handled do
    let shared := handled.filter fun (_, other) =>
      other.channel == handler.channel && other.trigger == handler.trigger
    unless handler.selective || shared.length ≤ 1 do
      throw (.unguardedHandler name handler.channel handler.trigger)

/-- All checks of the components' generations; returns the multiplicity cell of every component. -/
def validateComponents (components : List (Component F)) :
    Except ValidationError (List (Option MultiplicityColumn)) := do
  let multiplicities ← components.mapM validateComponent
  validateHandlers components
  validateDataReads components multiplicities
  return multiplicities

/-- An ensemble whose generation passed `validateGeneration`, with the multiplicity cell of every
component, in ensemble order. -/
structure ValidGeneration (ens : Ensemble F PublicIO) where
  multiplicities : List (Option MultiplicityColumn)
  valid : validateComponents ens.tables = .ok multiplicities

/-- Check the generation of every component of an ensemble, and resolve its multiplicity cell. -/
def validateGeneration (ens : Ensemble F PublicIO) :
    Except ValidationError (ValidGeneration ens) :=
  match hvalid : validateComponents ens.tables with
  | .error error => .error error
  | .ok multiplicities => .ok { multiplicities, valid := hvalid }

end Air.Flat.WitnessGeneration
