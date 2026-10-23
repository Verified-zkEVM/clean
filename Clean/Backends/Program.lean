module

public import Clean.Air.WitnessGeneration

@[expose] public section

/-!
# Extraction programs

An extraction program is the form of a flat AIR ensemble that source-code backends print: witness
programs, constraints, interactions, component shapes, and generation modes. `lower` validates an
ensemble and produces it.

The representation reuses Clean's expression and witness IR nodes, together with their Lean
semantics.
-/

namespace Backends

open Air.Flat
open Air.Flat.WitnessGeneration

variable {F : Type} [FiniteField F]
variable {PublicIO : TypeMap} [ProvableType PublicIO]

inductive LocalSort where
  | field
  | u64
deriving Repr, DecidableEq, BEq

def localHasSort (locals : List LocalSort) (index : ℕ) (sort : LocalSort) : Bool :=
  locals[index]? == some sort

mutual

def fexprWellFormed (locals : List LocalSort) : Witgen.FExpr F → Bool
  | .expr _ | .const _ => true
  | .localVar index => localHasSort locals index .field
  | .add left right | .mul left right =>
      fexprWellFormed locals left && fexprWellFormed locals right
  | .inv value => fexprWellFormed locals value
  | .ofU64 value => u64exprWellFormed locals value
  | .ite condition thenValue elseValue =>
      bexprWellFormed locals condition && fexprWellFormed locals thenValue &&
        fexprWellFormed locals elseValue
  | .listGet values index =>
      fexprListWellFormed locals values && u64exprWellFormed locals index
  | .dataGet _ _ row _ | .hintGet _ _ row _ => u64exprWellFormed locals row

def fexprListWellFormed (locals : List LocalSort) : List (Witgen.FExpr F) → Bool
  | [] => true
  | value :: values => fexprWellFormed locals value && fexprListWellFormed locals values

def u64exprWellFormed (locals : List LocalSort) : Witgen.U64Expr F → Bool
  | .const _ | .idx => true
  | .localVar index => localHasSort locals index .u64
  | .val value => fexprWellFormed locals value
  | .add left right | .mul left right | .div left right | .mod left right |
      .land left right | .lor left right | .lxor left right |
      .shiftL left right | .shiftR left right =>
        u64exprWellFormed locals left && u64exprWellFormed locals right
  | .ite condition thenValue elseValue =>
      bexprWellFormed locals condition && u64exprWellFormed locals thenValue &&
        u64exprWellFormed locals elseValue

def bexprWellFormed (locals : List LocalSort) : Witgen.BExpr F → Bool
  | .true | .false => true
  | .feq left right | .flt left right =>
      fexprWellFormed locals left && fexprWellFormed locals right
  | .neq left right | .lt left right =>
      u64exprWellFormed locals left && u64exprWellFormed locals right
  | .bit value _ => fexprWellFormed locals value
  | .not condition => bexprWellFormed locals condition
  | .and left right => bexprWellFormed locals left && bexprWellFormed locals right

end

def vexprWellFormed (locals : List LocalSort) : {n : ℕ} → Witgen.VExpr F n → Bool
  | _, .lit values => values.toList.all (fexprWellFormed locals)
  | _, .mapRange _ body => fexprWellFormed locals body
  | _, .envRange _ => true
  | _, .bitsOf value => fexprWellFormed locals value
  | _, .append left right => vexprWellFormed locals left && vexprWellFormed locals right

def appendStepSort (locals : List LocalSort) : Witgen.Step F → List LocalSort
  | .letF _ => locals ++ [.field]
  | .letU _ => locals ++ [.u64]

def stepsWellFormedFrom : List LocalSort → List (Witgen.Step F) → Bool
  | _, [] => true
  | locals, .letF value :: steps =>
      fexprWellFormed locals value && stepsWellFormedFrom (locals ++ [.field]) steps
  | locals, .letU value :: steps =>
      u64exprWellFormed locals value && stepsWellFormedFrom (locals ++ [.u64]) steps

def stepSorts (initial : List LocalSort) (steps : List (Witgen.Step F)) : List LocalSort :=
  steps.foldl appendStepSort initial

def witnessProgramWellFormed {n : ℕ} (steps : List (Witgen.Step F))
    (output : Witgen.VExpr F n) : Bool :=
  stepsWellFormedFrom [] steps && vexprWellFormed (stepSorts [] steps) output

/-- A witness program, whose local references all have the sort of an earlier step. -/
structure WitnessBlock (F : Type) [FiniteField F] where
  outputWidth : ℕ
  steps : List (Witgen.Step F)
  output : Witgen.VExpr F outputWidth
  well_formed : witnessProgramWellFormed steps output = true

namespace WitnessBlock

def eval (block : WitnessBlock F) (environment : ProverEnvironment F)
    (row : ℕ := 0) : Vector F block.outputWidth :=
  block.output.eval {
    env := environment
    locals := Witgen.evalSteps environment block.steps #[] row
    idx := row
  }

end WitnessBlock

def cellWellFormed (locals : List LocalSort) : Cell F → Bool
  | .fixed value | .witness value => fexprWellFormed locals value
  | .multiplicity => true

/-- The input program of a generation mode: its `let`-steps, and its input cells. -/
structure InputProgram (F : Type) [FiniteField F] where
  steps : List (Witgen.Step F)
  cells : List (Cell F)
  well_formed :
    (stepsWellFormedFrom [] steps && cells.all (cellWellFormed (stepSorts [] steps))) = true

/-- The input columns of the fixed cells. -/
def InputProgram.fixedColumns (input : InputProgram F) : List ℕ :=
  (input.cells.zipIdx.filter (·.1.isFixed)).map (·.2)

structure ComponentProgram (F : Type) [FiniteField F] where
  name : String
  inputWidth : ℕ
  width : ℕ
  witnesses : List (WitnessBlock F)
  constraints : List (Expression F)
  interactions : List (AbstractInteraction F)

namespace ComponentProgram

def evalWitnesses (data : ProverData F) (hint : ProverHint F) :
    List (WitnessBlock F) → Array F → Array F
  | [], row => row
  | block :: blocks, row =>
      let environment : ProverEnvironment F := {
        get index := row[index]?.getD 0
        data
        hint
      }
      evalWitnesses data hint blocks (row ++ (block.eval environment).toArray)

/-- Complete a component row from its input. -/
def completeRow (component : ComponentProgram F) (input : Array F)
    (data : ProverData F) (hint : ProverHint F := .empty F) : Except String (Array F) := do
  unless input.size = component.inputWidth do
    throw s!"component input has width {input.size}, expected {component.inputWidth}"
  let row := evalWitnesses data hint component.witnesses input
  unless row.size = component.width do
    throw s!"generated row has width {row.size}, expected {component.width}"
  return row

def constraintsHold (component : ComponentProgram F) (row : Array F)
    (data : ProverData F) : Bool :=
  let environment := Environment.fromArray row data
  component.constraints.all fun constraint => constraint.eval environment == 0

def interactionValues (component : ComponentProgram F) (row : Array F)
    (data : ProverData F) : List (Interaction F) :=
  let environment := Environment.fromArray row data
  component.interactions.map (·.eval environment)

end ComponentProgram

/-- A `DemandMode`. -/
structure DemandProgram (F : Type) [FiniteField F] where
  channel : String
  trigger : Direction
  /-- The guard, as a condition on the message cells. -/
  guard : Witgen.BExpr F
  /-- The input of a new row, reading the message cells. -/
  input : InputProgram F
  multiplicity : Option MultiplicityColumn
  padding : Array F

/-- How the rows of one component are generated. -/
inductive ModeProgram (F : Type) [FiniteField F] where
  | demand (mode : DemandProgram F)
  /-- `rows` rows, whose inputs are `input` at the row index, with multiplicity 0. -/
  | preallocated (channel : String) (trigger : Direction) (rows : UInt64) (input : InputProgram F)
      (multiplicity : MultiplicityColumn)

/-- An ensemble in the form that source-code backends print. -/
structure Program (F : Type) [FiniteField F] where
  publicInputWidth : ℕ
  proverInputWidth : ℕ
  hintTables : List HintTable
  components : List (ComponentProgram F)
  verifierInteractions : List (AbstractInteraction F)
  modes : List (ModeProgram F)
  fuel : ℕ

/-! ## Lowering a flat Clean ensemble to an extraction program -/

inductive LoweringError where
  | validation (error : ValidationError)
  | nativeWitness (component operation : ℕ)
  | malformedWitnessLocals (component operation : ℕ)
  | malformedInputProgram (component : ℕ)
  | malformedGuard (component : ℕ)
  | legacyLookup (component : ℕ)
  | componentVariable (component index width : ℕ)
  | verifierVariable (index width : ℕ)
deriving Repr, DecidableEq

instance : ToString LoweringError where
  toString
    | .validation error => toString error
    | .nativeWitness component operation =>
        s!"component {component} witness operation {operation} is a native Lean closure"
    | .malformedWitnessLocals component operation =>
        s!"component {component} witness operation {operation} has an invalid local reference"
    | .malformedInputProgram component =>
        s!"component {component} input program has an invalid local reference"
    | .malformedGuard component =>
        s!"component {component} guard has an invalid local reference"
    | .legacyLookup component =>
        s!"component {component} contains a legacy lookup; extraction supports channels only"
    | .componentVariable component index width =>
        s!"component {component} expression reads cell {index}, but its width is {width}"
    | .verifierVariable index width =>
        s!"verifier interaction reads public cell {index}, but the public input width is {width}"

def expressionBadVariable (width : ℕ) : Expression F → Option ℕ
  | .var cell => if cell.index < width then none else some cell.index
  | .const _ => none
  | .add left right | .mul left right =>
      expressionBadVariable width left |>.orElse (fun _ => expressionBadVariable width right)

def expressionsBadVariable (width : ℕ) (expressions : List (Expression F)) : Option ℕ :=
  expressions.findSome? (expressionBadVariable width)

def lowerWitness (component operation : ℕ) {width : ℕ}
    (code : Witgen.WitgenIR F width) : Except LoweringError (WitnessBlock F) :=
  match code with
  | .native _ => .error (.nativeWitness component operation)
  | .ir steps output =>
      if h : witnessProgramWellFormed steps output then
        .ok { outputWidth := width, steps, output, well_formed := h }
      else
        .error (.malformedWitnessLocals component operation)

def lowerWitnesses (component : ℕ) (operations : List (FlatOperation F)) :
    Except LoweringError (List (WitnessBlock F)) := do
  operations.zipIdx.filterMapM fun (operation, index) =>
    match operation with
    | .witness _ code => return some (← lowerWitness component index code)
    | _ => return none

def lowerInputProgram {Input : TypeMap} [ProvableType Input] (index : ℕ)
    (cells : Vector (Cell F) (size Input)) (steps : List (Witgen.Step F)) :
    Except LoweringError (InputProgram F) :=
  let cells := cells.toList
  if h : (stepsWellFormedFrom [] steps && cells.all (cellWellFormed (stepSorts [] steps))) = true
  then .ok { steps, cells, well_formed := h }
  else .error (.malformedInputProgram index)

def lowerComponent (index : ℕ) (component : Component F) :
    Except LoweringError (ComponentProgram F) := do
  let operations := component.rowOperations
  unless operations.lookups.isEmpty do
    throw (.legacyLookup index)
  let flat := operations.toFlat
  let witnesses ← lowerWitnesses index flat
  let constraints := operations.constraints
  let interactions := operations.interactions
  let expressions := constraints ++ interactions.flatMap fun interaction =>
    interaction.mult :: interaction.msg.toList
  match expressionsBadVariable component.width expressions with
  | some cellIndex => throw (.componentVariable index cellIndex component.width)
  | none => pure ()
  return {
    name := component.circuit.name
    inputWidth := component.rowOffset
    width := component.width
    witnesses
    constraints
    interactions
  }

def lowerGeneration (index : ℕ) (component : Component F)
    (multiplicity : Option MultiplicityColumn) : Except LoweringError (ModeProgram F) := do
  let (cells, steps) := component.generation.cells
  let input ← lowerInputProgram index cells steps
  match component.generation, multiplicity with
  | .demand mode, multiplicity =>
      let guard := mode.guardCondition
      unless bexprWellFormed [] guard do
        throw (.malformedGuard index)
      let { channel, trigger, padding, .. } := mode
      return .demand {
        channel := channel.name, trigger, guard, input, multiplicity
        padding := (toElements padding).toArray }
  | .preallocated mode, some multiplicity =>
      return .preallocated mode.channel.name mode.trigger mode.height input multiplicity
  | .preallocated _, none =>
      throw (.validation (.multiplicity component.circuit.name (.cells 0)))

/-- Validate the generation of an ensemble, and lower it to an extraction program. `fuel` bounds the
number of witness generation steps. -/
def lower (ensemble : Ensemble F PublicIO) (fuel : ℕ) : Except LoweringError (Program F) := do
  match validateGeneration ensemble with
  | .error error => throw (.validation error)
  | .ok valid =>
    let components ← ensemble.tables.zipIdx.mapM fun (component, index) =>
      lowerComponent index component
    let modes ← (ensemble.tables.zip valid.multiplicities).zipIdx.mapM
      fun ((component, multiplicity), index) => lowerGeneration index component multiplicity
    let verifierOperations := ensemble.verifierOperations.toFlat
    let verifierInteractions := FlatOperation.interactions verifierOperations
    let verifierExpressions := verifierInteractions.flatMap fun interaction =>
      interaction.mult :: interaction.msg.toList
    match expressionsBadVariable (size PublicIO) verifierExpressions with
    | some cellIndex => throw (.verifierVariable cellIndex (size PublicIO))
    | none => pure ()
    return {
      publicInputWidth := size PublicIO
      proverInputWidth := size ensemble.ProverInput
      hintTables := ensemble.hintTables
      components
      verifierInteractions
      modes
      fuel
    }

end Backends
