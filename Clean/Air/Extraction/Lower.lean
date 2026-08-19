import Clean.Air.Extraction.IR
import Clean.Circuit.WitnessShare

/-! Structural lowering from a flat Clean ensemble to the typed extraction program. -/

namespace Air.Flat.Extraction

open Air.Flat.WitnessGeneration
open scoped Witgen

variable {F : Type} [FiniteField F]
variable {PublicIO : TypeMap} [ProvableType PublicIO]
variable {ProverInput : TypeMap} [ProvableType ProverInput]

inductive LoweringError where
  | modeCount (expected actual : ℕ)
  | paddingCount (expected actual : ℕ)
  | nativeWitness (component operation : ℕ)
  | malformedWitnessLocals (component operation : ℕ)
  | malformedFixedProgram (component : ℕ)
  | malformedInitializer (component : ℕ)
  | legacyLookup (component : ℕ)
  | fixedDemandMode (component : ℕ)
  | preallocatedWidth (component expected actual : ℕ)
  | preallocatedRows (component expected actual : ℕ)
  | fixedPadding (component expected actual : ℕ)
  | preallocatedInteraction (component interaction : ℕ)
  | preallocatedColumn (component column fixedWidth inputWidth : ℕ)
  | unknownDataRead (component operation : ℕ) (key : String)
  | dataReadWidth (component operation : ℕ) (key : String) (expected actual : ℕ)
  | unstableDataRead (component operation : ℕ) (key : String) (column : ℕ)
  | componentVariable (component index width : ℕ)
  | verifierVariable (index width : ℕ)
deriving Repr, DecidableEq

instance : ToString LoweringError where
  toString
    | .modeCount expected actual =>
        s!"generation-mode count {actual} does not match component count {expected}"
    | .paddingCount expected actual =>
        s!"padding count {actual} does not match component count {expected}"
    | .nativeWitness component operation =>
        s!"component {component} witness operation {operation} is a native Lean closure"
    | .malformedWitnessLocals component operation =>
        s!"component {component} witness operation {operation} has an invalid local reference"
    | .malformedFixedProgram component =>
        s!"component {component} fixed-column program has an invalid local reference"
    | .malformedInitializer component =>
        s!"component {component} row initializer has an invalid local reference"
    | .legacyLookup component =>
        s!"component {component} contains a legacy lookup; extraction supports channels only"
    | .fixedDemandMode component =>
        s!"fixed-column component {component} uses demand-driven generation"
    | .preallocatedWidth component expected actual =>
        s!"component {component} preallocated input suffix has width {actual}, expected {expected}"
    | .preallocatedRows component expected actual =>
        s!"component {component} has {actual} preallocated rows, expected {expected} fixed rows"
    | .fixedPadding component expected actual =>
        s!"fixed-column component {component} has height {actual}, expected {expected} after padding"
    | .preallocatedInteraction component interaction =>
        s!"component {component} preallocated handler interaction {interaction} is out of bounds"
    | .preallocatedColumn component column fixedWidth inputWidth =>
        s!"component {component} preallocated handler column {column} is outside the mutable input range [{fixedWidth}, {inputWidth})"
    | .unknownDataRead component operation key =>
        s!"component {component} witness operation {operation} reads unknown prover-data component '{key}'"
    | .dataReadWidth component operation key expected actual =>
        s!"component {component} witness operation {operation} reads prover-data component '{key}' with width {actual}, expected {expected}"
    | .unstableDataRead component operation key column =>
        s!"component {component} witness operation {operation} reads generated prover-data cell '{key}' column {column}"
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

private def lowerWitness (component operation : ℕ) {width : ℕ}
    (code : Witgen.WitgenIR F width) : Except LoweringError (WitnessBlock F) :=
  match code.shareIfSmaller with
  | .native _ => .error (.nativeWitness component operation)
  | .ir steps output =>
      if h : witnessProgramWellFormed steps output then
        .ok { outputWidth := width, steps, output, wellFormed := h }
      else
        .error (.malformedWitnessLocals component operation)

private def lowerWitnesses (component : ℕ) (operations : List (FlatOperation F)) :
    Except LoweringError (List (WitnessBlock F)) := do
  operations.zipIdx.filterMapM fun (operation, index) =>
    match operation with
    | .witness _ code => return some (← lowerWitness component index code)
    | _ => return none

private def lowerRowProgram (error : LoweringError) (program : Witgen.RowProgram F) :
    Except LoweringError (WitnessBlock F) :=
  if h : witnessProgramWellFormed program.steps program.output then
    .ok {
      outputWidth := program.width
      steps := program.steps
      output := program.output
      wellFormed := h
    }
  else
    .error error

private def lowerComponent (index : ℕ) (component : Component F) :
    Except LoweringError (ComponentProgram F) := do
  let operations := component.rowOperations
  unless operations.lookups.isEmpty do
    throw (.legacyLookup index)
  let flat := operations.toFlat
  let witnesses ← lowerWitnesses index flat
  let fixedColumns ← component.fixedColumns.mapM fun fixed => do
    let program ← lowerRowProgram (.malformedFixedProgram index) fixed.program
    return { height := fixed.height, program }
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
    fixedColumns
    width := component.width
    witnesses
    constraints
    interactions
  }

private def validateMode (index : ℕ) (component : Component F)
    (mode : Mode F) (padding : Padding F) : Except LoweringError Unit := do
  let fixedWidth := component.fixedWidth
  match component.fixedColumns, mode with
  | none, _ => pure ()
  | some _, .demand _ => throw (.fixedDemandMode index)
  | some fixed, .preallocated preallocated =>
      unless preallocated.rows = fixed.height do
        throw (.preallocatedRows index fixed.height preallocated.rows)
      let paddedHeight := padding.targetHeight preallocated.rows
      unless paddedHeight = fixed.height do
        throw (.fixedPadding index fixed.height paddedHeight)
  match mode with
  | .demand _ => pure ()
  | .preallocated preallocated =>
      let expectedWidth := component.rowOffset - fixedWidth
      unless preallocated.input.width = expectedWidth do
        throw (.preallocatedWidth index expectedWidth preallocated.input.width)
      let _ ← lowerRowProgram (.malformedInitializer index) preallocated.input
      for handler in preallocated.handlers do
        unless handler.interaction < component.rowOperations.interactions.length do
          throw (.preallocatedInteraction index handler.interaction)
        unless fixedWidth ≤ handler.column && handler.column < component.rowOffset do
          throw (.preallocatedColumn index handler.column fixedWidth component.rowOffset)

private structure DataRead where
  key : String
  width : ℕ
  column : ℕ

mutual

private def fexprDataReads : Witgen.FExpr F → List DataRead
  | .expr _ | .const _ | .index | .localVar _ => []
  | .add left right | .mul left right => fexprDataReads left ++ fexprDataReads right
  | .inv value => fexprDataReads value
  | .ofU64 value => u64exprDataReads value
  | .ite condition thenValue elseValue =>
      bexprDataReads condition ++ fexprDataReads thenValue ++ fexprDataReads elseValue
  | .listGet values index => values.flatMap fexprDataReads ++ u64exprDataReads index
  | .listGetAtIndex values => values.flatMap fexprDataReads
  | .proverInputGet index => u64exprDataReads index
  | .dataGet key width row column =>
      { key, width, column := column.val } :: u64exprDataReads row
  | .hintGet _ _ row _ => u64exprDataReads row

private def u64exprDataReads : Witgen.U64Expr F → List DataRead
  | .const _ | .idx | .localVar _ => []
  | .val value => fexprDataReads value
  | .add left right | .mul left right | .div left right | .mod left right |
      .land left right | .lor left right | .lxor left right |
      .shiftL left right | .shiftR left right => u64exprDataReads left ++ u64exprDataReads right
  | .ite condition thenValue elseValue =>
      bexprDataReads condition ++ u64exprDataReads thenValue ++ u64exprDataReads elseValue

private def bexprDataReads : Witgen.BExpr F → List DataRead
  | .true | .false => []
  | .feq left right | .flt left right => fexprDataReads left ++ fexprDataReads right
  | .neq left right | .lt left right => u64exprDataReads left ++ u64exprDataReads right
  | .bit value _ => fexprDataReads value
  | .not condition => bexprDataReads condition
  | .and left right => bexprDataReads left ++ bexprDataReads right

end

private def vexprDataReads : {n : ℕ} → Witgen.VExpr F n → List DataRead
  | _, .lit values => values.toList.flatMap fexprDataReads
  | _, .mapRange _ body => fexprDataReads body
  | _, .envRange _ => []
  | _, .bitsOf value => fexprDataReads value
  | _, .append left right => vexprDataReads left ++ vexprDataReads right

private def stepDataReads : Witgen.Step F → List DataRead
  | .letF value => fexprDataReads value
  | .letU value => u64exprDataReads value

private def witnessDataReads : {n : ℕ} → Witgen.WitgenIR F n → List DataRead
  | _, .native _ => []
  | _, .ir steps output => steps.flatMap stepDataReads ++ vexprDataReads output

private def validateDataReads (ensemble : Ensemble F PublicIO) (modes : List (Mode F)) :
    Except LoweringError Unit := do
  for (component, componentIndex) in ensemble.tables.zipIdx do
    for (operation, operationIndex) in component.rowOperations.toFlat.zipIdx do
      if let .witness _ code := operation then
        for read in witnessDataReads code do
          let some (target, mode) := (ensemble.tables.zip modes).find? fun (target, _) =>
              target.circuit.name == read.key
            | throw (.unknownDataRead componentIndex operationIndex read.key)
          unless read.width = target.rowOffset do
            throw (.dataReadWidth componentIndex operationIndex read.key target.rowOffset read.width)
          let unstable := match mode with
            | .demand _ => true
            | .preallocated preallocated =>
                preallocated.handlers.any fun handler => handler.column = read.column
          if unstable then
            throw (.unstableDataRead componentIndex operationIndex read.key read.column)

/-- Lower and validate the backend-facing portion of an ensemble without producing source text. -/
def lower (ensemble : Ensemble F PublicIO) (config : Config F ProverInput) :
    Except LoweringError (Program F) := do
  unless config.modes.length = ensemble.tables.length do
    throw (.modeCount ensemble.tables.length config.modes.length)
  unless config.padding.length = ensemble.tables.length do
    throw (.paddingCount ensemble.tables.length config.padding.length)
  for (((component, mode), padding), index) in
      ((ensemble.tables.zip config.modes).zip config.padding).zipIdx do
    validateMode index component mode padding
  validateDataReads ensemble config.modes
  let components ← ensemble.tables.zipIdx.mapM fun (component, index) =>
    lowerComponent index component
  let verifierOperations := ensemble.verifierOperations.toFlat
  let verifierInteractions := FlatOperation.interactions verifierOperations
  let verifierExpressions := verifierInteractions.flatMap fun interaction =>
    interaction.mult :: interaction.msg.toList
  match expressionsBadVariable (size PublicIO) verifierExpressions with
  | some cellIndex => throw (.verifierVariable cellIndex (size PublicIO))
  | none => pure ()
  return {
    publicInputWidth := size PublicIO
    proverInputWidth := size ProverInput
    components
    verifierInteractions
    modes := config.modes
    padding := config.padding
    fuel := config.fuel
  }

end Air.Flat.Extraction
