module

public import Clean.Air.WitnessGeneration

@[expose] public section

/-!
# Extraction programs

An extraction program is the form of an AIR ensemble that source-code backends print: witness
programs, constraints, interactions, component shapes, and generation modes. `lower` validates an
ensemble and produces it.

A two-row component's constraints read the next row's input from the window cells of its rows, and
use the selectors only as gates: a constraint that reads a selector is the selector times a
constraint that reads none, which a backend checks on the rows the selector marks. This is how
Plonky3 uses its selectors, which are only 0 or 1 up to a nonzero factor.

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

/-- The rows a constraint is checked on: every row, or the rows one of the selectors marks. -/
inductive Gate where
  | everyRow
  | firstRow
  | lastRow
  | transition
deriving Repr, DecidableEq

/-- A constraint, split into its gate and a body that reads no selector. -/
structure GatedConstraint (F : Type) where
  gate : Gate
  body : Expression F

structure ComponentProgram (F : Type) [FiniteField F] where
  name : String
  inputWidth : ℕ
  /-- For a two-row component, the width of the row's own input: cells `[w, 2w)` of a row hold the
  next row's first `w` cells, and cells `2w`, `2w + 1` and `2w + 2` the selectors `isFirstRow`,
  `isLastRow` and `isTransition`. A backend reads these cells from the next row and from its
  selectors instead of committing them. -/
  window : Option ℕ
  width : ℕ
  witnesses : List (WitnessBlock F)
  constraints : List (GatedConstraint F)
  interactions : List (AbstractInteraction F)

/-- A `DemandMode`. -/
structure DemandProgram (F : Type) [FiniteField F] where
  channel : String
  trigger : Interaction.Direction
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
  | preallocated (channel : String) (trigger : Interaction.Direction) (rows : UInt64) (input : InputProgram F)
      (multiplicity : MultiplicityColumn)
  /-- `rows` rows, whose inputs are `input` at the row index, which answer no demand. -/
  | standalone (rows : UInt64) (input : InputProgram F)

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
  | noComponents
  | nativeWitness (component operation : ℕ)
  | malformedWitnessLocals (component operation : ℕ)
  | malformedInputProgram (component : ℕ)
  | malformedGuard (component : ℕ)
  | legacyLookup (component : ℕ)
  | componentVariable (component index width : ℕ)
  | verifierVariable (index width : ℕ)
  | ungatedSelector (component constraint : ℕ)
  | segmentGeneration (component : ℕ)
deriving Repr, DecidableEq

instance : ToString LoweringError where
  toString
    | .validation error => toString error
    | .noComponents => "the ensemble has no components"
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
    | .ungatedSelector component constraint =>
        s!"component {component} constraint {constraint} reads a selector, but is not the \
          selector times a constraint that reads none"
    | .segmentGeneration component =>
        s!"component {component} is generated by a segment program, which extraction doesn't \
          support"

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

/-- The selector cell of a gate, for a two-row component whose own input has width `width`. -/
def Gate.selectorCell (width : ℕ) : Gate → Option ℕ
  | .everyRow => none
  | .firstRow => some (2 * width)
  | .lastRow => some (2 * width + 1)
  | .transition => some (2 * width + 2)

/-- The gate of a selector cell, for a two-row component whose own input has width `width`. -/
def selectorGate? (width : ℕ) : Expression F → Option Gate
  | .var cell =>
      if cell.index = 2 * width then some .firstRow
      else if cell.index = 2 * width + 1 then some .lastRow
      else if cell.index = 2 * width + 2 then some .transition
      else none
  | _ => none

/-- Split a selector factor off a product, keeping the shape of the other factors. -/
def splitSelector (width : ℕ) : Expression F → Option (Gate × Expression F)
  | .mul left right =>
      match selectorGate? width left, selectorGate? width right with
      | some gate, _ => some (gate, right)
      | none, some gate => some (gate, left)
      | none, none =>
          match splitSelector width left with
          | some (gate, left) => some (gate, .mul left right)
          | none => (splitSelector width right).map fun (gate, right) => (gate, .mul left right)
  | _ => none

/-- Split a constraint into its gate and a body that reads no selector: either it reads no selector,
or it is a product with a selector factor. -/
def gateConstraint (window : Option ℕ) (constraint : Expression F) :
    Option (GatedConstraint F) :=
  match window with
  | none => some { gate := .everyRow, body := constraint }
  | some width =>
      let readsSelector (expression : Expression F) := (expressionCells expression).any
        fun cell => 2 * width ≤ cell && cell < 2 * width + 3
      if !readsSelector constraint then some { gate := .everyRow, body := constraint }
      else do
        let (gate, body) ← splitSelector width constraint
        if readsSelector body then none else some { gate, body }

lemma selectorGate?_eq_some {F : Type} {width : ℕ} {expression : Expression F} {gate : Gate}
    (h : selectorGate? width expression = some gate) :
    ∃ cell, gate.selectorCell width = some cell ∧ expression = .var ⟨cell⟩ := by
  match expression with
  | .var ⟨index⟩ =>
    simp only [selectorGate?] at h
    split_ifs at h <;> cases h <;> simp_all [Gate.selectorCell]
  | .const _ | .add _ _ | .mul _ _ => simp [selectorGate?] at h

/-- A split constraint is its selector times its body. -/
theorem eval_of_splitSelector {width : ℕ} {expression body : Expression F} {gate : Gate}
    (env : Environment F) (h : splitSelector width expression = some (gate, body)) :
    ∃ cell, gate.selectorCell width = some cell ∧
      expression.eval env = env.get cell * body.eval env := by
  induction expression generalizing gate body with
  | var _ | const _ | add _ _ => simp [splitSelector] at h
  | mul left right ihLeft ihRight =>
    simp only [splitSelector] at h
    split at h
    · rename_i hleft
      obtain ⟨cell, hcell, rfl⟩ := selectorGate?_eq_some hleft
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨cell, hcell, rfl⟩
    · rename_i hright
      obtain ⟨cell, hcell, rfl⟩ := selectorGate?_eq_some hright
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨cell, hcell, by simp only [Expression.eval]; ring⟩
    · split at h
      · rename_i hsplit
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨cell, hcell, heval⟩ := ihLeft hsplit
        exact ⟨cell, hcell, by simp only [Expression.eval, heval]; ring⟩
      · obtain ⟨⟨gate', right'⟩, hsplit, heq⟩ := Option.map_eq_some_iff.mp h
        simp only [Prod.mk.injEq] at heq
        obtain ⟨rfl, rfl⟩ := heq
        obtain ⟨cell, hcell, heval⟩ := ihRight hsplit
        exact ⟨cell, hcell, by simp only [Expression.eval, heval]; ring⟩

/-- Whether the constraints of a component hold on a complete row: each body, times the selector of
its gate. -/
def ComponentProgram.constraintsHold (component : ComponentProgram F) (row : Array F)
    (data : ProverData F) : Bool :=
  let environment := Environment.fromArray row data
  let width := component.window.getD 0
  component.constraints.all fun constraint =>
    let gate := (constraint.gate.selectorCell width).elim 1 environment.get
    gate * constraint.body.eval environment == 0

def lowerConstraints (component : ℕ) (window : Option ℕ) (constraints : List (Expression F)) :
    Except LoweringError (List (GatedConstraint F)) :=
  constraints.zipIdx.mapM fun (constraint, index) =>
    match gateConstraint window constraint with
    | some gated => .ok gated
    | none => .error (.ungatedSelector component index)

def lowerComponent (index : ℕ) (component : Component F) :
    Except LoweringError (ComponentProgram F) := do
  let operations := component.rowOperations
  unless operations.lookups.isEmpty do
    throw (.legacyLookup index)
  let flat := operations.toFlat
  let witnesses ← lowerWitnesses index flat
  let window := component.window.map (·.rowWidth)
  let constraints ← lowerConstraints index window operations.constraints
  let interactions := operations.interactions
  let expressions := operations.constraints ++ interactions.flatMap fun interaction =>
    interaction.mult :: interaction.msg.toList
  match expressionsBadVariable component.width expressions with
  | some cellIndex => throw (.componentVariable index cellIndex component.width)
  | none => pure ()
  return {
    name := component.circuit.name
    inputWidth := component.rowOffset
    window
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
  | .standalone mode, _ => return .standalone mode.height input
  | .segments _, _ => throw (.segmentGeneration index)

/-- Validate the generation of an ensemble, and lower it to an extraction program. `fuel` bounds the
number of witness generation steps. -/
def lower (ensemble : Ensemble F PublicIO) (fuel : ℕ) : Except LoweringError (Program F) := do
  if ensemble.tables.isEmpty then throw .noComponents
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
