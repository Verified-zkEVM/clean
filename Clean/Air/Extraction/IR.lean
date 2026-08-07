import Clean.Air.WitnessGeneration

/-!
# Typed AIR extraction program

This file is the semantic boundary between Clean and concrete backends. An extraction program is
ordinary typed Lean data: it contains structured witness programs, constraints, interactions,
component shapes, and ensemble generation modes. Backends consume this representation instead of
traversing a Clean ensemble while printing source code.

The representation deliberately reuses Clean's expression and witness IR nodes, together with
their existing Lean semantics. `WitnessBlock.wellFormed` additionally certifies that every local
reference has the sort of an earlier step. Native Lean closures are not representable.
-/

namespace Air.Flat.Extraction

open Air.Flat.WitnessGeneration

variable {F : Type} [FiniteField F] [DecidableEq F]

inductive LocalSort where
  | field
  | u64
deriving Repr, DecidableEq, BEq

private def localHasSort (locals : List LocalSort) (index : ℕ) (sort : LocalSort) : Bool :=
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

/-- One structured witness operation. Native Lean closures cannot inhabit this type. -/
structure WitnessBlock (F : Type) [FiniteField F] where
  outputWidth : ℕ
  steps : List (Witgen.Step F)
  output : Witgen.VExpr F outputWidth
  wellFormed : witnessProgramWellFormed steps output = true

namespace WitnessBlock

/-- Lean semantics for the backend-facing structured witness block. -/
def eval (block : WitnessBlock F) (environment : ProverEnvironment F) : Vector F block.outputWidth :=
  block.output.eval {
    env := environment
    locals := Witgen.evalSteps environment block.steps
  }

end WitnessBlock

/-- A backend-facing component with explicit shape and only same-row operations. -/
structure ComponentProgram (F : Type) [FiniteField F] where
  inputWidth : ℕ
  width : ℕ
  witnesses : List (WitnessBlock F)
  constraints : List (Expression F)
  interactions : List (AbstractInteraction F)

namespace ComponentProgram

private def evalWitnesses (data : ProverData F) (hint : ProverHint F) :
    List (WitnessBlock F) → Array F → Array F
  | [], row => row
  | block :: blocks, row =>
      let environment : ProverEnvironment F := {
        get index := row[index]?.getD 0
        data
        hint
      }
      evalWitnesses data hint blocks (row ++ (block.eval environment).toArray)

/-- Complete one component row according to the typed extraction semantics. -/
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

/-- Complete typed artifact consumed by source-code backends. -/
structure Program (F : Type) [FiniteField F] where
  publicInputWidth : ℕ
  components : List (ComponentProgram F)
  verifierInteractions : List (AbstractInteraction F)
  modes : List (Mode F)
  fuel : ℕ

end Air.Flat.Extraction
