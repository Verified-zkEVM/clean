import Clean.Air.WitnessGeneration
import Clean.Circuit.WitnessExport

/-!
# Ensemble witness-generation export

This is the backend-independent build artifact for channel-driven ensemble witness
generation. It contains generation modes plus the structured row-local Witgen programs
and interactions for every component. JSON is a transport format for code generation;
it is not intended to be interpreted in the proving hot path.
-/

open Lean

namespace Air.Flat.WitnessGeneration

variable {F : Type} [FiniteField F] [DecidableEq F] [ToJson F]
variable {PublicIO : TypeMap} [ProvableType PublicIO]

namespace Export

def directionToJson : Direction → Json
  | .pull => "pull"
  | .push => "push"

def aggregationToJson : Aggregation → Json
  | .perOccurrence => "perOccurrence"
  | .byMessage => "byMessage"

def inputCellToJson : InputCell F → Json
  | .message index => Json.mkObj [
      ("type", "message"),
      ("index", toJson index)]
  | .multiplicity => Json.mkObj [("type", "multiplicity")]
  | .const value => Json.mkObj [
      ("type", "const"),
      ("value", toJson value)]

def inputTemplateToJson (template : InputTemplate F) : Json :=
  Json.arr (template.cells.map inputCellToJson).toArray

def fixedSlotToJson (slot : FixedSlot F) : Json := Json.mkObj [
  ("channel", slot.channel),
  ("direction", directionToJson slot.direction),
  ("message", toJson slot.message),
  ("row", toJson slot.row),
  ("column", toJson slot.column)]

def modeToJson : Mode F → Json
  | .demand mode => Json.mkObj [
      ("type", "demand"),
      ("channel", mode.channel),
      ("direction", directionToJson mode.direction),
      ("aggregation", aggregationToJson mode.aggregation),
      ("input", inputTemplateToJson mode.input)]
  | .fixed inputRows slots => Json.mkObj [
      ("type", "fixed"),
      ("inputRows", toJson inputRows),
      ("slots", Json.arr (slots.map fixedSlotToJson).toArray)]

mutual

partial def fexprUsesExternalData : Witgen.FExpr F → Bool
  | .expr _ | .const _ | .localVar _ => false
  | .add left right | .mul left right =>
      fexprUsesExternalData left || fexprUsesExternalData right
  | .inv value => fexprUsesExternalData value
  | .ofU64 value => u64UsesExternalData value
  | .ite condition thenValue elseValue =>
      bexprUsesExternalData condition || fexprUsesExternalData thenValue ||
        fexprUsesExternalData elseValue
  | .listGet values index =>
      values.any fexprUsesExternalData || u64UsesExternalData index
  | .dataGet _ _ _ _ | .hintGet _ _ _ _ => true

partial def u64UsesExternalData : Witgen.U64Expr F → Bool
  | .const _ | .idx | .localVar _ => false
  | .val value => fexprUsesExternalData value
  | .add left right | .mul left right | .div left right | .mod left right |
      .land left right | .lor left right | .lxor left right |
      .shiftL left right | .shiftR left right =>
        u64UsesExternalData left || u64UsesExternalData right
  | .ite condition thenValue elseValue =>
      bexprUsesExternalData condition || u64UsesExternalData thenValue ||
        u64UsesExternalData elseValue

partial def bexprUsesExternalData : Witgen.BExpr F → Bool
  | .true | .false => false
  | .feq left right | .flt left right =>
      fexprUsesExternalData left || fexprUsesExternalData right
  | .neq left right | .lt left right =>
      u64UsesExternalData left || u64UsesExternalData right
  | .bit value _ => fexprUsesExternalData value
  | .not condition => bexprUsesExternalData condition
  | .and left right => bexprUsesExternalData left || bexprUsesExternalData right

end

def vexprUsesExternalData : {n : ℕ} → Witgen.VExpr F n → Bool
  | _, .lit values => values.toList.any fexprUsesExternalData
  | _, .mapRange _ body => fexprUsesExternalData body
  | _, .envRange _ => false
  | _, .bitsOf value => fexprUsesExternalData value
  | _, .append left right => vexprUsesExternalData left || vexprUsesExternalData right

def stepUsesExternalData : Witgen.Step F → Bool
  | .letF value => fexprUsesExternalData value
  | .letU value => u64UsesExternalData value

def witgenUsesExternalData : {n : ℕ} → Witgen.WitgenIR F n → Bool
  | _, .native _ => false
  | _, .ir steps output =>
      steps.any stepUsesExternalData || vexprUsesExternalData output

def unsupportedWitnesses (operations : List (FlatOperation F)) : List ℕ :=
  operations.zipIdx.filterMap fun (operation, index) =>
    match operation with
    | .witness _ code =>
        if code.exportable && !witgenUsesExternalData code then none else some index
    | _ => none

def componentToJson (index : ℕ) (component : Component F) : Except String Json := do
  let operations := component.rowOperations
  let flat := operations.toFlat
  match unsupportedWitnesses flat with
  | [] => pure ()
  | indices => throw s!"component {index} has native or external-data witness operations at flat indices {indices}"
  let witgen ← operations.witgenJson?
  return Json.mkObj [
    ("index", toJson index),
    ("inputWidth", toJson component.rowOffset),
    ("width", toJson component.width),
    ("witgen", witgen)]

def componentsToJson (components : List (Component F)) : Except String (Array Json) := do
  return (← components.zipIdx.mapM fun (component, index) =>
    componentToJson index component).toArray

/-- Build the complete backend-independent ensemble-witness artifact. -/
def ensembleToJson (ensemble : Ensemble F PublicIO) (config : Config F) : Except String Json := do
  unless config.modes.length = ensemble.tables.length do
    throw s!"generation-mode count {config.modes.length} does not match component count {ensemble.tables.length}"
  let components ← componentsToJson ensemble.tables
  let verifier ← ensemble.verifierOperations.witgenJson?
  return Json.mkObj [
    ("version", 1),
    ("fuel", toJson config.fuel),
    ("publicInputWidth", toJson (size PublicIO)),
    ("modes", Json.arr (config.modes.map modeToJson).toArray),
    ("components", Json.arr components),
    ("verifier", verifier)]

def jsonString (ensemble : Ensemble F PublicIO) (config : Config F) : IO String := do
  match ensembleToJson ensemble config with
  | .ok json => return json.pretty
  | .error error => throw (IO.userError error)

end Export

end Air.Flat.WitnessGeneration
