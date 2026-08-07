import Clean.Air.Extraction.IR

/-! Structural lowering from a flat Clean ensemble to the typed extraction program. -/

namespace Air.Flat.Extraction

open Air.Flat.WitnessGeneration

variable {F : Type} [FiniteField F] [DecidableEq F]
variable {PublicIO : TypeMap} [ProvableType PublicIO]

inductive LoweringError where
  | modeCount (expected actual : ℕ)
  | nativeWitness (component operation : ℕ)
  | malformedWitnessLocals (component operation : ℕ)
  | legacyLookup (component : ℕ)
  | componentVariable (component index width : ℕ)
  | verifierVariable (index width : ℕ)
deriving Repr, DecidableEq

instance : ToString LoweringError where
  toString
    | .modeCount expected actual =>
        s!"generation-mode count {actual} does not match component count {expected}"
    | .nativeWitness component operation =>
        s!"component {component} witness operation {operation} is a native Lean closure"
    | .malformedWitnessLocals component operation =>
        s!"component {component} witness operation {operation} has an invalid local reference"
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

private def lowerWitness (component operation : ℕ) {width : ℕ}
    (code : Witgen.WitgenIR F width) : Except LoweringError (WitnessBlock F) :=
  match code with
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

private def lowerComponent (index : ℕ) (component : Component F) :
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
    inputWidth := component.rowOffset
    width := component.width
    witnesses
    constraints
    interactions
  }

/-- Lower and validate the backend-facing portion of an ensemble without producing source text. -/
def lower (ensemble : Ensemble F PublicIO) (config : Config F) :
    Except LoweringError (Program F) := do
  unless config.modes.length = ensemble.tables.length do
    throw (.modeCount ensemble.tables.length config.modes.length)
  let components ← ensemble.tables.zipIdx.mapM fun (component, index) =>
    lowerComponent index component
  let verifierInteractions := ensemble.verifierOperations.interactions
  let verifierExpressions := verifierInteractions.flatMap fun interaction =>
    interaction.mult :: interaction.msg.toList
  match expressionsBadVariable (size PublicIO) verifierExpressions with
  | some cellIndex => throw (.verifierVariable cellIndex (size PublicIO))
  | none => pure ()
  return {
    publicInputWidth := size PublicIO
    components
    verifierInteractions
    modes := config.modes
    fuel := config.fuel
  }

end Air.Flat.Extraction
