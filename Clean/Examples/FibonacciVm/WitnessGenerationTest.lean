module

public import Clean.Examples.FibonacciVm.Ensemble
public import Clean.Backends.Plonky3.Lower
public import Clean.Utils.Primes

-- `native_decide` runs compiled code from these modules.
public meta import Clean.Examples.FibonacciVm.Ensemble
public meta import Clean.Backends.Plonky3.Lower
public meta import Clean.Utils.Primes

@[expose] public section

namespace Air.Flat.WitnessGenerationTest

open Air.Flat.WitnessGeneration

def steps : ℕ := 32

def publicInput : fieldTriple (F pBabybear) :=
  let state := fibonacci steps
  (steps, state.1, state.2)

def result : Except String (List ℕ × ℕ × ℕ × Bool × Bool) :=
  match FibonacciWitness.generate publicInput with
  | .error error => .error (toString error)
  | .ok witness =>
      match witness.tables with
      | _ :: _ :: bytes :: _ =>
          let multiplicities := bytes.table.map fun row => row[1]?.getD 0
          .ok (
            witness.tables.map (·.length),
            multiplicities.sum.val,
            (multiplicities.map FiniteField.val).max?.getD 0,
            constraintsHold witness,
            channelsBalanced witness)
      | _ => .error "ensemble has no byte table"

/--
The verifier seed automatically creates 32 Fibonacci rows; their pulls create 32
distinct addition rows; byte range checks are accumulated in the 256 fixed byte rows.
-/
example : result = .ok ([32, 32, 256], 32, 2, true, true) := by native_decide

def derivedBytesData : Bool :=
  match FibonacciWitness.generate publicInput with
  | .error _ => false
  | .ok witness =>
      let rows := witness.data "bytes" 2
      rows.size == 256 && match rows[42]? with
        | some row => row[0] == (42 : F pBabybear)
        | none => false

/-- The byte component exports its complete `(value, multiplicity)` input rows. -/
example : derivedBytesData = true := by native_decide

def dynamicComponentData : Bool :=
  match FibonacciWitness.generate publicInput with
  | .error _ => false
  | .ok witness =>
      let rows := witness.data "fibonacci" 4
      rows.size == 32 && match rows[0]? with
        | some row => row[0] == 1 && row[1] == 0 && row[2] == 0 && row[3] == 1
        | none => false

/-- Demand-generated components expose their complete inputs just like fixed components. -/
example : dynamicComponentData = true := by native_decide

def repeatedSteps : ℕ := 400

def repeatedPublicInput : fieldTriple (F pBabybear) :=
  let state := fibonacci repeatedSteps
  (repeatedSteps, state.1, state.2)

def repeatedResult : Except String (List ℕ × Bool × Bool) :=
  match FibonacciWitness.generate repeatedPublicInput with
  | .error error => .error (toString error)
  | .ok witness => .ok (
      witness.tables.map (·.length),
      constraintsHold witness,
      channelsBalanced witness)

/-- Repeated addition pulls coalesce after the period of Fibonacci modulo 256. -/
example : repeatedResult = .ok ([512, 512, 256], true, true) := by native_decide

instance : Fact (p1009 > 512) := ⟨by norm_num [p1009]⟩

def invalidPublicInput : fieldTriple (F p1009) := (10, 42, 42)

def invalidRejected : Bool :=
  match FibonacciWitness.generate invalidPublicInput with
  | .error .interactionBound => true
  | _ => false

/-- An unreachable final state keeps the VM running until the interactions reach the field size,
beyond which channels cannot balance. A small field reaches that bound quickly. -/
example : invalidRejected = true := by native_decide

def configErrors : List String :=
  let config := FibonacciWitness.config (p := pBabybear)
  let ensemble := (fibonacciEnsemble (p := pBabybear)).ensemble
  [{ config with components := config.components.drop 1 },
    { config with components := config.components ++ config.components.take 1 },
    { config with components :=
      ("unknown", { mode := FibonacciWitness.fibMode, padding := { input := #[] } }) ::
        config.components }]
  |>.map fun (config : Config (F pBabybear)) => match config.align ensemble with
    | .error error => toString error
    | .ok _ => ""

/-- Generation metadata is looked up by component name; missing, duplicate, and unknown entries
are rejected. -/
example : configErrors = [
    "component 'fibonacci' has no generation config",
    "component 'fibonacci' has multiple generation configs",
    "generation config names unknown component 'unknown'"] := by native_decide

def noData : ProverData (F pBabybear) := fun _ _ => #[]

def extractedFirstRow : Except String (Array (F pBabybear)) := do
  let program ← Backends.Plonky3.lower
    (fibonacciEnsemble (p := pBabybear)).ensemble
    (FibonacciWitness.config (p := pBabybear))
    |>.mapError toString
  let some component := program.components[0]?
    | throw "extracted program has no Fibonacci component"
  component.completeRow #[1, 0, 0, 1] noData

/-- The typed extraction semantics execute the same row-local witness IR as the source circuit. -/
example : extractedFirstRow = .ok #[1, 0, 0, 1, 1] := by native_decide

end Air.Flat.WitnessGenerationTest
