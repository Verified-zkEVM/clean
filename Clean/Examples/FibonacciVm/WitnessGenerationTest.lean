module

public import Clean.Examples.FibonacciVm.Ensemble
public import Clean.Utils.Primes

-- `native_decide` runs compiled code from these modules.
public meta import Clean.Examples.FibonacciVm.Ensemble
public meta import Clean.Utils.Primes

@[expose] public section

namespace Air.Flat.WitnessGenerationTest

open Air.Flat.WitnessGeneration

def steps : ℕ := 32

def publicInput : fieldTriple (F pBabybear) :=
  let state := fibonacci steps
  (steps, state.1, state.2)

def result : Except String (List ℕ × ℕ × ℕ × Bool × Bool) :=
  match fibonacciGenerate publicInput 1000 with
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
The verifier's push creates 32 Fibonacci rows, their pulls create 32 distinct addition rows, and
the byte range checks are counted in the 256 fixed byte rows.
-/
example : result = .ok ([32, 32, 256], 32, 2, true, true) := by native_decide

/-- A channel on which the verifier pushes values for a table to consume. -/
def valueChannel : Channel (F pBabybear) field where
  name := "values"
  Guarantees _ _ := True

/-- One row of a table that consumes the values `0, ..., 7`, counted by its multiplicity. -/
def consumeValue : GeneralFormalCircuit (F pBabybear) fieldPair unit where
  name := "sink"
  main | (value, multiplicity) => valueChannel.emit .pull multiplicity value
  channelsWithRequirements := [valueChannel.toRaw]
  Spec _ _ _ := True
  soundness := by circuit_proof_start [valueChannel]
  completeness := by circuit_proof_start [valueChannel]

/-- The consuming table answers values pushed more often than pulled. -/
def sink : Component (F pBabybear) where
  circuit := consumeValue
  generation := .preallocated {
    channel := valueChannel
    trigger := .push
    height := 8
    input i := pure (.fixed i.toField, .multiplicity)
  }

/-- A verifier that pushes the value 5 twice. -/
def pushingVerifier : Verifier.Program (F pBabybear) unit where
  main _ := do
    Verifier.push valueChannel (5 : Expression (F pBabybear))
    Verifier.push valueChannel (5 : Expression (F pBabybear))
  Spec _ _ := True
  soundness := by simp

def pushedValues : Ensemble (F pBabybear) unit where
  tables := [sink]
  unique_names := by simp
  channels := [valueChannel.toRaw]
  unique_channel_names := by simp
  verifier := pushingVerifier
  tables_channels := by simp [circuit_norm, sink, consumeValue]
  verifier_channels := by simp [circuit_norm, pushingVerifier]

def pushedResult : Except String (F pBabybear × Bool × Bool) :=
  match generate pushedValues 1000 () () with
  | .error error => .error (toString error)
  | .ok witness =>
      match witness.tables with
      | [sink] =>
          .ok ((sink.table[5]?.bind (·[1]?)).getD 0, constraintsHold witness,
            channelsBalanced witness)
      | _ => .error "ensemble has no sink table"

/-- The sink answers the surplus pushes by pulling 5 twice, in the row for 5. -/
example : pushedResult = .ok (2, true, true) := by native_decide

end Air.Flat.WitnessGenerationTest
