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

/-- A verifier that pushes byte 5 twice, so that the byte table has to pull it twice. -/
def pushingVerifier : Verifier.Program (F pBabybear) unit where
  main _ := do
    Verifier.push bytes.channel (5 : Expression (F pBabybear))
    Verifier.push bytes.channel (5 : Expression (F pBabybear))
  Spec _ _ := True
  soundness := by simp

def pushedBytes : Ensemble (F pBabybear) unit where
  tables := [bytes.component]
  unique_names := by simp
  channels := [bytes.channel.toRaw]
  verifier := pushingVerifier

def pushedResult : Except String (F pBabybear × Bool × Bool) :=
  match generate pushedBytes 1000 () () with
  | .error error => .error (toString error)
  | .ok witness =>
      match witness.tables with
      | [bytes] =>
          .ok ((bytes.table[5]?.bind (·[1]?)).getD 0, constraintsHold witness,
            channelsBalanced witness)
      | _ => .error "ensemble has no byte table"

/-- The byte table answers the surplus pushes with a negative multiplicity in the row for 5. -/
example : pushedResult = .ok (-2, true, true) := by native_decide

end Air.Flat.WitnessGenerationTest
