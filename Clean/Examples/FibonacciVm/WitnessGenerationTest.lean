module

public import Clean.Examples.FibonacciVm.Ensemble
public import Clean.Utils.Primes

-- `native_decide` runs compiled code from these modules.
public meta import Clean.Examples.FibonacciVm.Ensemble
public meta import Clean.Utils.Primes

@[expose] public section

namespace Air.Flat.WitnessGenerationTest

open Air.Flat.WitnessGeneration

def publicInput (steps : ℕ) : fieldTriple (F pBabybear) :=
  let state := fibonacci steps
  (steps, state.1, state.2)

def result (steps : ℕ) : Except String (List ℕ × ℕ × ℕ × Bool × Bool) :=
  match fibonacciGenerate (publicInput steps) 1000 with
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
example : result 32 = .ok ([32, 32, 256], 32, 2, true, true) := by native_decide

/-- Without steps, the verifier's push and pull cancel, so the Fibonacci and addition tables stay
empty. -/
example : result 0 = .ok ([0, 0, 256], 0, 0, true, true) := by native_decide

/--
For these heights, the verifier computes the interaction counts of every channel, the same as the
Rust statement's, and checks the LogUp bound for them.
-/
example :
    let ens := (fibonacciEnsemble (p := pBabybear)).ensemble
    ens.channels.map (fun channel => (channel.name, ens.interactionCount channel.name [32, 32, 256]))
      = [("fibonacci", 66), ("add8", 64), ("bytes", 288)] ∧
    ens.interactionsFit .logUp [32, 32, 256] := by
  native_decide

end Air.Flat.WitnessGenerationTest
