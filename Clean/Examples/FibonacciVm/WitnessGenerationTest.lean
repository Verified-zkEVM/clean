import Clean.Examples.FibonacciVm.Circuit
import Clean.Air.Extraction.Lower
import Clean.Utils.Primes

namespace Air.Flat.WitnessGenerationTest

open Air.Flat.WitnessGeneration

private def steps : ℕ := 32

private def publicInput : fieldTriple (F pBabybear) :=
  let state := fibonacci steps
  (steps, state.1, state.2)

private def result : Except String (List ℕ × ℕ × ℕ × Bool × Bool) :=
  match FibonacciWitness.generate publicInput 1000 with
  | .error error => .error error
  | .ok witness =>
      match witness.tables with
      | _ :: _ :: bytes :: _ =>
          match bytes.table with
          | byteRow :: _ => .ok (
              witness.tables.map (·.length),
              byteRow.toList.sum.val,
              (byteRow.toList.map FiniteField.val).max?.getD 0,
              constraintsHold witness,
              channelsBalanced witness)
          | [] => .error "byte table has no rows"
      | _ => .error "ensemble has no byte table"

/--
The verifier seed automatically creates 32 Fibonacci rows; their pulls create 32
distinct addition rows; byte range checks are accumulated into the one fixed byte row.
-/
example : result = .ok ([32, 32, 32], 32, 2, true, true) := by native_decide

private def repeatedSteps : ℕ := 400

private def repeatedPublicInput : fieldTriple (F pBabybear) :=
  let state := fibonacci repeatedSteps
  (repeatedSteps, state.1, state.2)

private def repeatedResult : Except String (List ℕ × Bool × Bool) :=
  match FibonacciWitness.generate repeatedPublicInput 2000 with
  | .error error => .error error
  | .ok witness => .ok (
      witness.tables.map (·.length),
      constraintsHold witness,
      channelsBalanced witness)

/-- Repeated addition pulls coalesce after the period of Fibonacci modulo 256. -/
example : repeatedResult = .ok ([512, 512, 32], true, true) := by native_decide

private def invalidPublicInput : fieldTriple (F pBabybear) := (10, 42, 42)

private def invalidRejected : Bool :=
  match FibonacciWitness.generate invalidPublicInput 20 with
  | .error _ => true
  | .ok _ => false

/-- A final state not reached within the configured fuel fails generation. -/
example : invalidRejected = true := by native_decide

private def noData : ProverData (F pBabybear) := fun _ _ => #[]

private def extractedFirstRow : Except String (Array (F pBabybear)) := do
  let program ← Air.Flat.Extraction.lower
    (fibonacciEnsemble (p := pBabybear)).ensemble
    (FibonacciWitness.config (p := pBabybear) 1000)
    |>.mapError toString
  let some component := program.components[0]?
    | throw "extracted program has no Fibonacci component"
  component.completeRow #[1, 0, 0, 1] noData

/-- The typed extraction semantics execute the same row-local witness IR as the source circuit. -/
example : extractedFirstRow = .ok #[1, 0, 0, 1, 1] := by native_decide

private def constrainedVerifier : GeneralFormalCircuit (F pBabybear) unit unit where
  main _ := do
    assertZero 0
  Spec _ _ _ := True
  soundness := by circuit_proof_start
  completeness := by circuit_proof_start

private def constrainedVerifierEnsemble : Air.Flat.Ensemble (F pBabybear) unit where
  tables := []
  channels := []
  verifier := constrainedVerifier
  verifier_length_zero := by simp [constrainedVerifier, circuit_norm]

private def constrainedVerifierRejected : Bool :=
  match Air.Flat.Extraction.lower constrainedVerifierEnsemble { modes := [], padding := [], fuel := 1 } with
  | .error (.verifierConstraint 0) => true
  | _ => false

/-- Rust extraction must not silently discard verifier constraints. -/
example : constrainedVerifierRejected = true := by native_decide

end Air.Flat.WitnessGenerationTest
