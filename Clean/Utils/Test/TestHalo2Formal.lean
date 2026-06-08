import Clean.Halo2.Formal
import Clean.Halo2.Orchard

namespace Halo2.Tests

open Halo2
open Halo2.Pinned

private def leftCell : Synthesis.Cell :=
  { column := Pinned.Column.advice 0, row := 0 }

private def rightCell : Synthesis.Cell :=
  { column := Pinned.Column.advice 1, row := 7 }

/-- A tiny `FormalCircuit` using the Halo2-native `wire` operation.  The spec is
stated directly over Halo2 traces; there is no lowering to ordinary Clean
circuits. -/
def wireFormalCircuit : FormalCircuit Int :=
  { circuit := Circuit.wire leftCell rightCell
    Spec := fun trace => trace.evalCell leftCell = trace.evalCell rightCell
    soundness := by
      intro trace _ h
      simpa [Circuit.Satisfied, Operation.Satisfied] using
        h (Operation.wire leftCell rightCell) (by simp [Circuit.wire]) }

theorem wireFormalCircuit_sound {trace : Trace Int}
    (h : wireFormalCircuit.circuit.Satisfied wireFormalCircuit.lookup trace) :
    wireFormalCircuit.Spec trace :=
  wireFormalCircuit.sound trivial h

private def zeroGate : Pinned.Expression :=
  .advice 0 0 (.rot 0)

/-- A minimal custom-gate `FormalCircuit`: advice cell `(0,0)` must be zero. -/
def zeroGateFormalCircuit : FormalCircuit Int :=
  { circuit := Circuit.assertZero 0 zeroGate
    Spec := fun trace => trace.advice 0 0 = 0
    soundness := by
      intro trace _ h
      simpa [Circuit.Satisfied, Operation.Satisfied, zeroGate, Pinned.Expression.eval] using
        h (Operation.gate 0 zeroGate) (by simp [Circuit.assertZero, Circuit.gate]) }

theorem zeroGateFormalCircuit_sound {trace : Trace Int}
    (h : zeroGateFormalCircuit.circuit.Satisfied zeroGateFormalCircuit.lookup trace) :
    zeroGateFormalCircuit.Spec trace :=
  zeroGateFormalCircuit.sound trivial h

private def boolGate : Pinned.Expression :=
  let x : Pinned.Expression := .advice 0 0 (.rot 0)
  x * (.constant "one" - x)

/-- A small nontrivial example: the Halo2 custom gate `x * (1 - x) = 0`
soundly enforces a Boolean value over `Int`. -/
def boolGateFormalCircuit : FormalCircuit Int :=
  { circuit := Circuit.assertZero 0 boolGate
    Assumptions := fun trace => trace.constant "one" = 1
    Spec := fun trace => trace.advice 0 0 = 0 ∨ trace.advice 0 0 = 1
    soundness := by
      intro trace hOne h
      have hGate : Pinned.Expression.eval trace 0 boolGate = 0 := by
        simpa [Circuit.Satisfied, Operation.Satisfied] using
          h (Operation.gate 0 boolGate) (by simp [Circuit.assertZero, Circuit.gate])
      dsimp [boolGate, Pinned.Expression.eval] at hGate
      rw [hOne] at hGate
      rcases Int.mul_eq_zero.mp hGate with h0 | h1
      · exact Or.inl h0
      · right
        omega }

theorem boolGateFormalCircuit_sound {trace : Trace Int}
    (hOne : trace.constant "one" = 1)
    (h : boolGateFormalCircuit.circuit.Satisfied boolGateFormalCircuit.lookup trace) :
    boolGateFormalCircuit.Spec trace :=
  boolGateFormalCircuit.sound hOne h

/-- Lookup arguments are first-class operations whose relation is supplied by the
formal trace semantics. -/
theorem lookupOperation_sound {trace : Trace Int} {relation : List Int → List Int → Prop}
    (h : (Circuit.lookup 0 [.advice 0 0 (.rot 0)] [.fixed 0 0 (.rot 0)]).Satisfied
      relation trace) :
    relation [trace.advice 0 0] [trace.fixed 0 0] := by
  simpa [Circuit.Satisfied, Operation.Satisfied, Circuit.lookup, Pinned.Expression.eval] using
    h (Operation.lookup 0 [.advice 0 0 (.rot 0)] [.fixed 0 0 (.rot 0)])
      (by simp [Circuit.lookup])

/-- Fixed assignments are also first-class operations in the proof-facing DSL. -/
theorem fixedOperation_sound {trace : Trace Int}
    (h : (Circuit.fixed leftCell "one").Satisfied (fun _ _ => True) trace) :
    trace.evalCell leftCell = trace.constant "one" := by
  simpa [Circuit.Satisfied, Operation.Satisfied] using
    h (Operation.fixed leftCell "one") (by simp [Circuit.fixed])

/-- `Circuit.push` composes constraints in the same proof style as Clean circuits. -/
theorem push_satisfaction_example {trace : Trace Int}
    (h : (Circuit.wire leftCell rightCell).push (Operation.fixed leftCell "one") |>.Satisfied
      (fun _ _ => True) trace) :
    trace.evalCell leftCell = trace.evalCell rightCell ∧
      trace.evalCell leftCell = trace.constant "one" := by
  simpa using h

private def configuredWithWire : Synthesis.ConfiguredCircuit Unit :=
  { config := ()
    cs := {}
    synthesize := fun _ =>
      { copyConstraints := [(leftCell, rightCell)] } }

/-- Converting synthesis metadata to the proof-facing `Circuit` keeps copy
constraints as `Operation.wire`; it does not erase them into custom gates. -/
theorem fromConfigured_keeps_copy_constraint_as_wire :
    (Circuit.fromConfigured configuredWithWire).operations = [Operation.wire leftCell rightCell] := by
  native_decide

/-- Layout row accounting includes copy-constraint endpoints, not just selector activations. -/
theorem configuredWithWire_layout_rows :
    (configuredWithWire.synthesize configuredWithWire.config).usedRows = 8 := by
  native_decide

/-- A configured circuit can be packaged directly as a `FormalCircuit`; proofs are
against `Circuit.fromConfigured`, not against a lowered ordinary Clean circuit. -/
def configuredWireFormalCircuit : FormalCircuit Int :=
  FormalCircuit.fromConfigured "configured wire" configuredWithWire (fun _ _ => True) (fun _ => True)
    (fun trace => trace.evalCell leftCell = trace.evalCell rightCell)
    (by
      intro trace _ h
      have hmem : Operation.wire leftCell rightCell ∈
          (Circuit.fromConfigured configuredWithWire).operations := by
        rw [fromConfigured_keeps_copy_constraint_as_wire]
        simp
      simpa [Operation.Satisfied] using h (Operation.wire leftCell rightCell) hmem)

private def csWithGate : ConstraintSystem :=
  { gates := [zeroGate] }

/-- Gate metadata expands to one proof-facing gate operation per checked row. -/
theorem fromConstraintSystem_expands_gates_by_row :
    (Circuit.fromConstraintSystem csWithGate 2).operations =
      [Operation.gate 0 zeroGate, Operation.gate 1 zeroGate] := by
  native_decide

private def csWithLookup : ConstraintSystem :=
  { lookups := [{ inputExpressions := [.advice 0 0 (.rot 0)], tableExpressions := [.fixed 0 0 (.rot 0)] }] }

/-- Pinned lookup arguments become proof-facing `Operation.lookup`s, not opaque metadata. -/
theorem fromConstraintSystem_keeps_lookup_operation :
    (Circuit.fromConstraintSystem csWithLookup 1).operations =
      [Operation.lookup 0 [.advice 0 0 (.rot 0)] [.fixed 0 0 (.rot 0)]] := by
  native_decide

/-- The current Orchard synthesis layer feeds the proof-facing DSL: the AddChip
copy constraint appears as a Halo2-native `wire` operation. -/
theorem orchardFormalCircuit_contains_synthesis_wire :
    (Circuit.fromConfigured Halo2.Orchard.Action.plonkCircuit).operations.any
      (fun op => op == Operation.wire
        { column := Pinned.Column.advice 7, row := 1 }
        { column := Pinned.Column.advice 8, row := 1 }) = true := by
  native_decide

end Halo2.Tests
