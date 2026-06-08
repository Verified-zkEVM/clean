import Clean.Halo2.Formal

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
  { circuit := Circuit.gate 0 zeroGate
    Spec := fun trace => trace.advice 0 0 = 0
    soundness := by
      intro trace _ h
      simpa [Circuit.Satisfied, Operation.Satisfied, zeroGate, Pinned.Expression.eval] using
        h (Operation.gate 0 zeroGate) (by simp [Circuit.gate]) }

theorem zeroGateFormalCircuit_sound {trace : Trace Int}
    (h : zeroGateFormalCircuit.circuit.Satisfied zeroGateFormalCircuit.lookup trace) :
    zeroGateFormalCircuit.Spec trace :=
  zeroGateFormalCircuit.sound trivial h

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

private def csWithLookup : ConstraintSystem :=
  { lookups := [{ inputExpressions := [.advice 0 0 (.rot 0)], tableExpressions := [.fixed 0 0 (.rot 0)] }] }

/-- Pinned lookup arguments become proof-facing `Operation.lookup`s, not opaque metadata. -/
theorem fromConstraintSystem_keeps_lookup_operation :
    (Circuit.fromConstraintSystem csWithLookup 1).operations =
      [Operation.lookup 0 [.advice 0 0 (.rot 0)] [.fixed 0 0 (.rot 0)]] := by
  native_decide

end Halo2.Tests
