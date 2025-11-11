import Clean.Examples.YieldExample.ByteRangeYielder
import Clean.Examples.YieldExample.U32NormalizedAssertion
import Clean.Circuit.Basic
import Clean.Types.U32
import Clean.Utils.Tactics

namespace Examples.YieldExample.ComposedExample

variable {p : ℕ} [Fact p.Prime] [Fact (p > 512)]

/--
Main circuit that composes ByteRangeYielder and U32NormalizedAssertion.
First yields all bytes 0-255, then checks that the input U32 is normalized.
-/
def main (input : Var U32 (F p)) : Circuit (F p) Unit := do
  -- First yield all bytes 0-255
  ByteRangeYielder.circuit ()
  -- Then check the input is normalized using those yields
  U32NormalizedAssertion.circuit input

def elaborated : ElaboratedCircuit (F p) U32 unit where
  main
  localLength _ := 0
  localLength_eq := by
    intro _
    simp only [circuit_norm, main, ByteRangeYielder.circuit, ByteRangeYielder.elaborated, U32NormalizedAssertion.circuit, U32NormalizedAssertion.elaborated]
  yields input env offset :=
    ByteRangeYielder.elaborated.yields () env offset ∪
    U32NormalizedAssertion.elaborated.yields input env offset
  yields_eq := by
    intro input env offset
    simp [circuit_norm, main, ByteRangeYielder.circuit, ByteRangeYielder.elaborated, U32NormalizedAssertion.circuit, U32NormalizedAssertion.elaborated]
  subcircuitsConsistent := by
    simp [circuit_norm, main, ByteRangeYielder.circuit, ByteRangeYielder.elaborated, U32NormalizedAssertion.circuit, U32NormalizedAssertion.elaborated]

/--
Assumptions:
1. The input must be normalized (needed for completeness)
2. The global yielded set equals the local yields (needed for completeness)
-/
def Assumptions (input : U32 (F p)) (yielded : Set (NamedList (F p))) : Prop :=
  input.Normalized ∧
  ∀ env offset input_var, eval env input_var = input →
    yielded = elaborated.yields input_var env offset

/--
Spec: If the yielded set equals the localYields (preventing unsound entries),
then the input is normalized.
-/
def Spec (input : U32 (F p)) (yielded : Set (NamedList (F p)))
         (_ : unit (F p)) (localYields : Set (NamedList (F p))) : Prop :=
  yielded = localYields → input.Normalized

theorem soundness : GeneralFormalCircuitUsingYields.Soundness (F p) elaborated Spec := by
  circuit_proof_all [ByteRangeYielder.circuit, ByteRangeYielder.elaborated,
    ByteRangeYielder.Assumptions, ByteRangeYielder.Spec,
    U32NormalizedAssertion.circuit, U32NormalizedAssertion.elaborated,
    U32NormalizedAssertion.Assumptions, U32NormalizedAssertion.Spec]

theorem completeness : GeneralFormalCircuitUsingYields.Completeness (F p) elaborated Assumptions := by
  circuit_proof_start [ByteRangeYielder.circuit, ByteRangeYielder.elaborated,
    ByteRangeYielder.Assumptions, ByteRangeYielder.Spec,
    U32NormalizedAssertion.circuit, U32NormalizedAssertion.elaborated,
    U32NormalizedAssertion.Assumptions, U32NormalizedAssertion.Spec]
  obtain ⟨h_normalized, h_yielded_eq⟩ := h_assumptions
  specialize h_yielded_eq env input_var h_input
  simp_all

def circuit : GeneralFormalCircuitUsingYields (F p) U32 unit where
  elaborated
  Assumptions
  Spec
  soundness
  completeness

end Examples.YieldExample.ComposedExample
