import Midnight.SHA256.WitnessExecution
import Midnight.SHA256.WitnessInitialTables
import Midnight.Math.Witness.Columns
import Midnight.Math.Witness.FixedTables

/-! The constructive executor applied to the complete native preimage program.
The remaining premises are message-independent structural certificates. The
closed certificate module must discharge them before claiming witness existence
for the standalone circuit. No source witness equation or gate is assumed here. -/
namespace Midnight.SHA256.WitnessExecution
open Halo2 Midnight.Math.Witness
open Semantics

attribute [local irreducible] WitnessCircuit.preimageCircuit
  source scalarAssignments place Preimage.circuit
  Preimage.publicDigest Preimage.extractedMessage Preimage.hintMessage Spec.digest
  WitnessInitial.initial

def generated (hint : ProverHint F) : ProverEnvironment F :=
  Execute.run place scalarAssignments (WitnessInitial.initial hint)

attribute [local irreducible] generated

theorem source_eq : source = Preimage.circuit.operations 0 := by
  unfold source Preimage.circuit
  rfl

theorem generated_hint (hint : ProverHint F) : (generated hint).hint = hint := by
  rw [generated, Execute.run_hint, WitnessInitial.initial_hint]

theorem generated_capacity (hint : ProverHint F) : Preimage.Capacity (generated hint).toEnvironment := by
  unfold Preimage.Capacity
  rw [generated, Execute.run_usableRows]
  exact WitnessInitial.capacity hint

theorem generated_public (hint : ProverHint F) :
    Preimage.publicDigest (generated hint).toEnvironment = Spec.digest (Preimage.hintMessage hint) := by
  have same : Preimage.publicDigest (generated hint).toEnvironment =
      Preimage.publicDigest (WitnessInitial.initial hint).toEnvironment := by
    unfold Preimage.publicDigest
    apply Vector.ext
    intro i hi
    simp only [Vector.getElem_ofFn]
    apply congrArg ZMod.val
    simpa only [generated, scalarAssignments] using
      Operations.run_instance place 0 source (WitnessInitial.initial hint) ⟨1⟩ i
  exact same.trans (WitnessInitial.public_digest hint)

theorem generated_extends (hint : ProverHint F)
    (ordered : dependencyCheck = true)
    (fixed : source.FixedWritesLawful []) :
    ExtendsWitnesses place (generated hint) source 0 := by
  have valid := Fast.empty_refines place scalarAssignments ordered
  rw [scalarAssignments] at valid
  unfold generated scalarAssignments
  apply Operations.run_extendsWitnesses place 0 source [] valid (WitnessInitial.initial hint)
  · simpa only [source] using WitnessInitial.source_tables hint Preimage.privatePrograms
  · exact Operations.assignments_separate_tables place 0 source [] fixed

/-- Execute the original advice programs, then use the source's honest
completeness proof. Structural premises concern only the fixed circuit. -/
theorem generated_correct (hint : ProverHint F)
    (bytes : Spec.Bytes (Preimage.hintMessage hint))
    (ordered : dependencyCheck = true)
    (fixed : source.FixedWritesLawful []) :
    Constraints place (generated hint).toEnvironment source 0 ∧
      Preimage.extractedMessage 0 ⟨place,(generated hint).toEnvironment⟩ = Preimage.hintMessage hint ∧
      Preimage.publicDigest (generated hint).toEnvironment = Spec.digest (Preimage.hintMessage hint) := by
  have witnesses := generated_extends hint ordered fixed
  rw [source_eq] at witnesses
  have hintBytes : Spec.Bytes (Preimage.hintMessage (generated hint).hint) := by
    rw [generated_hint]
    exact bytes
  have claim : Preimage.publicDigest (generated hint).toEnvironment =
      Spec.digest (Preimage.hintMessage (generated hint).hint) := by
    rw [generated_hint]
    exact generated_public hint
  have constraints := (Preimage.complete 0 ⟨place,generated hint⟩ (generated_capacity hint)
    hintBytes claim witnesses).1
  have extracted := Preimage.extractedMessage_honest 0 ⟨place,generated hint⟩
    (generated_capacity hint) hintBytes witnesses
  rw [generated_hint] at extracted
  rw [source_eq]
  exact ⟨constraints,extracted,generated_public hint⟩

end Midnight.SHA256.WitnessExecution
