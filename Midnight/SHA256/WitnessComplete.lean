import Midnight.SHA256.WitnessDependencyCertificate
import Midnight.SHA256.WitnessExecutionSound
import Midnight.SHA256.Semantics.Formal

/-! Constructive completeness of the fixed 24-byte preimage example. The source
read-order, placement and fixed-column obligations are closed certificates here,
not caller premises. The witness is obtained by executing the actual source IR.
The assertion's public digest is the fixed native instance column 1. -/
namespace Midnight.SHA256.WitnessComplete
open Halo2 Semantics

attribute [local irreducible] WitnessCircuit.preimageCircuit WitnessExecution.source
  WitnessExecution.generated WitnessExecution.place WitnessExecution.scalarAssignments
  Preimage.circuit Preimage.formal Preimage.extractedMessage Preimage.publicDigest
  Preimage.hintMessage Spec.digest

/-- The actual witness-bearing source owns its fixed columns and preserves its
loaded tables. Advice erasure and arbitrary-start source relocation discharge it. -/
theorem source_fixed : WitnessExecution.source.FixedWritesLawful [] := by
  unfold WitnessExecution.source
  exact Structural.fixed Preimage.privatePrograms 0

/-- Every source assignment equation holds for the constructive executor. This
statement requires no message validity because read ordering is input independent. -/
theorem generated_extends (hint : ProverHint F) :
    ExtendsWitnesses WitnessExecution.place (WitnessExecution.generated hint)
      WitnessExecution.source 0 :=
  WitnessExecution.generated_extends hint WitnessDependencyCertificate.dependencyCheck source_fixed

/-- A complete realization of the exact bundled assertion, with the extracted
private message and actual native public statement both tied to the environment. -/
structure Realizes (message : Spec.Message) (env : ProverEnvironment F) : Prop where
  capacity : Preimage.Capacity env.toEnvironment
  witnesses : ExtendsWitnesses WitnessExecution.place env
    ((Preimage.formal.synthesize () ()).operations 0) 0
  constraints : Constraints WitnessExecution.place env.toEnvironment
    ((Preimage.formal.synthesize () ()).operations 0) 0
  extracted : Preimage.extractedMessage 0 ⟨WitnessExecution.place, env.toEnvironment⟩ = message
  public_digest : Preimage.publicDigest env.toEnvironment = Spec.digest message

/-- The actual source's honest witness construction satisfies the full assertion;
all fixed structural and dependency obligations have already been discharged. -/
theorem generated_correct (hint : ProverHint F)
    (bytes : Spec.Bytes (Preimage.hintMessage hint)) :
    Realizes (Preimage.hintMessage hint) (WitnessExecution.generated hint) := by
  have result := WitnessExecution.generated_correct hint bytes
    WitnessDependencyCertificate.dependencyCheck source_fixed
  refine ⟨WitnessExecution.generated_capacity hint, ?_, ?_, result.2.1, result.2.2⟩
  · rw [Preimage.formal_operations, ← WitnessExecution.source_eq]
    exact generated_extends hint
  · rw [Preimage.formal_operations, ← WitnessExecution.source_eq]
    exact result.1

/-- A deterministic environment obtained from the fixed external hint interface. -/
def forMessage (message : Spec.Message) : ProverEnvironment F :=
  WitnessExecution.generated (WitnessInitial.hintFor message)

attribute [local irreducible] forMessage

theorem forMessage_correct (message : Spec.Message) (bytes : Spec.Bytes message) :
    Realizes message (forMessage message) := by
  have same := WitnessInitial.hintFor_message message bytes
  have valid : Spec.Bytes (Preimage.hintMessage (WitnessInitial.hintFor message)) := same.symm ▸ bytes
  have result := generated_correct (WitnessInitial.hintFor message) valid
  rw [same] at result
  unfold forMessage
  exact result

/-- Every valid 24-byte message has an actual satisfying source witness, with the
native capacity and exact public instance digest included in its realization. -/
theorem exists_for_message (message : Spec.Message) (bytes : Spec.Bytes message) :
    ∃ env : ProverEnvironment F, Realizes message env :=
  ⟨forMessage message, forMessage_correct message bytes⟩

theorem Realizes.instance_sha256 {message : Spec.Message} {env : ProverEnvironment F}
    (realized : Realizes message env) (i : Fin 32) :
    env.toEnvironment.inst ⟨1⟩ i.val = ((Spec.digest message)[i] : F) := by
  have value := Preimage.formal_instance_sha256 0 ⟨WitnessExecution.place,env.toEnvironment⟩
    realized.capacity realized.constraints i
  rw [realized.extracted] at value
  exact value

/-- Direct actual-instance form of constructive completeness; the caller supplies
only valid input bytes, not witness equations, gate satisfaction or layout facts. -/
theorem forMessage_instance (message : Spec.Message) (bytes : Spec.Bytes message) (i : Fin 32) :
    (forMessage message).toEnvironment.inst ⟨1⟩ i.val = ((Spec.digest message)[i] : F) :=
  (forMessage_correct message bytes).instance_sha256 i

end Midnight.SHA256.WitnessComplete
