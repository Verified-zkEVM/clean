import Midnight.SHA256.Semantics.PreimageSource
import Midnight.SHA256.Semantics.Body

/-! Full native preimage semantics, including its actual public instance column
and its own table loads. The verifier's message comes only from assigned cells. -/
namespace Midnight.SHA256.Semantics.Preimage
open Halo2 WitnessCircuit Linear BodyInput

attribute [local irreducible] WitnessCircuit.body WitnessCircuit.synthesize
  WitnessCircuit.assignBytes Spec.digest

/-- Prove projections before supplying the complete source body, so kernel
conversion never unfolds its internal state to establish these monadic laws. -/
private theorem returnFirst_operations {α β : Type} (program : Circuit F (α × β))
    (self : RegionIndex) :
    (do let (value, _) ← program; pure value : Circuit F α).operations self =
      program.operations self := by
  change _ ++ [] = _
  exact List.append_nil _

private theorem returnFirst_output {α β : Type} (program : Circuit F (α × β))
    (self : RegionIndex) :
    (do let (value, _) ← program; pure value : Circuit F α).output self =
      (program.output self).1 := rfl

private theorem returnFirst_next {α β : Type} (program : Circuit F (α × β))
    (self : RegionIndex) :
    (do let (value, _) ← program; pure value : Circuit F α).nextRegionIndex self =
      program.nextRegionIndex self := rfl

theorem synthesize_operations (input : Vector (WitgenIR F 1) 24) (self : RegionIndex) :
    (WitnessCircuit.synthesize input).operations self =
      (WitnessCircuit.body input []).operations self := by
  unfold WitnessCircuit.synthesize
  exact returnFirst_operations (WitnessCircuit.body input []) self

theorem synthesize_output (input : Vector (WitgenIR F 1) 24) (self : RegionIndex) :
    (WitnessCircuit.synthesize input).output self =
      ((WitnessCircuit.body input []).output self).1 := by
  unfold WitnessCircuit.synthesize
  exact returnFirst_output (WitnessCircuit.body input []) self

theorem synthesize_next (input : Vector (WitgenIR F 1) 24) (self : RegionIndex) :
    (WitnessCircuit.synthesize input).nextRegionIndex self =
      (WitnessCircuit.body input []).nextRegionIndex self := by
  unfold WitnessCircuit.synthesize
  exact returnFirst_next (WitnessCircuit.body input []) self

theorem synthesize_lawful (input : Vector (WitgenIR F 1) 24) (self : RegionIndex) :
    (WitnessCircuit.synthesize input).nextRegionIndex self =
      self + ((WitnessCircuit.synthesize input).operations self).regionCount := by
  rw [synthesize_next, synthesize_operations]
  exact Body.body_lawful input [] self

theorem finish_operations (outputs : Array Cell) (self : RegionIndex) :
    (finish outputs).operations self = (expose outputs).operations self ++ tables.operations self := by
  unfold finish
  change (expose outputs).operations self ++
    (tables.operations ((expose outputs).nextRegionIndex self) ++ []) = _
  rw [List.append_nil, expose_next]

theorem finish_constraints (outputs : Array Cell) (env : Placed Environment F) (self : RegionIndex) :
    Constraints env.place env.env ((finish outputs).operations self) self ↔
      (∀ i, i < outputs.size → outputs[i]!.eval env.place env.env = env.env.inst ⟨1⟩ i) ∧
      Constraints env.place env.env (tables.operations self) self := by
  rw [finish_operations, constraints_append, expose_count, Nat.add_zero, expose_constraints]

theorem finish_witnesses (outputs : Array Cell) (env : Placed ProverEnvironment F) (self : RegionIndex) :
    ExtendsWitnesses env.place env.env ((finish outputs).operations self) self ↔
      ExtendsWitnesses env.place env.env (tables.operations self) self := by
  rw [finish_operations, extendsWitnesses_append, expose_count, Nat.add_zero]
  exact and_iff_right (expose_witnesses outputs env self)

private theorem bindFinish_output (program : Circuit F (Array Cell))
    (self : RegionIndex) :
    (do let outputs ← program; finish outputs).output self = program.output self := rfl

theorem preimage_output (input : Vector (WitgenIR F 1) 24) (self : RegionIndex) :
    (WitnessCircuit.preimageCircuit input).output self =
      (WitnessCircuit.synthesize input).output self := by
  rw [preimage_source]
  exact bindFinish_output (WitnessCircuit.synthesize input) self

theorem preimage_constraints (input : Vector (WitgenIR F 1) 24)
    (env : Placed Environment F) (self : RegionIndex) :
    Constraints env.place env.env ((WitnessCircuit.preimageCircuit input).operations self) self ↔
      Constraints env.place env.env ((WitnessCircuit.body input []).operations self) self ∧
      (∀ i, i < ((WitnessCircuit.synthesize input).output self).size →
        ((WitnessCircuit.synthesize input).output self)[i]!.eval env.place env.env = env.env.inst ⟨1⟩ i) ∧
      Constraints env.place env.env
        (tables.operations ((WitnessCircuit.synthesize input).nextRegionIndex self))
        ((WitnessCircuit.synthesize input).nextRegionIndex self) := by
  rw [preimage_source]
  change Constraints env.place env.env
    ((WitnessCircuit.synthesize input).operations self ++
      (finish ((WitnessCircuit.synthesize input).output self)).operations
        ((WitnessCircuit.synthesize input).nextRegionIndex self)) self ↔ _
  rw [constraints_append, ← synthesize_lawful input self, finish_constraints, synthesize_operations]

theorem preimage_witnesses (input : Vector (WitgenIR F 1) 24)
    (env : Placed ProverEnvironment F) (self : RegionIndex) :
    ExtendsWitnesses env.place env.env ((WitnessCircuit.preimageCircuit input).operations self) self ↔
      ExtendsWitnesses env.place env.env ((WitnessCircuit.body input []).operations self) self ∧
      ExtendsWitnesses env.place env.env
        (tables.operations ((WitnessCircuit.synthesize input).nextRegionIndex self))
        ((WitnessCircuit.synthesize input).nextRegionIndex self) := by
  rw [preimage_source]
  change ExtendsWitnesses env.place env.env
    ((WitnessCircuit.synthesize input).operations self ++
      (finish ((WitnessCircuit.synthesize input).output self)).operations
        ((WitnessCircuit.synthesize input).nextRegionIndex self)) self ↔ _
  rw [extendsWitnesses_append, ← synthesize_lawful input self, finish_witnesses, synthesize_operations]

/-- The private bytes extracted from the real source assignments. No hint or
honest witness equation is used by this verifier-side function. -/
def extractedMessage (self : RegionIndex) (env : Placed Environment F) : Spec.Message :=
  Body.extractedMessage privatePrograms [] self env

/-- The statement is fixed to the native public instance column and its 32 rows. -/
def publicDigest (env : Environment F) : Vector Nat 32 :=
  Vector.ofFn fun i => (env.inst ⟨1⟩ i.val).val

private theorem public_of_output (outputs : Array Cell) (message : Spec.Message)
    (env : Placed Environment F)
    (value : values env outputs = (Spec.digest message).toArray)
    (copies : ∀ i, i < outputs.size → outputs[i]!.eval env.place env.env = env.env.inst ⟨1⟩ i) :
    publicDigest env.env = Spec.digest message := by
  have size : outputs.size = 32 := by
    have := congrArg Array.size value
    simpa only [values, Array.size_map, Vector.size_toArray] using this
  apply Vector.ext
  intro i hi
  have inOutputs : i < outputs.size := by omega
  have valueAt := congrArg (fun xs : Array Nat => xs[i]!) value
  change (values env outputs)[i]! = (Spec.digest message).toArray[i]! at valueAt
  rw [getElem!_pos (values env outputs) i (by simpa [values] using inOutputs),
    getElem!_pos (Spec.digest message).toArray i (by simpa using hi)] at valueAt
  simp only [values, Array.getElem_map] at valueAt
  have copy := copies i inOutputs
  simp only [getElem!_pos outputs i inOutputs] at copy
  simpa only [publicDigest, Vector.getElem_ofFn, PrepareCircuit.cellValue, copy, Vector.getElem_toArray] using valueAt

/-- Complete verifier-side boundary: its own table constraints provide the
lookup meanings, and its actual public copies publish the computed SHA digest. -/
theorem sound (self : RegionIndex) (env : Placed Environment F) (capacity : Capacity env.env)
    (satisfied : Constraints env.place env.env (circuit.operations self) self) :
    Spec.Bytes (extractedMessage self env) ∧
      publicDigest env.env = Spec.digest (extractedMessage self env) ∧
      values env (circuit.output self) = (Spec.digest (extractedMessage self env)).toArray := by
  have parts := (preimage_constraints privatePrograms env self).mp satisfied
  obtain ⟨range,spread⟩ := tables_sound _ env capacity parts.2.2
  obtain ⟨bytes,value,_⟩ := Body.body_sound privatePrograms [] self env range spread
    (cacheMeaning_nil env) parts.1
  have result : values env ((WitnessCircuit.synthesize privatePrograms).output self) =
      (Spec.digest (extractedMessage self env)).toArray := by
    rw [synthesize_output]
    exact value
  refine ⟨bytes, public_of_output _ _ env result parts.2.1, ?_⟩
  change values env ((WitnessCircuit.preimageCircuit privatePrograms).output self) = _
  rw [preimage_output]
  exact result

theorem honestMessage_eq (env : Placed ProverEnvironment F) :
    BodyInput.honestMessage privatePrograms env = hintMessage env.env.hint := by
  apply Vector.ext
  intro i hi
  simp only [BodyInput.honestMessage, hintMessage, Vector.getElem_map]
  have := privatePrograms_eval env ⟨i,hi⟩
  simp only [Fin.getElem_fin] at this
  exact congrArg ZMod.val this

private theorem copies_of_output (outputs : Array Cell) (message : Spec.Message)
    (env : Placed Environment F) (value : values env outputs = (Spec.digest message).toArray)
    (claim : publicDigest env.env = Spec.digest message) :
    ∀ i, i < outputs.size → outputs[i]!.eval env.place env.env = env.env.inst ⟨1⟩ i := by
  have size : outputs.size = 32 := by
    have := congrArg Array.size value
    simpa only [values, Array.size_map, Vector.size_toArray] using this
  intro i hi
  have bound : i < 32 := by omega
  have valueAt := congrArg (fun xs : Array Nat => xs[i]!) value
  change (values env outputs)[i]! = (Spec.digest message).toArray[i]! at valueAt
  rw [getElem!_pos (values env outputs) i (by simpa [values] using hi),
    getElem!_pos (Spec.digest message).toArray i (by simpa using bound)] at valueAt
  simp only [values, Array.getElem_map] at valueAt
  have hp := congrArg (fun vector : Vector Nat 32 => vector[i]) claim
  simp only [publicDigest, Vector.getElem_ofFn] at hp
  apply ZMod.val_injective
  simpa only [getElem!_pos outputs i hi, PrepareCircuit.cellValue] using valueAt.trans hp.symm

/-- Honest completeness consumes real source witness equations and the public
claim for the external hint message. It does not assume computed advice values,
gate constraints, or equality of the extracted private message to the hint. -/
theorem complete (self : RegionIndex) (env : Placed ProverEnvironment F)
    (capacity : Capacity env.env.toEnvironment)
    (bytes : Spec.Bytes (hintMessage env.env.hint))
    (claim : publicDigest env.env.toEnvironment = Spec.digest (hintMessage env.env.hint))
    (witnesses : ExtendsWitnesses env.place env.env (circuit.operations self) self) :
    Constraints env.place env.env.toEnvironment (circuit.operations self) self ∧
      values env.toEnvironment (circuit.output self) = (Spec.digest (hintMessage env.env.hint)).toArray := by
  have parts := (preimage_witnesses privatePrograms env self).mp witnesses
  have loaded := tables_complete _ env parts.2
  obtain ⟨range,spread⟩ := tables_sound _ env.toEnvironment capacity loaded
  obtain ⟨satisfied,value,_⟩ := Body.body_complete privatePrograms env range spread
    (privatePrograms_honest env bytes) [] self (cacheMeaning_nil _) parts.1
  rw [honestMessage_eq] at value
  have result : values env.toEnvironment ((WitnessCircuit.synthesize privatePrograms).output self) =
      (Spec.digest (hintMessage env.env.hint)).toArray := by
    rw [synthesize_output]
    exact value
  refine ⟨(preimage_constraints privatePrograms env.toEnvironment self).mpr
    ⟨satisfied,copies_of_output _ _ _ result claim,loaded⟩, ?_⟩
  change values env.toEnvironment ((WitnessCircuit.preimageCircuit privatePrograms).output self) = _
  rw [preimage_output]
  exact result

/-- The actual private assignments agree with the fixed external hint under
honest source witness equations. This equality is proved, never assumed. -/
theorem extractedMessage_honest (self : RegionIndex) (env : Placed ProverEnvironment F)
    (capacity : Capacity env.env.toEnvironment)
    (bytes : Spec.Bytes (hintMessage env.env.hint))
    (witnesses : ExtendsWitnesses env.place env.env (circuit.operations self) self) :
    extractedMessage self env.toEnvironment = hintMessage env.env.hint := by
  have parts := (preimage_witnesses privatePrograms env self).mp witnesses
  have loaded := tables_complete _ env parts.2
  have range := (tables_sound _ env.toEnvironment capacity loaded).1
  have before := parts.1
  rw [Body.source_body,
    WitnessBuild.bind_extendsWitnesses _ _ (Inputs.assignBytes_lawful privatePrograms)] at before
  obtain ⟨_,rep,_⟩ := BodyInput.assignBytes_complete privatePrograms env range
    (privatePrograms_honest env bytes) [] self (cacheMeaning_nil _) before.1
  exact (inputRep_extract rep).trans (honestMessage_eq env)

end Midnight.SHA256.Semantics.Preimage
