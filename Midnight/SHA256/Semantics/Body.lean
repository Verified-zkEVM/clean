import Midnight.SHA256.Semantics.BodyInput
import Midnight.SHA256.Semantics.Schedule
import Midnight.SHA256.Semantics.Rounds

/-! Semantic composition of the unchanged witness-bearing SHA-256 source body.
Soundness names the actual assigned private input cells. Honest completeness
uses the supplied serializable programs only to identify the intended message. -/
namespace Midnight.SHA256.Semantics.Body
open Halo2 WitnessCircuit WitnessBuild Initialize RoundGadgets Linear BodyInput

abbrev Cell := WitnessCircuit.Cell
abbrev Cache := WitnessCircuit.Cache

attribute [local irreducible] WitnessCircuit.assignBytes WitnessCircuit.initialState
  WitnessCircuit.pad WitnessCircuit.blockFromBytes WitnessCircuit.messageSchedule
  WitnessCircuit.addStates Rounds.source Digest.serialize

def finish (initial : Compression) (block : Array Cell) : Build (Array Cell) := do
  let words ← WitnessCircuit.messageSchedule block
  let final ← Rounds.source words initial
  let digest ← WitnessCircuit.addStates initial final
  Digest.serialize digest

def suffix (bytes : Array Cell) : Build (Array Cell) := do
  let initial ← WitnessCircuit.initialState
  let padded ← WitnessCircuit.pad bytes
  let block ← WitnessCircuit.blockFromBytes padded
  finish initial block

theorem source_body (input : Vector (WitgenIR F 1) 24) :
    WitnessCircuit.body input = (do let bytes ← WitnessCircuit.assignBytes input; suffix bytes) := by
  unfold WitnessCircuit.body suffix finish Rounds.source Digest.serialize
  simp only [WitnessBuild.bind_pure]

attribute [local irreducible] WitnessCircuit.body

theorem finish_lawful (initial : Compression) (block : Array Cell) : Lawful (finish initial block) := by
  unfold finish
  apply lawful_bind (Schedule.messageSchedule_lawful block)
  intro words
  apply lawful_bind (Rounds.source_lawful words initial)
  intro final
  exact lawful_bind (Feedforward.addStates_lawful initial final) Digest.serialize_lawful

theorem suffix_lawful (bytes : Array Cell) : Lawful (suffix bytes) := by
  unfold suffix
  apply lawful_bind Initialize.initialState_lawful
  intro initial
  apply lawful_bind (Padding.pad_lawful bytes)
  intro padded
  exact lawful_bind (Block.blockFromBytes_lawful padded) (finish_lawful initial)

theorem body_lawful (input : Vector (WitgenIR F 1) 24) : Lawful (WitnessCircuit.body input) := by
  rw [source_body]
  exact lawful_bind (Inputs.assignBytes_lawful input) suffix_lawful

theorem feedforward_reference (message : Spec.Message) :
    Feedforward.expected Specs.SHA256.H0
      (Specs.SHA256.sha256Compress Specs.SHA256.H0 (Specs.SHA256.messageSchedule (Spec.block message))) =
      Spec.hashWords message := by
  rw [Spec.hashWords_eq_compressBlock]
  rfl

/-- Every native post-packing call participates in the actual operation list. -/
theorem finish_sound (env : Placed Environment F) (range : Range.ByteTable env.env)
    (spread : Gates.SpreadTable env.env) (initial : Compression)
    (initialRep : StateRep env initial Specs.SHA256.H0)
    (block : Array Cell) (message : Spec.Message) (blockRep : BlockRep env block message) :
    Sound env (finish initial block) (fun output => values env output = (Spec.digest message).toArray) := by
  unfold finish
  apply sound_bind (Schedule.messageSchedule_lawful block)
    (Schedule.messageSchedule_sound env spread block (Spec.block message) blockRep.1 blockRep.2)
  intro words schedule
  have rep := Rounds.ScheduleRep.of_values env words (Specs.SHA256.messageSchedule (Spec.block message))
    schedule.1 schedule.2
  apply sound_bind (Rounds.source_lawful words initial)
    (Rounds.source_sound env spread words _ rep initial Specs.SHA256.H0 initialRep)
  intro final finalRep
  apply sound_bind (Feedforward.addStates_lawful initial final)
    (Feedforward.addStates_sound initial final _ _ env spread initialRep finalRep)
  intro digest digestRep cache self valid satisfied
  obtain ⟨value, cacheEq⟩ := Digest.serialize_sound digest _ env range digestRep
    (Feedforward.expected_bound _ _) cache self satisfied
  refine ⟨?_, cacheEq.symm ▸ valid⟩
  rw [feedforward_reference] at value
  exact value

theorem finish_complete (env : Placed ProverEnvironment F) (range : Range.ByteTable env.env.toEnvironment)
    (spread : Gates.SpreadTable env.env.toEnvironment) (initial : Compression)
    (initialRep : StateRep env.toEnvironment initial Specs.SHA256.H0)
    (block : Array Cell) (message : Spec.Message) (blockRep : BlockRep env.toEnvironment block message) :
    Complete env (finish initial block)
      (fun output => values env.toEnvironment output = (Spec.digest message).toArray) := by
  unfold finish
  apply complete_bind (Schedule.messageSchedule_lawful block)
    (Schedule.messageSchedule_complete env spread block (Spec.block message) blockRep.1 blockRep.2)
  intro words schedule
  have rep := Rounds.ScheduleRep.of_values env.toEnvironment words
    (Specs.SHA256.messageSchedule (Spec.block message)) schedule.1 schedule.2
  have roundComplete : Complete env (Rounds.source words initial)
      (fun out => StateRep env.toEnvironment out
        (Specs.SHA256.sha256Compress Specs.SHA256.H0 (Specs.SHA256.messageSchedule (Spec.block message)))) := by
    intro cache self valid witnesses
    exact Rounds.source_complete env spread words _ rep initial Specs.SHA256.H0 initialRep
      cache self valid witnesses
  apply complete_bind (Rounds.source_lawful words initial) roundComplete
  intro final finalRep
  apply complete_bind (Feedforward.addStates_lawful initial final)
    (Feedforward.addStates_complete initial final _ _ env spread initialRep finalRep)
  intro digest digestRep cache self valid witnesses
  obtain ⟨satisfied, value, cacheEq⟩ := Digest.serialize_complete digest _ env range digestRep
    (Feedforward.expected_bound _ _) cache self witnesses
  refine ⟨satisfied, ?_, cacheEq.symm ▸ valid⟩
  rw [feedforward_reference] at value
  exact value

theorem suffix_sound (env : Placed Environment F) (range : Range.ByteTable env.env)
    (spread : Gates.SpreadTable env.env) (bytes : Array Cell) (message : Spec.Message)
    (inputRep : InputRep env bytes message) :
    Sound env (suffix bytes) (fun output => values env output = (Spec.digest message).toArray) := by
  unfold suffix
  apply sound_bind Initialize.initialState_lawful (Initialize.initialState_sound env)
  intro initial initialRep
  apply sound_bind (Padding.pad_lawful bytes) (BodyInput.pad_sound env bytes message inputRep)
  intro padded paddedRep
  apply sound_bind (Block.blockFromBytes_lawful padded) (BodyInput.block_sound env padded message paddedRep)
  intro block blockRep
  exact finish_sound env range spread initial initialRep block message blockRep

theorem suffix_complete (env : Placed ProverEnvironment F) (range : Range.ByteTable env.env.toEnvironment)
    (spread : Gates.SpreadTable env.env.toEnvironment) (bytes : Array Cell) (message : Spec.Message)
    (inputRep : InputRep env.toEnvironment bytes message) :
    Complete env (suffix bytes)
      (fun output => values env.toEnvironment output = (Spec.digest message).toArray) := by
  unfold suffix
  apply complete_bind Initialize.initialState_lawful (BodyInput.initialState_complete_action env)
  intro initial initialRep
  apply complete_bind (Padding.pad_lawful bytes) (BodyInput.pad_complete env bytes message inputRep)
  intro padded paddedRep
  apply complete_bind (Block.blockFromBytes_lawful padded) (BodyInput.block_complete env padded message paddedRep)
  intro block blockRep
  exact finish_complete env range spread initial initialRep block message blockRep

/-- The witness is extracted from the cells returned by the body's real first
stage, at the actual region index and incoming cache. No honest hint is read. -/
def extractedMessage (input : Vector (WitgenIR F 1) 24) (cache : Cache)
    (self : RegionIndex) (env : Placed Environment F) : Spec.Message :=
  BodyInput.extractMessage env ((WitnessCircuit.assignBytes input cache).output self).1

/-- Dependent source composition retains the actual first-stage output in the
postcondition without unfolding either source program during proof checking. -/
private theorem sound_bind_input {α β : Type} (first : Build α) (next : α → Build β)
    (action : Build β) (source : action = first >>= next) (law : Lawful first)
    (env : Placed Environment F) (middle : α → Prop) (post : α → β → Prop)
    (before : Sound env first middle)
    (after : ∀ value, middle value → Sound env (next value) (post value))
    (cache : Cache) (self : RegionIndex) (valid : CacheMeaning env cache)
    (satisfied : Constraints env.place env.env ((action cache).operations self) self) :
    let input := ((first cache).output self).1
    let output := (action cache).output self
    middle input ∧ post input output.1 ∧ CacheMeaning env output.2 := by
  subst action
  rw [bind_constraints _ _ law _ _ _ _] at satisfied
  obtain ⟨mid, nextCache⟩ := before cache self valid satisfied.1
  obtain ⟨result, finalCache⟩ := after _ mid _ _ nextCache satisfied.2
  simp only [bind_output]
  exact ⟨mid,result,finalCache⟩

/-- Full source-body soundness, including verifier-visible byte bounds and the
reference SHA-256 digest of the exact private assigned-cell message. -/
theorem body_sound (input : Vector (WitgenIR F 1) 24) (cache : Cache) (self : RegionIndex)
    (env : Placed Environment F) (range : Range.ByteTable env.env)
    (spread : Gates.SpreadTable env.env) (cacheValid : CacheMeaning env cache)
    (satisfied : Constraints env.place env.env ((WitnessCircuit.body input cache).operations self) self) :
    let output := (WitnessCircuit.body input cache).output self
    Spec.Bytes (extractedMessage input cache self env) ∧
      values env output.1 = (Spec.digest (extractedMessage input cache self env)).toArray ∧
      CacheMeaning env output.2 := by
  have before : Sound env (WitnessCircuit.assignBytes input)
      (fun cells => InputRep env cells (BodyInput.extractMessage env cells)) := by
    intro incoming index incomingValid inputConstraints
    obtain ⟨rep, cacheEq⟩ := BodyInput.assignBytes_extracted input env range incoming index inputConstraints
    exact ⟨rep,cacheEq.symm ▸ incomingValid⟩
  obtain ⟨rep,value,finalCache⟩ := sound_bind_input (WitnessCircuit.assignBytes input) suffix
    (WitnessCircuit.body input) (source_body input) (Inputs.assignBytes_lawful input) env
    (fun cells => InputRep env cells (BodyInput.extractMessage env cells))
    (fun cells output => values env output = (Spec.digest (BodyInput.extractMessage env cells)).toArray)
    before (fun cells rep => suffix_sound env range spread cells _ rep) cache self cacheValid satisfied
  exact ⟨rep.1,value,finalCache⟩

/-- Honest source-body completeness identifies the message with the real input
program evaluations, derives all source constraints, and proves its SHA digest. -/
theorem body_complete (input : Vector (WitgenIR F 1) 24) (env : Placed ProverEnvironment F)
    (range : Range.ByteTable env.env.toEnvironment) (spread : Gates.SpreadTable env.env.toEnvironment)
    (honest : Inputs.HonestBytes env input.toList) :
    Complete env (WitnessCircuit.body input)
      (fun output => values env.toEnvironment output = (Spec.digest (BodyInput.honestMessage input env)).toArray) := by
  rw [source_body]
  apply complete_bind (Inputs.assignBytes_lawful input) (BodyInput.assignBytes_complete input env range honest)
  intro bytes rep
  exact suffix_complete env range spread bytes _ rep

end Midnight.SHA256.Semantics.Body
