import Midnight.SHA256.Semantics.Inputs
import Midnight.SHA256.Semantics.Digest

/-! Source-body adapters for verifier-extracted private bytes, initialization,
padding and input packing. Every action contract is derived from actual source
constraints or actual witness programs, before SHA round composition. -/
namespace Midnight.SHA256.Semantics.BodyInput
open Halo2 WitnessCircuit WitnessBuild Initialize RoundGadgets Linear

abbrev Cell := WitnessCircuit.Cell
abbrev Cache := WitnessCircuit.Cache

attribute [local irreducible] WitnessCircuit.assignBytes WitnessCircuit.initialState
  WitnessCircuit.pad WitnessCircuit.blockFromBytes

def values (env : Placed Environment F) (cells : Array Cell) : Array Nat :=
  cells.map (PrepareCircuit.cellValue env.place env.env)

def InputRep (env : Placed Environment F) (cells : Array Cell) (message : Spec.Message) : Prop :=
  Spec.Bytes message ∧ values env cells = message.toArray

def PaddedRep (env : Placed Environment F) (cells : Array Cell) (message : Spec.Message) : Prop :=
  cells.size = 64 ∧ Block.ByteInputs env cells ∧ (values env cells).toList = Spec.paddedBytes message

def BlockRep (env : Placed Environment F) (cells : Array Cell) (message : Spec.Message) : Prop :=
  values env cells = (Spec.block message).toArray ∧
    ∀ cell ∈ cells, PrepareCircuit.cellValue env.place env.env cell < 2^32

theorem inputRep_size {env : Placed Environment F} {cells : Array Cell} {message : Spec.Message}
    (rep : InputRep env cells message) : cells.size = 24 := by
  have hs := congrArg Array.size rep.2
  simpa only [values, Array.size_map, Vector.size_toArray] using hs

theorem inputRep_bytes {env : Placed Environment F} {cells : Array Cell} {message : Spec.Message}
    (rep : InputRep env cells message) : Block.ByteInputs env cells := by
  intro cell hc
  have hm : PrepareCircuit.cellValue env.place env.env cell ∈ values env cells :=
    Array.mem_map.mpr ⟨cell,hc,rfl⟩
  rw [rep.2] at hm
  obtain ⟨i, hi, heq⟩ := Array.mem_iff_getElem.mp hm
  change PrepareCircuit.cellValue env.place env.env cell < 256
  rw [← heq]
  exact rep.1 ⟨i, by simpa using hi⟩

/-- Verifier extraction from the actual input-assignment output cells. The size
premise is proved from that source loop, independently of private hint values. -/
def extract (env : Placed Environment F) (cells : Array Cell) (size : cells.size = 24) : Spec.Message :=
  ⟨values env cells, by simpa only [values, Array.size_map] using size⟩

theorem extract_rep (env : Placed Environment F) (cells : Array Cell) (size : cells.size = 24)
    (bytes : Block.ByteInputs env cells) : InputRep env cells (extract env cells size) := by
  refine ⟨?_, rfl⟩
  intro i
  have hi : i.val < cells.size := by simpa only [size] using i.isLt
  simpa only [Fin.getElem_fin, extract, Vector.getElem_mk, values, Array.getElem_map, PrepareCircuit.cellValue, Block.read] using
    bytes cells[i.val] (Array.getElem_mem hi)

/-- Total extractor used by the full circuit contract. On source outputs, the
proved size 24 guarantees no default array read is used. -/
def extractMessage (env : Placed Environment F) (cells : Array Cell) : Spec.Message :=
  Vector.mapFinRange 24 fun i => PrepareCircuit.cellValue env.place env.env cells[i.val]!

theorem extractMessage_eq (env : Placed Environment F) (cells : Array Cell) (size : cells.size = 24) :
    extractMessage env cells = extract env cells size := by
  apply Vector.ext
  intro i hi
  have hc : i < cells.size := by omega
  simp only [extractMessage, Vector.getElem_mapFinRange, extract, Vector.getElem_mk,
    values, Array.getElem_map, getElem!_pos cells i hc]

theorem inputRep_extract {env : Placed Environment F} {cells : Array Cell} {message : Spec.Message}
    (rep : InputRep env cells message) : extractMessage env cells = message := by
  rw [extractMessage_eq env cells (inputRep_size rep)]
  apply Vector.toArray_inj.mp
  exact rep.2

theorem assignBytes_extracted (input : Vector (WitgenIR F 1) 24) (env : Placed Environment F)
    (table : Range.ByteTable env.env) (cache : Cache) (self : RegionIndex)
    (satisfied : Constraints env.place env.env ((WitnessCircuit.assignBytes input cache).operations self) self) :
    let output := (WitnessCircuit.assignBytes input cache).output self
    InputRep env output.1 (extractMessage env output.1) ∧ output.2 = cache := by
  obtain ⟨bytes, size, cacheEq⟩ := Inputs.assignBytes_sound input cache self env table satisfied
  refine ⟨?_, cacheEq⟩
  change ((WitnessCircuit.assignBytes input cache).output self).1.size = 24 at size
  rw [extractMessage_eq env _ size]
  exact extract_rep env _ size bytes

/-- Prover-side message, used only in the honest-completeness contract. -/
def honestMessage (input : Vector (WitgenIR F 1) 24) (env : Placed ProverEnvironment F) : Spec.Message :=
  input.map fun program => (program.eval env)[0].val

theorem honestMessage_bytes (input : Vector (WitgenIR F 1) 24) (env : Placed ProverEnvironment F)
    (honest : Inputs.HonestBytes env input.toList) : Spec.Bytes (honestMessage input env) := by
  intro i
  simp only [honestMessage, Fin.getElem_fin, Vector.getElem_map]
  exact honest input[i] (Vector.mem_toList_iff.mpr (Vector.getElem_mem i.isLt))

theorem assignBytes_complete (input : Vector (WitgenIR F 1) 24) (env : Placed ProverEnvironment F)
    (table : Range.ByteTable env.env.toEnvironment) (honest : Inputs.HonestBytes env input.toList) :
    Complete env (WitnessCircuit.assignBytes input)
      (fun cells => InputRep env.toEnvironment cells (honestMessage input env)) := by
  intro cache self valid witnesses
  obtain ⟨hc, hv, hk⟩ := Inputs.assignBytes_complete input cache self env table honest witnesses
  refine ⟨hc, ⟨honestMessage_bytes input env honest, ?_⟩, ?_⟩
  · have h := congrArg (fun xs : Array F => xs.map ZMod.val) hv
    change (((WitnessCircuit.assignBytes input) cache).output self).1.map
      (fun cell => PrepareCircuit.cellValue env.toEnvironment.place env.toEnvironment.env cell) = _
    simpa only [values, Block.readArray, honestMessage, Vector.toArray_map, Array.map_map,
      Function.comp_def, PrepareCircuit.cellValue, Block.read, StateT.run] using h
  · exact hk.symm ▸ valid

theorem initialState_complete_action (env : Placed ProverEnvironment F) :
    Complete env WitnessCircuit.initialState (fun state => StateRep env.toEnvironment state Specs.SHA256.H0) := by
  intro cache self valid witnesses
  have hc := Initialize.initialState_complete cache self env witnesses
  exact ⟨hc, Initialize.initialState_sound env.toEnvironment cache self valid hc⟩

theorem field_message_eq {env : Placed Environment F} {cells : Array Cell} {message : Spec.Message}
    (rep : InputRep env cells message) :
    (Padding.message env cells (inputRep_size rep)).map scalarNat = message := by
  apply Vector.toArray_inj.mp
  have h : ((Padding.message env cells (inputRep_size rep)).map scalarNat).toArray = values env cells := by
    simp only [Padding.message, Vector.toArray_map, Block.readArray, values, Array.map_map]
    rfl
  exact h.trans rep.2

theorem pad_sound (env : Placed Environment F) (cells : Array Cell) (message : Spec.Message)
    (rep : InputRep env cells message) :
    Sound env (WitnessCircuit.pad cells) (fun output => PaddedRep env output message) := by
  intro cache self valid satisfied
  obtain ⟨size, bytes, reference, nextCache⟩ := Padding.pad_reference cells (inputRep_size rep)
    env (inputRep_bytes rep) cache self valid satisfied
  rw [field_message_eq rep] at reference
  exact ⟨⟨size, bytes, reference⟩, nextCache⟩

theorem pad_complete (env : Placed ProverEnvironment F) (cells : Array Cell) (message : Spec.Message)
    (rep : InputRep env.toEnvironment cells message) :
    Complete env (WitnessCircuit.pad cells) (fun output => PaddedRep env.toEnvironment output message) := by
  intro cache self valid witnesses
  have hc := (Padding.pad_complete cells cache self env valid witnesses).1
  exact ⟨hc, pad_sound env.toEnvironment cells message rep cache self valid hc⟩

theorem padded_vector {env : Placed Environment F} {cells : Array Cell} {message : Spec.Message}
    (rep : PaddedRep env cells message) : Block.byteVector env cells = Spec.paddedBlockBytes message := by
  apply Vector.ext
  intro i hi
  have h := congrArg (fun xs : List Nat => xs.getD i 0) rep.2.2
  simp only [Block.byteVector, Spec.paddedBlockBytes, Vector.getElem_mapFinRange]
  have hsize := rep.1
  have hc : i < cells.size := by omega
  simpa [values, PrepareCircuit.cellValue, Block.read, getElem!_pos, hc] using h

theorem block_sound (env : Placed Environment F) (cells : Array Cell) (message : Spec.Message)
    (rep : PaddedRep env cells message) :
    Sound env (WitnessCircuit.blockFromBytes cells) (fun output => BlockRep env output message) := by
  intro cache self valid satisfied
  obtain ⟨size, reference, nextCache⟩ := Block.blockFromBytes_reference cells rep.1 env rep.2.1
    cache self valid satisfied
  have hv : values env (((WitnessCircuit.blockFromBytes cells).run cache).output self).1 =
      (Spec.block message).toArray := by
    rw [padded_vector rep] at reference
    exact reference
  refine ⟨⟨hv, ?_⟩, nextCache⟩
  intro cell hc
  have hm : PrepareCircuit.cellValue env.place env.env cell ∈
      values env (((WitnessCircuit.blockFromBytes cells).run cache).output self).1 :=
    Array.mem_map.mpr ⟨cell,hc,rfl⟩
  rw [hv] at hm
  obtain ⟨i, hi, heq⟩ := Array.mem_iff_getElem.mp hm
  have bound : i < 16 := by simpa using hi
  have hp := Block.packedWord_lt env cells rep.1 rep.2.1 i bound
  have href := Block.packedWord_reference env cells ⟨i,bound⟩
  rw [padded_vector rep] at href
  rw [← heq]
  change (Specs.SHA256.bytesToBlock (Spec.paddedBlockBytes message))[(⟨i,bound⟩ : Fin 16)] < 2^32
  rw [← href]
  exact hp

theorem block_complete (env : Placed ProverEnvironment F) (cells : Array Cell) (message : Spec.Message)
    (rep : PaddedRep env.toEnvironment cells message) :
    Complete env (WitnessCircuit.blockFromBytes cells) (fun output => BlockRep env.toEnvironment output message) := by
  intro cache self valid witnesses
  have hc := (Block.blockFromBytes_complete cells cache self env valid witnesses).1
  exact ⟨hc, block_sound env.toEnvironment cells message rep cache self valid hc⟩

end Midnight.SHA256.Semantics.BodyInput
