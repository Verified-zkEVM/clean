import Clean.Gadgets.BLAKE3.Compress
import Clean.Gadgets.BLAKE3.ApplyRounds
import Clean.Gadgets.BLAKE3.BLAKE3State
import Clean.Gadgets.Or.Or32
import Clean.Gadgets.IsZero
import Clean.Specs.BLAKE3
import Clean.Tables.BLAKE3.ProcessBlocksInductive
import Clean.Circuit.Provable
import Clean.Utils.Tactics

namespace Gadgets.BLAKE3.FinalizeChunk
variable {p : ℕ} [Fact p.Prime] [p_large_enough : Fact (p > 2^16 + 2^8)]
instance : Fact (p > 512) := .mk (by linarith [p_large_enough.elim])

open Specs.BLAKE3
open Tables.BLAKE3.ProcessBlocksInductive

/--
Input structure for finalizeChunk circuit.
-/
structure Inputs (F : Type) where
  state : ProcessBlocksState F           -- Current state (cv, counter, blocks_compressed)
  buffer_len : F                        -- Number of valid bytes (0-64)
  buffer_data : Vector F 64             -- Buffer bytes (only first buffer_len are valid, rest are zeros)
  base_flags : U32 F                    -- Additional flags (KEYED_HASH, etc.)

instance : ProvableStruct Inputs where
  components := [ProcessBlocksState, field, ProvableVector field 64, U32]
  toComponents := fun { state, buffer_len, buffer_data, base_flags } =>
    .cons state (.cons buffer_len (.cons buffer_data (.cons base_flags .nil)))
  fromComponents := fun xss =>
    match xss with
    | .cons state (.cons buffer_len (.cons buffer_data (.cons base_flags .nil))) =>
      { state, buffer_len, buffer_data, base_flags }
  fromComponents_toComponents := by intros; rfl

/--
Convert 64 bytes to 16 U32 words (little-endian).
Each U32 word is formed from 4 consecutive bytes.
This is just a data reorganization, no constraints needed.
-/
def bytesToWords (bytes : Var (ProvableVector field 64) (F p)) : Var (ProvableVector U32 16) (F p) :=
  Vector.ofFn fun (i : Fin 16) =>
    let base := i.val*4
    U32.mk 
      bytes[base]
      bytes[base + 1] 
      bytes[base + 2]
      bytes[base + 3]

/--
Main circuit that processes the final block of a chunk with CHUNK_END flag.
-/
def main (input : Var Inputs (F p)) : Circuit (F p) (Var (ProvableVector U32 8) (F p)) := do
  
  -- Convert bytes to words (just reorganization, no circuit needed)
  let block_words := bytesToWords input.buffer_data
  
  -- Compute start flag (CHUNK_START if blocks_compressed = 0)
  let isFirstBlock ← IsZero.circuit input.state.blocks_compressed
  let start_flag : Var U32 (F p) := ⟨isFirstBlock*(chunkStart : F p), 0, 0, 0⟩
  
  -- Compute final flags: base_flags | start_flag | CHUNK_END
  let chunk_end_flag : Var U32 (F p) := ⟨(chunkEnd : F p), 0, 0, 0⟩
  let flags_with_start ← Or32.circuit { x := input.base_flags, y := start_flag }
  let final_flags ← Or32.circuit { x := flags_with_start, y := chunk_end_flag }
  
  -- Prepare compress input
  let compress_input : Var ApplyRounds.Inputs (F p) := {
    chaining_value := input.state.chaining_value
    block_words := block_words
    counter_high := ⟨0, 0, 0, 0⟩
    counter_low := input.state.chunk_counter
    block_len := ⟨input.buffer_len, 0, 0, 0⟩  -- Convert length to U32
    flags := final_flags
  }
  
  -- Apply compress
  let final_state ← Compress.circuit compress_input
  
  -- Return first 8 words
  return final_state.take 8

instance elaborated : ElaboratedCircuit (F p) Inputs (ProvableVector U32 8) where
  main
  localLength input := 
    1 +  -- IsZero circuit
    4 +  -- First Or32 circuit
    4 +  -- Second Or32 circuit
    377  -- Compress circuit localLength (from Compress.lean)
  output := fun input offset =>
    let compress_offset := offset + 1 + 4 + 4
    let compress_out := Compress.circuit.output 
      { chaining_value := input.state.chaining_value
        block_words := bytesToWords input.buffer_data
        counter_high := ⟨0, 0, 0, 0⟩
        counter_low := input.state.chunk_counter
        block_len := ⟨input.buffer_len, 0, 0, 0⟩
        flags := default }  -- This would be computed from the Or32 circuits
      compress_offset
    compress_out.take 8
  localLength_eq := by simp [main, circuit_norm]; sorry
  output_eq := by simp [main, circuit_norm]; sorry

def Assumptions (input : Inputs (F p)) : Prop :=
  input.state.Normalized ∧
  input.buffer_len.val ≤ 64 ∧
  (∀ i : Fin 64, input.buffer_data[i].val < 256) ∧
  -- STRENGTHENED: Unused bytes must be zero
  (∀ i : Fin 64, i.val ≥ input.buffer_len.val → input.buffer_data[i] = 0) ∧
  input.base_flags.Normalized

def Spec (input : Inputs (F p)) (output : ProvableVector U32 8 (F p)) : Prop :=
  -- Convert input to spec types
  let chunk_state : ChunkState := {
    chaining_value := input.state.chaining_value.map U32.value
    chunk_counter := input.state.chunk_counter.value
    blocks_compressed := input.state.blocks_compressed.value
    block_buffer := (input.buffer_data.take input.buffer_len.val).toList.map (·.val)
  }
  -- Output matches spec function
  output.map U32.value = Specs.BLAKE3.finalizeChunk chunk_state input.base_flags.value ∧
  (∀ i : Fin 8, output[i].Normalized)

theorem soundness : Soundness (F p) elaborated Assumptions Spec := by
  circuit_proof_start
  sorry -- Will implement proof

theorem completeness : Completeness (F p) elaborated Assumptions := by
  circuit_proof_start
  sorry -- Will implement proof

def circuit : FormalCircuit (F p) Inputs (ProvableVector U32 8) := {
  elaborated with Assumptions, Spec, soundness, completeness
}

end Gadgets.BLAKE3.FinalizeChunk