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

omit p_large_enough in
lemma bytesToWords_normalized (env : Environment (F p)) (bytes_var : Var (ProvableVector field 64) (F p))
    (h_bytes : ∀ i : Fin 64, (eval env bytes_var)[i].val < 256) :
    ∀ i : Fin 16, (eval env (bytesToWords bytes_var))[i].Normalized := by
  intro i
  simp only [bytesToWords]
  simp only [id_eq, Fin.getElem_fin]
  have h0 := h_bytes (↑i * 4)
  have h1 := h_bytes (↑i * 4 + 1)
  have h2 := h_bytes (↑i * 4 + 2)
  have h3 := h_bytes (↑i * 4 + 3)
  simp only [circuit_norm, eval_vector] at h0 h1 h2 h3 ⊢
  simp only [Vector.getElem_ofFn]
  simp only [U32.Normalized]
  simp only [explicit_provable_type, toVars]
  simp only [Vector.map_mk, List.map_toArray, List.map_cons, List.map_nil]
  constructor
  · convert h0
    simp only [Fin.val_mul, Fin.val_natCast, Fin.val_ofNat', Nat.mod_eq_of_lt]
    omega
  constructor
  · convert h1
    simp only [Fin.val_mul, Fin.val_add, Fin.val_natCast, Fin.val_ofNat', Nat.mod_eq_of_lt]
    omega
  constructor
  · convert h2
    simp only [Fin.val_mul, Fin.val_add, Fin.val_natCast, Fin.val_ofNat', Nat.mod_eq_of_lt]
    omega
  · convert h3
    simp only [Fin.val_mul, Fin.val_add, Fin.val_natCast, Fin.val_ofNat', Nat.mod_eq_of_lt]
    omega


omit [Fact (Nat.Prime p)] p_large_enough in
lemma block_len_normalized (buffer_len : F p) (h : buffer_len.val ≤ 64) :
    (U32.mk buffer_len 0 0 0 : U32 (F p)).Normalized := by
  simp [U32.Normalized, ZMod.val_zero]
  omega

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
  localLength input := 2 * 4 + (4 + (4 + (5376 + 64)))

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

  sorry

theorem completeness : Completeness (F p) elaborated Assumptions := by
  circuit_proof_start
  apply And.intro
  · trivial
  rcases h_env with ⟨h_iszero, h_env⟩
  specialize h_iszero trivial
  simp only [IsZero.circuit, IsZero.Spec] at h_iszero
  apply And.intro
  · simp only [Or32.circuit, Or32.Assumptions]
    apply And.intro
    · aesop
    · simp only [ProvableType.eval]
      simp only [id_eq]
      simp only [fromElements, toVars, toElements]
      simp only [Vector.map_mk, List.map_toArray, List.map_cons, List.map_nil]
      simp only [U32.Normalized, Expression.eval, ZMod.val_zero, chunkStart]
      simp only [h_iszero]
      split
      · norm_num
        simp only [ZMod.val_one]
        omega
      · norm_num
  rcases h_env with ⟨h_or, h_env⟩
  specialize h_or (by
    simp only [Or32.circuit, Or32.Assumptions]
    apply And.intro
    · aesop
    · simp only [ProvableType.eval]
      simp only [id_eq]
      simp only [fromElements, toVars, toElements]
      simp only [Vector.map_mk, List.map_toArray, List.map_cons, List.map_nil]
      simp only [U32.Normalized, Expression.eval, ZMod.val_zero, chunkStart]
      simp only [h_iszero]
      split
      · norm_num
        simp only [ZMod.val_one]
        omega
      · norm_num)
  simp only [Or32.circuit, Or32.Spec] at h_or
  apply And.intro
  · simp only [Or32.circuit, Or32.Assumptions]
    simp only [h_or]
    constructor
    · trivial
    apply U32.const_is_Normalized
    native_decide
  simp only [Compress.circuit, Compress.Assumptions, ApplyRounds.Assumptions]
  rcases h_env with ⟨h_or2, h_env⟩
  specialize h_or2 (by
  · simp only [Or32.circuit, Or32.Assumptions]
    simp only [h_or]
    constructor
    · trivial
    apply U32.const_is_Normalized
    native_decide
  )
  simp only [Or32.circuit, Or32.Spec] at h_or2
  simp only [h_or2]
  simp only [ProcessBlocksState.Normalized] at h_assumptions
  simp only [h_assumptions]
  simp only [U32.zero_is_Normalized]



  sorry

def circuit : FormalCircuit (F p) Inputs (ProvableVector U32 8) := {
  elaborated with Assumptions, Spec, soundness, completeness
}

end Gadgets.BLAKE3.FinalizeChunk
