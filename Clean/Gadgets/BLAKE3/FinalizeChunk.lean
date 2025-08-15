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
  rintro ⟨i, h_i⟩
  simp only [bytesToWords]
  simp only [id_eq, Fin.getElem_fin]
  have h0 := h_bytes (i * 4)
  have h1 := h_bytes (i * 4 + 1)
  have h2 := h_bytes (i * 4 + 2)
  have h3 := h_bytes (i * 4 + 3)
  simp only [circuit_norm, eval_vector] at h0 h1 h2 h3 ⊢
  simp only [Vector.getElem_ofFn, U32.Normalized, explicit_provable_type, toVars]
  simp only [Vector.map_mk, List.map_toArray, List.map_cons, List.map_nil]
  simp only [Fin.val_mul, Fin.val_add, Fin.val_natCast, Fin.val_ofNat', Nat.mod_eq_of_lt] at h0 h1 h2 h3
  simp only [id_eq, Fin.isValue, Nat.mod_mul_mod, Fin.val_one, Nat.mod_add_mod, Fin.val_two] at h0 h1 h2 h3
  constructor
  · calc
      _ = _ := by congr; omega
      _ < 256 := h0
  constructor
  · calc
      _ = _ := by congr; omega
      _ < 256 := h1
  constructor
  · calc
      _ = _ := by congr; omega
      _ < 256 := h2
  · calc
      _ = _ := by congr; omega
      _ < 256 := h3

omit [Fact (Nat.Prime p)] p_large_enough in
lemma block_len_normalized (buffer_len : F p) (h : buffer_len.val ≤ 64) :
    (U32.mk buffer_len 0 0 0 : U32 (F p)).Normalized := by
  simp [U32.Normalized, ZMod.val_zero]
  omega

attribute [local circuit_norm] ZMod.val_zero ZMod.val_one

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

private lemma ZMod_val_chunkEnd :
    ZMod.val (n:=p) ↑chunkEnd = 2 := by
  have := p_large_enough.elim
  simp only [ZMod.val_natCast, chunkEnd, pow_one]
  rw [Nat.mod_eq_of_lt]; omega

-- When I tried to prove all of these inline, I got 'deep recursion detected' in Lean kernel.
omit p_large_enough in
private lemma bytesToWords_value (env : Environment (F p))
    (input_var_buffer_data : Vector (Expression (F p)) 64)
    (input_buffer_data : Vector (F p) 64)
    (input_buffer_len : F p)
    (h_small : ZMod.val input_buffer_len ≤ 64)
    (h_data : eval (α:=ProvableVector field 64) env input_var_buffer_data = input_buffer_data)
    (h_rest : ∀ (i : Fin 64), ↑i ≥ ZMod.val input_buffer_len → input_buffer_data[↑i] = 0) :
    Vector.map U32.value (Vector.map (eval env) (bytesToWords input_var_buffer_data)) =
    Specs.BLAKE3.bytesToWords (List.map (fun x ↦ ZMod.val x) (input_buffer_data.take (ZMod.val input_buffer_len)).toList) := by
  simp only [bytesToWords, Specs.BLAKE3.bytesToWords]
  ext i h_i
  simp only [id_eq, Vector.map_map, Vector.getElem_map, Vector.getElem_ofFn]
  simp only [Vector.take_eq_extract, Vector.toArray_extract]
  simp only [Array.toList_extract, List.extract_eq_drop_take, tsub_zero]
  rw [Function.comp_apply]
  simp only [List.drop_zero, List.map_take, List.length_take, List.length_map, Array.length_toList,
    Vector.size_toArray, Nat.reducePow]
  simp only [explicit_provable_type, toVars]
  simp only [Vector.map_mk, List.map_toArray, List.map_cons, List.map_nil, U32.value]
  norm_num
  congr
  · rw [List.getElem_append]
    simp only [List.length_take]
    simp only [List.length_map]
    split
    · simp only [List.getElem_take]
      simp only [List.getElem_map, Array.getElem_toList, Vector.getElem_toArray]
      simp only [← ProvableType.eval_field]
      have := eval_vector (α:=field) (env:=env) (n:=64)
      rw [this] at h_data
      simp only [← h_data]
      simp
    · rename_i h_large
      simp only [List.getElem_replicate]
      simp only [← ProvableType.eval_field]
      have := eval_vector (α:=field) (env:=env) (n:=64)
      rw [this] at h_data
      simp only [← h_data] at h_rest
      rw [min_eq_left] at h_large
      rotate_left
      · convert h_small
        simp
      specialize h_rest (i * 4) (by
        simp only [Fin.val_mul]
        simp only [Fin.val_natCast, Fin.isValue, Nat.mod_mul_mod, ge_iff_le]
        omega)
      simp only [id_eq, Nat.cast_mul, Nat.cast_ofNat, Fin.isValue, Fin.getElem_fin,
        Vector.getElem_map] at h_rest
      simp only [ZMod.val_eq_zero]
      simp only [Fin.val_mul] at h_rest
      simp only [Fin.val_natCast, Fin.isValue, Nat.mod_mul_mod] at h_rest
      simp only [← h_rest]
      congr
      omega
  · rw [List.getElem_append]
    simp only [List.length_take]
    simp only [List.length_map]
    split
    · simp only [List.getElem_take]
      simp only [List.getElem_map, Array.getElem_toList, Vector.getElem_toArray]
      simp only [← ProvableType.eval_field]
      have := eval_vector (α:=field) (env:=env) (n:=64)
      rw [this] at h_data
      simp only [← h_data]
      simp
    · rename_i h_large
      simp only [List.getElem_replicate]
      simp only [← ProvableType.eval_field]
      have := eval_vector (α:=field) (env:=env) (n:=64)
      rw [this] at h_data
      simp only [← h_data] at h_rest
      rw [min_eq_left] at h_large
      rotate_left
      · convert h_small
        simp
      specialize h_rest (i * 4 + 1) (by
        simp only [Fin.val_add, Fin.val_mul]
        simp only [Fin.val_natCast, Fin.isValue, Nat.mod_mul_mod, ge_iff_le]
        omega)
      simp only [id_eq, Nat.cast_mul, Nat.cast_ofNat, Fin.isValue, Fin.getElem_fin,
        Vector.getElem_map] at h_rest
      simp only [ZMod.val_eq_zero]
      simp only [Fin.val_add, Fin.val_mul] at h_rest
      simp only [Fin.val_natCast, Fin.isValue, Nat.mod_mul_mod] at h_rest
      simp only [← h_rest]
      congr
      omega
  · rw [List.getElem_append]
    simp only [List.length_take]
    simp only [List.length_map]
    split
    · simp only [List.getElem_take]
      simp only [List.getElem_map, Array.getElem_toList, Vector.getElem_toArray]
      simp only [← ProvableType.eval_field]
      have := eval_vector (α:=field) (env:=env) (n:=64)
      rw [this] at h_data
      simp only [← h_data]
      simp
    · rename_i h_large
      simp only [List.getElem_replicate]
      simp only [← ProvableType.eval_field]
      have := eval_vector (α:=field) (env:=env) (n:=64)
      rw [this] at h_data
      simp only [← h_data] at h_rest
      rw [min_eq_left] at h_large
      rotate_left
      · convert h_small
        simp
      specialize h_rest (i * 4 + 2) (by
        simp only [Fin.val_add, Fin.val_mul]
        simp only [Fin.val_natCast, Fin.isValue, Nat.mod_mul_mod, ge_iff_le]
        omega)
      simp only [id_eq, Nat.cast_mul, Nat.cast_ofNat, Fin.isValue, Fin.getElem_fin,
        Vector.getElem_map] at h_rest
      simp only [ZMod.val_eq_zero]
      simp only [Fin.val_add, Fin.val_mul] at h_rest
      simp only [Fin.val_natCast, Fin.isValue, Nat.mod_mul_mod] at h_rest
      simp only [← h_rest]
      congr
      omega
  · rw [List.getElem_append]
    simp only [List.length_take]
    simp only [List.length_map]
    split
    · simp only [List.getElem_take]
      simp only [List.getElem_map, Array.getElem_toList, Vector.getElem_toArray]
      simp only [← ProvableType.eval_field]
      have := eval_vector (α:=field) (env:=env) (n:=64)
      rw [this] at h_data
      simp only [← h_data]
      simp
    · rename_i h_large
      simp only [List.getElem_replicate]
      simp only [← ProvableType.eval_field]
      have := eval_vector (α:=field) (env:=env) (n:=64)
      rw [this] at h_data
      simp only [← h_data] at h_rest
      rw [min_eq_left] at h_large
      rotate_left
      · convert h_small
        simp
      specialize h_rest (i * 4 + 3) (by
        simp only [Fin.val_add, Fin.val_mul]
        simp only [Fin.val_natCast, Fin.isValue, Nat.mod_mul_mod, ge_iff_le]
        omega)
      simp only [id_eq, Nat.cast_mul, Nat.cast_ofNat, Fin.isValue, Fin.getElem_fin,
        Vector.getElem_map] at h_rest
      simp only [ZMod.val_eq_zero]
      simp only [Fin.val_add, Fin.val_mul] at h_rest
      simp only [Fin.val_natCast, Fin.isValue, Nat.mod_mul_mod] at h_rest
      simp only [← h_rest]
      congr
      omega

theorem soundness : Soundness (F p) elaborated Assumptions Spec := by
  circuit_proof_start
  rcases h_holds with ⟨h_IsZero, h_holds⟩
  specialize h_IsZero trivial
  simp only [IsZero.circuit, IsZero.Spec] at h_IsZero
  rcases h_holds with ⟨h_Or32_1, h_holds⟩
  simp only [Or32.circuit, Or32.Assumptions, Or32.Spec] at h_Or32_1
  specialize h_Or32_1 (by
    constructor
    · simp_all
    · simp only [circuit_norm, h_IsZero]
      split
      · simp only [one_mul, ZMod.val_zero, Nat.ofNat_pos, and_self, and_true, chunkStart, pow_zero, Nat.cast_one, ZMod.val_one]
        linarith
      · simp only [zero_mul, ZMod.val_zero, Nat.ofNat_pos, and_self])
  rcases h_holds with ⟨h_Or32_2, h_Compress⟩
  simp only [Or32.circuit, Or32.Assumptions, Or32.Spec] at h_Or32_2
  specialize h_Or32_2 (by
    constructor
    · simp only [h_Or32_1]
    · simp only [circuit_norm, ZMod.val_zero]
      rw [ZMod_val_chunkEnd]
      decide)
  simp only [Compress.circuit, Compress.Assumptions, Compress.Spec] at h_Compress
  specialize h_Compress (by
    simp only [ApplyRounds.Assumptions]
    simp only [h_Or32_2.2]
    simp only [ProcessBlocksState.Normalized] at h_assumptions
    constructor
    · simp only [h_assumptions]
      trivial
    constructor
    · apply bytesToWords_normalized
      aesop
    constructor
    · simp only [circuit_norm]
      decide
    constructor
    · simp only [h_assumptions]
    · simp only [circuit_norm]
      omega)
  constructor
  · simp only [finalizeChunk]
    simp only [eval_vector]
    simp only [← Vector.map_take]
    rcases h_Compress with ⟨h_Compress_value, h_Compress_Normalized⟩
    clear h_Compress_Normalized
    simp only [BLAKE3State.value] at h_Compress_value
    simp only [eval_vector] at h_Compress_value
    simp only [h_Compress_value]
    clear h_Compress_value
    simp only [h_Or32_2]
    simp only [h_Or32_1]
    rw [bytesToWords_value] <;> try assumption
    · conv =>
        lhs
        arg 1
        arg 3
        arg 2
        simp only [eval, U32.value]
        simp only [toVars, toElements, fromElements]
        simp only [Nat.reducePow, Vector.map_mk, List.map_toArray, List.map_cons, List.map_nil,
          Nat.add_eq_left, mul_eq_zero, OfNat.ofNat_ne_zero, Nat.add_eq_zero, ZMod.val_eq_zero, or_false,
          and_self, false_or, Expression.eval]
        norm_num
      simp only [add_zero]
      conv_lhs =>
        arg 1
        arg 4
        simp only [explicit_provable_type, toVars]
        simp only [Vector.map_mk, List.map_toArray, List.map_cons, List.map_nil, U32.value, h_input]
        simp only [Expression.eval, ZMod.val_zero]
        ring_nf
      conv_rhs =>
        arg 1
        arg 4
        simp only [Vector.take_eq_extract, Vector.toArray_extract, Array.toList_extract,
          List.extract_eq_drop_take, tsub_zero, List.drop_zero, List.map_take, List.length_take,
          List.length_map, Array.length_toList, Vector.size_toArray]
        rw [Nat.min_eq_left (h:=by simp_all)]
      conv_lhs =>
        arg 1
        arg 5
        arg 2
        simp only [eval, U32.value]
        simp only [toVars, toElements, fromElements]
        simp only [Vector.map_mk, List.map_toArray, List.map_cons, List.map_nil, Nat.reducePow, Expression.eval]
        rw [ZMod_val_chunkEnd]
        simp only [chunkEnd, ZMod.val_zero]
        norm_num
      simp only [h_IsZero]
      simp only [ProcessBlocksState.Normalized] at h_assumptions
      have flag_eq : (if ∀ (i : Fin (size U32)), (toElements input_state_blocks_compressed)[i] = 0 then (1 : F p) else 0) = if input_state_blocks_compressed.value = 0 then 1 else 0 := by
        conv =>
          rhs
          arg 1
          rw [U32.value_zero_iff_components_zero (hx:=by simp only [h_assumptions])]
      rw [flag_eq]
      congr
      split
      · simp only [startFlag]
        simp_all only [circuit_norm]
        simp only [chunkStart]
        norm_num
        simp only [U32.value]
        simp only [ZMod.val_one, circuit_norm]
        ring
      · simp only [startFlag]
        simp_all only [circuit_norm]
        norm_num
        simp only [U32.value, ZMod.val_zero]
        ring
    · simp only [h_assumptions]
    · simp only [h_input]
    · simp_all
  · rintro ⟨i, h_i⟩
    simp only [eval_vector]
    rw [Vector.getElem_map (i:=i) (n:=8) (α:=U32 (Expression (F p))) (β:=U32 (F p))]

    conv =>
      arg 1
      arg 2
      change (Vector.take _ 8)[i]
      rw [Vector.getElem_take]

    rcases h_Compress with ⟨h_Compress_value, h_Compress_Normalized⟩
    simp only [BLAKE3State.Normalized] at h_Compress_Normalized
    specialize h_Compress_Normalized i
    clear h_Compress_value

    simp only [Fin.val_natCast] at h_Compress_Normalized
    have : i % 16 = i := by omega
    simp only [this] at h_Compress_Normalized
    simp only [getElem_eval_vector, h_Compress_Normalized]

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
    · simp only [U32.Normalized, Expression.eval, ZMod.val_zero, chunkStart]
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
    · simp only [h_iszero]
      split
      · simp only [chunkStart, circuit_norm]
        norm_num
        simp only [ZMod.val_one]
        omega
      · simp only [circuit_norm]
        norm_num)
  simp only [Or32.circuit, Or32.Spec] at h_or
  apply And.intro
  · simp only [Or32.circuit, Or32.Assumptions]
    simp only [h_or]
    constructor
    · trivial
    simp only [circuit_norm, ZMod.val_zero]
    rw [ZMod_val_chunkEnd]
    omega
  simp only [Compress.circuit, Compress.Assumptions, ApplyRounds.Assumptions]
  rcases h_env with ⟨h_or2, h_env⟩
  specialize h_or2 (by
  · simp only [Or32.circuit, Or32.Assumptions]
    simp only [h_or]
    constructor
    · trivial
    simp only [circuit_norm, ZMod.val_zero]
    rw [ZMod_val_chunkEnd]
    omega
  )
  simp only [Or32.circuit, Or32.Spec] at h_or2
  simp only [h_or2]
  simp only [ProcessBlocksState.Normalized] at h_assumptions
  simp only [h_assumptions]
  simp only [circuit_norm, ZMod.val_zero]
  simp only [Nat.ofNat_pos, and_self, and_true, true_and]
  constructor
  · apply bytesToWords_normalized
    simp only [h_input]
    aesop
  omega

def circuit : FormalCircuit (F p) Inputs (ProvableVector U32 8) := {
  elaborated with Assumptions, Spec, soundness, completeness
}

end Gadgets.BLAKE3.FinalizeChunk
