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
  state : ProcessBlocksState F          -- Current state (cv, counter, blocks_compressed)
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

/--
Convert 64 bytes to 16 U32 words (little-endian).
Each U32 word is formed from 4 consecutive bytes.
This is just a data reorganization, no constraints needed.
-/
def bytesToWords {F} (bytes : Vector F 64) : Vector (U32 F) 16 :=
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
    ∀ i : Fin 16, (eval env (α := ProvableVector U32 16) (bytesToWords bytes_var))[i].Normalized := by
  rintro ⟨i, h_i⟩
  simp only [bytesToWords, Fin.getElem_fin]
  have h0 := h_bytes ⟨ i*4, by omega ⟩
  have h1 := h_bytes ⟨ i*4 + 1, by omega ⟩
  have h2 := h_bytes ⟨ i*4 + 2, by omega ⟩
  have h3 := h_bytes ⟨ i*4 + 3, by omega ⟩
  simp only [circuit_norm, eval_vector] at h0 h1 h2 h3 ⊢
  simp only [Vector.getElem_ofFn, U32.Normalized, explicit_provable_type, toVars]
  simp only [Vector.map_mk, List.map_toArray, List.map_cons, List.map_nil]
  and_intros <;> assumption

omit [Fact (Nat.Prime p)] p_large_enough in
lemma block_len_normalized (buffer_len : F p) (h : buffer_len.val ≤ 64) :
    (U32.mk buffer_len 0 0 0 : U32 (F p)).Normalized := by
  simp [U32.Normalized, ZMod.val_zero]
  omega

attribute [local circuit_norm] ZMod.val_zero ZMod.val_one chunkStart add_zero startFlag pow_zero zero_mul

/--
Main circuit that processes the final block of a chunk with CHUNK_END flag.
-/
def main {sentences : PropertySet (F p)} (order : SentenceOrder sentences) (input : Var Inputs (F p)) : Circuit sentences (Var (ProvableVector U32 8) (F p)) := do

  -- Convert bytes to words (just reorganization, no circuit needed)
  let block_words := bytesToWords input.buffer_data

  -- Compute start flag (CHUNK_START if blocks_compressed = 0)
  let isFirstBlock ← IsZero.circuit order input.state.blocks_compressed
  let start_flag : Var U32 (F p) := ⟨isFirstBlock*(chunkStart : F p), 0, 0, 0⟩

  -- Compute final flags: base_flags | start_flag | CHUNK_END
  let chunk_end_flag : Var U32 (F p) := ⟨(chunkEnd : F p), 0, 0, 0⟩
  let flags_with_start ← Or32.circuit order { x := input.base_flags, y := start_flag }
  let final_flags ← Or32.circuit order { x := flags_with_start, y := chunk_end_flag }

  -- Use compress
  let compress_input : Var ApplyRounds.Inputs (F p) := {
    chaining_value := input.state.chaining_value
    block_words := block_words
    counter_high := ⟨0, 0, 0, 0⟩
    counter_low := input.state.chunk_counter
    block_len := ⟨input.buffer_len, 0, 0, 0⟩  -- Convert length to U32
    flags := final_flags
  }
  let final_state ← Compress.circuit order compress_input
  return final_state.take 8

def elaborated {sentences : PropertySet (F p)} (order : SentenceOrder sentences) : ElaboratedCircuit (F p) sentences Inputs (ProvableVector U32 8) where
  main := main order
  localLength input := 2*4 + (4 + (4 + (5376 + 64)))

def Assumptions (input : Inputs (F p)) : Prop :=
  input.state.Normalized ∧
  input.buffer_len.val ≤ 64 ∧
  (∀ i : Fin 64, input.buffer_data[i].val < 256) ∧
  (∀ i : Fin 64, i.val ≥ input.buffer_len.val → input.buffer_data[i] = 0) ∧
  input.base_flags.Normalized

def CompletenessAssumptions {sentences : PropertySet (F p)} (_ : YieldContext sentences) (input : Inputs (F p)) : Prop :=
  Assumptions input

def Spec {sentences : PropertySet (F p)} (_checked : CheckedYields sentences) (input : Inputs (F p)) (output : ProvableVector U32 8 (F p)) : Prop :=
  let chunk_state : ChunkState := {
    chaining_value := input.state.chaining_value.map U32.value
    chunk_counter := input.state.chunk_counter.value
    blocks_compressed := input.state.blocks_compressed.value
    block_buffer := (input.buffer_data.take input.buffer_len.val).toList.map (·.val)
  }
  output.map U32.value = Specs.BLAKE3.finalizeChunk chunk_state input.base_flags.value ∧
  (∀ i : Fin 8, output[i].Normalized)

private lemma ZMod_val_chunkEnd :
    ZMod.val (n:=p) ↑chunkEnd = 2 := by
  have := p_large_enough.elim
  simp only [ZMod.val_natCast, chunkEnd, pow_one]
  rw [Nat.mod_eq_of_lt]; omega

omit p_large_enough in
private lemma eval_bytesToWords (env : Environment (F p))
    (input_var_buffer_data : Vector (Expression (F p)) 64) :
    eval env (α := ProvableVector U32 16) (bytesToWords input_var_buffer_data) =
      bytesToWords (eval (α:=ProvableVector field 64) env input_var_buffer_data) := by
  simp only [bytesToWords, circuit_norm, eval_vector]
  simp only [id_eq]
  rw [Vector.ext_iff]
  intro i hi
  simp only [Vector.getElem_map, Vector.getElem_ofFn, U32.eval_of_literal, U32.mk.injEq]
  have := getElem_eval_vector (α:=field) env input_var_buffer_data (i*4) (by omega)
  have := getElem_eval_vector (α:=field) env input_var_buffer_data (i*4 + 1) (by omega)
  have := getElem_eval_vector (α:=field) env input_var_buffer_data (i*4 + 2) (by omega)
  have := getElem_eval_vector (α:=field) env input_var_buffer_data (i*4 + 3) (by omega)
  simp_all

theorem soundness {sentences : PropertySet (F p)} (order : SentenceOrder sentences) : Soundness (F p) (elaborated order) order Assumptions Spec := by
  circuit_proof_start [IsZero.circuit, Or32.circuit, Compress.circuit, Compress.elaborated, ApplyRounds.circuit, ApplyRounds.elaborated,
    IsZero.Spec, IsZero.Assumptions,
    Or32.Spec, Or32.Assumptions,
    Compress.Spec, Compress.Assumptions,
    ApplyRounds.Spec, ApplyRounds.Assumptions,
    FinalStateUpdate.circuit, FinalStateUpdate.elaborated, FinalStateUpdate.Spec, FinalStateUpdate.Assumptions]
  constructor
  · sorry
  rcases h_holds with ⟨h_IsZero, h_Or32_1, h_Or32_2, h_Compress⟩
  simp_all only [chunkEnd, ProcessBlocksState.Normalized, ge_iff_le, id_eq, mul_one, Nat.ofNat_pos, and_self, and_true, true_and,
    Nat.reduceMul, and_imp, Nat.reducePow, mul_zero, add_zero]
  specialize h_Or32_1 (by
    split <;> simp [ZMod.val_one])

  simp_all only [forall_const]
  have val_two : (2 : F p).val = 2 := FieldUtils.val_lt_p 2 (by linarith [p_large_enough.elim])
  specialize h_Or32_2 (by simp [val_two])
  specialize h_Compress (by simp_all)
    (by apply bytesToWords_normalized; simp_all)
    (by linarith)
    (by simp_all)
  simp_all only [Fin.getElem_fin, Nat.cast_ofNat, BLAKE3State.value]
  have h_compress' := congrArg (fun v => v.take 8) h_Compress.2.1
  simp only [Vector.map_take, BLAKE3State, eval_vector] at h_compress'
  rw [← eval_vector] at h_compress'
  simp only [Vector.take_eq_extract, Vector.extract_mk, Nat.sub_zero, List.extract_toArray,
    List.extract_eq_drop_take, tsub_zero, List.drop_zero, List.take_succ_cons, List.take_zero,
    Vector.map_map] at h_compress'
  rw [← Vector.take_eq_extract] at h_compress'
  constructor
  · simp only [Vector.take_eq_extract, Vector.extract_mk, Nat.sub_zero, List.extract_toArray,
    List.extract_eq_drop_take, tsub_zero, List.drop_zero, List.take_succ_cons, List.take_zero]
    rw [h_compress']
    simp only [finalizeChunk]
    apply congrArg (fun (v : Vector ℕ 16) => v.take 8)
    have : Vector.map (U32.value ∘ eval env) (bytesToWords input_var_buffer_data) =
        (Specs.BLAKE3.bytesToWords
        (List.map (fun x ↦ ZMod.val x) (input_buffer_data.extract 0 (ZMod.val input_buffer_len)).toList)) := by
      clear h_compress' h_Or32_2 h_Or32_1 h_IsZero h_Compress
      rw [← Vector.map_map, ← eval_vector, eval_bytesToWords]
      simp only [h_input]
      simp only [bytesToWords, Specs.BLAKE3.bytesToWords]
      ext i hi
      simp only [explicit_provable_type, circuit_norm, Vector.getElem_ofFn, List.getElem_append,
        List.length_map, Vector.length_toList, Vector.getElem_extract,
        List.getElem_map, Vector.getElem_toList, List.getElem_replicate, dite_mul, zero_mul]
      have h_rest := h_assumptions.2.2.2.1
      congr <;> (
        split
        · ac_rfl
        · simp only [Nat.reducePow, mul_eq_zero, ZMod.val_eq_zero, OfNat.ofNat_ne_zero, or_false]
          exact h_rest ⟨ _, by omega ⟩ (by simp only; omega))
    rw [this]
    congr 1
    · rw [List.length_map, Vector.length_toList, left_eq_inf]
      linarith
    · congr
      simp only [startFlag, chunkStart]
      split <;> simp_all [circuit_norm]
  · rintro ⟨i, h_i⟩
    simp only [eval_vector]
    rw [Vector.getElem_map (i:=i) (n:=8) (α:=U32 (Expression (F p))) (β:=U32 (F p))]
    conv =>
      arg 1
      arg 2
      change (Vector.take _ 8)[i]'(by omega)
      rw [Vector.getElem_take]
    rcases h_Compress with ⟨_, h_Compress_value, h_Compress_Normalized⟩
    simp only [BLAKE3State.Normalized] at h_Compress_Normalized
    specialize h_Compress_Normalized ⟨ i, by omega ⟩
    simp only [getElem_eval_vector, h_Compress_Normalized]

theorem completeness {sentences : PropertySet (F p)} (order : SentenceOrder sentences) : Completeness (F p) sentences (elaborated order) CompletenessAssumptions := by
  circuit_proof_start[Or32.circuit, IsZero.circuit, Assumptions]
  apply And.intro
  · trivial
  rcases h_env with ⟨h_iszero, h_env⟩
  specialize h_iszero trivial
  simp only [IsZero.circuit, IsZero.Spec] at h_iszero
  apply And.intro
  · simp only [Or32.circuit, Or32.Assumptions, Or32.CompletenessAssumptions]
    apply And.intro
    · aesop
    · simp only [circuit_norm]
      simp only [h_iszero]
      split
      · norm_num
        simp only [circuit_norm]
        omega
      · norm_num
  rcases h_env with ⟨h_or, h_env⟩
  specialize h_or (by
    simp only [Or32.circuit, Or32.Assumptions, Or32.CompletenessAssumptions]
    apply And.intro
    · aesop
    · simp only [h_iszero]
      norm_num
      split
      · simp only [circuit_norm]
        omega
      · simp only [circuit_norm]
        norm_num)
  simp only [Or32.circuit, Or32.Spec] at h_or
  apply And.intro
  · simp only [Or32.circuit, Or32.Assumptions, Or32.CompletenessAssumptions]
    simp only [h_or]
    constructor
    · trivial
    simp only [circuit_norm]
    rw [ZMod_val_chunkEnd]
    omega
  simp only [Compress.circuit, Compress.Assumptions, ApplyRounds.Assumptions]
  rcases h_env with ⟨h_or2, h_env⟩
  specialize h_or2 (by
  · simp only [Or32.circuit, Or32.Assumptions, Or32.CompletenessAssumptions]
    simp only [h_or]
    constructor
    · trivial
    simp only [circuit_norm]
    rw [ZMod_val_chunkEnd]
    omega
  )
  simp only [Or32.circuit, Or32.Spec] at h_or2
  simp only [ProcessBlocksState.Normalized] at h_assumptions
  simp only [h_or2, h_assumptions, Compress.CompletenessAssumptions, Compress.Assumptions, ApplyRounds.Assumptions]
  simp only [circuit_norm]
  constructor
  · apply bytesToWords_normalized
    simp only [h_input]
    aesop
  omega

def circuit {sentences : PropertySet (F p)} (order : SentenceOrder sentences) : FormalCircuit order Inputs (ProvableVector U32 8) := {
  elaborated := elaborated order
  Assumptions
  CompletenessAssumptions
  completenessAssumptions_implies_assumptions := fun _ _ h => h
  Spec
  soundness := soundness order
  completeness := completeness order
}

end Gadgets.BLAKE3.FinalizeChunk
