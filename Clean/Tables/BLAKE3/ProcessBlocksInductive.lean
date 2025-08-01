/-
InductiveTable implementation for BLAKE3's processBlocks function.
This table has exactly 17 rows:
- Rows 0-15: Process up to 16 blocks (64 bytes each)
- Row 16: Final output containing the result of processBlocks
-/
import Clean.Table.Inductive
import Clean.Gadgets.BLAKE3.Compress
import Clean.Specs.BLAKE3
import Clean.Gadgets.Addition32.Addition32
import Clean.Gadgets.Conditional
import Clean.Gadgets.IsZeroU32

namespace Tables.BLAKE3.ProcessBlocksInductive
open Gadgets
open Specs.BLAKE3

variable {p : ℕ} [Fact p.Prime] [p_large: Fact (p > 2^32)]
-- Add the additional constraint needed by Compress
instance : Fact (p > 2^16 + 2^8) := .mk (by
  cases p_large
  linarith
)

omit p_large in
lemma U32_Normalized_componentwise env (a b c d : Var field (F p)):
    (eval (α := U32) env
    { x0 := a, x1 := b, x2 := c, x3 := d }).Normalized ↔
    ((eval env a).val < 256 ∧ (eval env b).val < 256 ∧ (eval env c).val < 256 ∧ (eval env d).val < 256) := by
  simp only [Parser.Attr.explicit_provable_type, ProvableType.eval, fromElements, toVars, toElements, Vector.map]
  simp only [List.map_toArray, List.map_cons, List.map_nil, U32.Normalized]

-- Using common lemma from U32 module
local notation "U32_zero_is_Normalized" => U32.zero_is_Normalized

-- Using common lemma from U32 module
local notation "U32_zero_value" => U32.zero_value

-- Using common lemma from U32 module
local notation "U32_one_is_Normalized" => U32.one_is_Normalized

-- Using common lemma from U32 module
local notation "U32_one_value" => U32.one_value

lemma U32_blockLen_is_Normalized (env : Environment (F p)) :
    (eval (α := U32) env { x0 := Expression.const ↑blockLen, x1 := 0, x2 := 0, x3 := 0 }).Normalized := by
  apply U32.const_is_Normalized
  simp only [blockLen]
  omega

lemma U32_blockLen_value (env : Environment (F p)) :
    (eval (α := U32) env { x0 := Expression.const ↑blockLen, x1 := 0, x2 := 0, x3 := 0 }).value = blockLen := by
  apply U32.const_value
  simp only [blockLen]
  omega

omit p_large in
lemma eval_env_mul (env : Environment (F p)) (a b : Var field (F p)) :
    (eval (α := field) env (Expression.mul a b : Var field (F p)) : F p) =
    (Expression.eval env a) * (Expression.eval env b) := by
  simp only [ProvableType.eval, fromElements, toVars, toElements]
  simp only [id_eq, Vector.map_mk, List.map_toArray, List.map_cons, List.map_nil]
  simp [Expression.eval]

/--
State maintained during block processing.
Corresponds to a simplified version of ChunkState.
-/
structure ProcessBlocksState (F : Type) where
  chaining_value : Vector (U32 F) 8    -- Current chaining value (8 × 32-bit words)
  chunk_counter : U32 F                 -- Which chunk number this is
  blocks_compressed : U32 F             -- Number of blocks compressed so far

instance : ProvableStruct ProcessBlocksState where
  components := [ProvableVector U32 8, U32, U32]
  toComponents := fun { chaining_value, chunk_counter, blocks_compressed } =>
    .cons chaining_value (.cons chunk_counter (.cons blocks_compressed .nil))
  fromComponents := fun xss =>
    match xss with
    | .cons cv (.cons cc (.cons bc .nil)) =>
      { chaining_value := cv, chunk_counter := cc, blocks_compressed := bc }
  fromComponents_toComponents := by
    intros
    rfl

/--
Convert ProcessBlocksState to ChunkState for integration with the spec.
-/
def ProcessBlocksState.toChunkState (state : ProcessBlocksState (F p)) : ChunkState :=
  { chaining_value := state.chaining_value.map (·.value)
  , chunk_counter := state.chunk_counter.value
  , blocks_compressed := state.blocks_compressed.value
  , block_buffer := []  -- ProcessBlocksState doesn't track partial blocks
  }

/--
Predicate that all components of ProcessBlocksState are normalized (valid U32 values).
-/
def ProcessBlocksState.Normalized (state : ProcessBlocksState (F p)) : Prop :=
  (∀ i : Fin 8, state.chaining_value[i].Normalized) ∧
  state.chunk_counter.Normalized ∧
  state.blocks_compressed.Normalized

lemma eval_acc_blocks_compressed (env : Environment (F p)) acc_chaining_value acc_chunk_counter acc_var_blocks_compressed
    acc_blocks_compressed
    (h_iszero : Expression.eval env (IsZeroU32.circuit.elaborated.output acc_var_blocks_compressed 105) =
      if acc_blocks_compressed.value = 0 then 1 else 0) :
    eval env acc_var_blocks_compressed = acc_blocks_compressed →
    ProcessBlocksState.Normalized
      { chaining_value := acc_chaining_value, chunk_counter := acc_chunk_counter,
        blocks_compressed := acc_blocks_compressed } →
    (eval env
            (U32.mk
                (Expression.mul (IsZeroU32.circuit.elaborated.output acc_var_blocks_compressed 105) (Expression.const ↑chunkStart))
                0 0 0 )).value =
    if acc_blocks_compressed.value = 0 then chunkStart else 0 := by
  intros h_eval h_normalized
  simp only [Parser.Attr.explicit_provable_type, ProvableType.eval, fromElements, toVars, toElements]
  simp only [Vector.map_mk, List.map_toArray, List.map_cons, List.map_nil, h_eval]
  simp only [ProcessBlocksState.Normalized] at h_normalized
  simp only [Expression.eval]
  simp only [chunkStart]
  simp only [h_iszero]
  split
  · simp only [U32.value]
    norm_num
    simp only [ZMod.val_one]
  · simp only [U32.value]
    norm_num

/--
Input for each row: either a block to process or nothing.
-/
structure BlockInput (F : Type) where
  block_exists : F                      -- 0 or 1 (boolean flag)
  block_data : Vector (U32 F) 16        -- 16 words = 64 bytes when exists

instance : ProvableStruct BlockInput where
  components := [field, ProvableVector U32 16]
  toComponents := fun { block_exists, block_data } =>
    .cons block_exists (.cons block_data .nil)
  fromComponents := fun xss =>
    match xss with
    | .cons block_exists (.cons data .nil) =>
      { block_exists := block_exists, block_data := data }
  fromComponents_toComponents := by
    intros
    rfl

/--
Predicate that all components of BlockInput are well-formed.
-/
def BlockInput.Normalized (input : BlockInput (F p)) : Prop :=
  (input.block_exists = 0 ∨ input.block_exists = 1) ∧
  (∀ i : Fin 16, input.block_data[i].Normalized)


namespace BLAKE3StateFirstHalf

def main (x : Var Gadgets.BLAKE3.BLAKE3State (F p)) : Circuit (F p) (Var (ProvableVector U32 8) (F p)) := do
  return x.take 8

/--
A subcircuit that takes the first eight elements of BLAKE3State
-/
def circuit : FormalCircuit (F p) Gadgets.BLAKE3.BLAKE3State (ProvableVector U32 8) where
  main := main
  localLength := 0
  Assumptions input := input.Normalized
  Spec input output := output = input.take 8 ∧ ∀ i : Fin 8, output[i].Normalized
  soundness := by
    circuit_proof_start
    have : (eval env (Vector.take input_var 8) : ProvableVector U32 8 (F p)) = (Vector.take input 8 : ProvableVector U32 8 (F p)) := by
      simp only [eval_vector, Vector.map_take]
      ext1
      rename_i i h_i
      -- the following is for adding [i] to h_input equations, automate
      simp only [eval_vector] at h_input
      simp only [Vector.ext_iff] at h_input
      specialize h_input i (by omega)
      simp only [Vector.getElem_map] at ⊢ h_input
      simp only [Vector.getElem_take]
      simp only [h_input]
    simp only [this]
    simp only [BLAKE3.BLAKE3State.Normalized] at h_assumptions
    constructor
    · trivial
    rintro ⟨ i, h_i ⟩
    specialize h_assumptions i
    simp only [BLAKE3.BLAKE3State, ProvableVector] at ⊢ input
    have getElem_take := Vector.getElem_take (xs := input) (i := i) (j := 8) (by omega)
    conv =>
      arg 1
      change (input.take 8)[i]
      rw [getElem_take]
    convert h_assumptions
    norm_num
    omega
  completeness := by circuit_proof_start

end BLAKE3StateFirstHalf

/--
The step function that processes one block or passes through the state.
-/
def step (state : Var ProcessBlocksState (F p)) (input : Var BlockInput (F p)) :
    Circuit (F p) (Var ProcessBlocksState (F p)) := do

  -- Add constraint that block_exists is boolean
  input.block_exists * (input.block_exists - 1) === 0

  -- Compute CHUNK_START flag (1 if blocks_compressed = 0, else 0)
  let isFirstBlock ← IsZeroU32.circuit state.blocks_compressed
  let startFlagU32 : Var U32 (F p) := ⟨Expression.mul isFirstBlock (Expression.const chunkStart), 0, 0, 0⟩

  -- Prepare constants
  let zeroU32 : Var U32 (F p) := ⟨0, 0, 0, 0⟩
  let blockLenU32 : Var U32 (F p) := ⟨(blockLen : F p), 0, 0, 0⟩

  -- Prepare inputs for compress
  let compressInput : Var Gadgets.BLAKE3.ApplyRounds.Inputs (F p) := {
    chaining_value := state.chaining_value
    block_words := input.block_data
    counter_high := zeroU32
    counter_low := state.chunk_counter
    block_len := blockLenU32
    flags := startFlagU32
  }

  -- Apply compress to get new chaining value
  let newCV16 ← Gadgets.BLAKE3.Compress.circuit compressInput
  -- Take first 8 elements for the chaining value
  let newCV8 ← BLAKE3StateFirstHalf.circuit newCV16

  -- Increment blocks_compressed
  let one32 : Var U32 (F p) := ⟨1, 0, 0, 0⟩
  let newBlocksCompressed ← Addition32.circuit { x := state.blocks_compressed, y := one32 }

  -- Create the new state (if block exists)
  let newState : Var ProcessBlocksState (F p) := {
    chaining_value := newCV8
    chunk_counter := state.chunk_counter
    blocks_compressed := newBlocksCompressed
  }

  -- Conditionally select between new state and old state based on block_exists
  -- If block_exists = 1, use newState; if block_exists = 0, use state
  let muxedCV ← Conditional.circuit (M := ProvableVector U32 8) {
    selector := input.block_exists
    ifTrue := newState.chaining_value
    ifFalse := state.chaining_value
  }

  let muxedBlocksCompressed ← Conditional.circuit (M := U32) {
    selector := input.block_exists
    ifTrue := newBlocksCompressed
    ifFalse := state.blocks_compressed
  }

  return {
    chaining_value := muxedCV
    chunk_counter := state.chunk_counter  -- Never changes
    blocks_compressed := muxedBlocksCompressed
  }

def Spec (initialState : ProcessBlocksState (F p)) (inputs : List (BlockInput (F p))) i (_ : inputs.length = i) (state : ProcessBlocksState (F p)) :=
    initialState.Normalized →
    (∀ input ∈ inputs, input.Normalized) →
    inputs.length < 2^32 →
    -- The spec relates the current state to the mathematical processBlocksWords function
    -- applied to the first i blocks from inputs (where block_exists = 1)
    let validBlocks := inputs.take i |>.filter (·.block_exists = 1)
    -- Extract the word data directly - no conversion needed!
    let blockWords := validBlocks.map (fun b => b.block_data.map (·.value))
    -- Use the initial state passed as parameter
    let finalState := processBlocksWords initialState.toChunkState blockWords
    -- Current state matches the result of processing all valid blocks so far
    state.toChunkState.blocks_compressed < inputs.length ∧
    state.toChunkState = finalState ∧
    state.Normalized

lemma soundness : InductiveTable.Soundness (F p) ProcessBlocksState BlockInput Spec step := by
  intro initialState row_index env acc_var x_var acc x xs xs_len h_eval h_holds spec_previous initial_Normalized input_Normalized inputs_short
  specialize spec_previous (by assumption)
  specialize spec_previous (by simp_all)
  specialize spec_previous (by
    simp only [List.concat_eq_append, List.length_append, List.length_cons, List.length_nil,
      zero_add, Nat.reducePow] at inputs_short
    omega)
  -- I think it's better to discharge conditions of spec_previous here
  rw [List.take_succ_eq_append_getElem]
  · rw [List.filter_append]
    have : (List.take row_index (xs.concat x)) = xs := by simp_all
    simp only [this]
    have : (xs.concat x)[row_index]'(by simp_all) = x := by simp_all
    simp only [this]
    have : (List.take row_index xs) = xs := by simp_all
    simp only [this] at spec_previous
    simp only [List.filter_singleton]
    by_cases h_x : x.block_exists = 1
    · simp only [h_x, decide_true, cond_true]
      have one_op :
          (eval env ((step acc_var x_var).output (size ProcessBlocksState + size BlockInput))).toChunkState =
            processBlockWords acc.toChunkState (x.block_data.map (·.value)) ∧
          (eval env ((step acc_var x_var).output (size ProcessBlocksState + size BlockInput))).Normalized := by
        simp only [step, circuit_norm] at ⊢ h_holds
        provable_struct_simp
        simp only [h_eval, h_x] at ⊢ h_holds
        rcases h_holds with ⟨ h_binary, h_holds ⟩
        clear h_binary
        rcases h_holds with ⟨ h_iszero, h_holds ⟩
        dsimp only [IsZeroU32.circuit, IsZeroU32.Assumptions, IsZeroU32.Spec] at h_iszero
        have : acc_blocks_compressed.Normalized := by
          simp only [ProcessBlocksState.Normalized] at spec_previous
          simp only [spec_previous]
        specialize h_iszero this
        rcases h_holds with ⟨ h_compress, h_holds ⟩
        dsimp only [BLAKE3.Compress.circuit, BLAKE3.Compress.Assumptions, BLAKE3.Compress.Spec, BLAKE3.ApplyRounds.Assumptions] at h_compress
        specialize h_compress (by
          clear h_holds
          simp only [ProcessBlocksState.Normalized] at spec_previous
          specialize input_Normalized { block_exists := x_block_exists, block_data := x_block_data } (by
            apply List.mem_of_getElem
            omega)
          simp only [BlockInput.Normalized] at input_Normalized
          simp only [spec_previous, input_Normalized, U32_zero_is_Normalized, U32_blockLen_is_Normalized]
          simp only [implies_true, id_eq, Nat.reduceMul, List.sum_cons, List.sum_nil, add_zero,
            Nat.reduceAdd, and_self, true_and, U32_Normalized_componentwise]
          constructor
          · rw [eval_env_mul]
            split at h_iszero
            · simp only [Expression.eval, chunkStart]
              norm_num at h_iszero ⊢
              simp only [h_iszero, ZMod.val_one]
              omega
            · norm_num at h_iszero ⊢
              simp only [h_iszero, Expression.eval, chunkStart]
              norm_num
          · simp only [ProvableType.eval, explicit_provable_type, toVars, Vector.map,
              List.map_toArray, List.map_cons, List.map_nil, Expression.eval,
              ZMod.val_zero, Nat.ofNat_pos]
        )
        rcases h_holds with ⟨ h_first_half, h_holds ⟩
        specialize h_first_half (by simp only [BLAKE3StateFirstHalf.circuit, h_compress])
        dsimp only [BLAKE3StateFirstHalf.circuit] at h_first_half
        rcases h_holds with ⟨ h_addition, h_holds ⟩
        specialize h_addition (by
          dsimp only [Addition32.circuit, Addition32.Assumptions]
          simp only [U32_one_is_Normalized]
          dsimp only [ProcessBlocksState.Normalized] at spec_previous
          simp [spec_previous])
        dsimp only [Addition32.circuit, Addition32.Spec] at h_addition ⊢
        rcases h_holds with ⟨ h_vector_cond, h_u32_cond ⟩
        specialize h_vector_cond (by simp only [Conditional.circuit, Conditional.Assumptions, circuit_norm])
        dsimp only [Conditional.circuit, Conditional.Spec] at h_vector_cond
        simp only [h_vector_cond] at h_addition ⊢
        specialize h_u32_cond (by simp only [Conditional.circuit, Conditional.Assumptions, circuit_norm])
        dsimp only [Conditional.circuit, Conditional.Spec] at h_u32_cond
        simp only [h_u32_cond] at h_addition ⊢
        dsimp only [BLAKE3StateFirstHalf.circuit] at h_addition ⊢
        simp only [h_first_half]
        dsimp only [Addition32.circuit]
        constructor
        · simp only [ProcessBlocksState.toChunkState]
          simp only [↓reduceIte, id_eq, Nat.reduceMul, List.sum_cons, List.sum_nil, add_zero,
            Nat.reduceAdd, Vector.take_eq_extract, Vector.map_extract, Pi.zero_apply] at ⊢ h_addition
          simp only [h_addition, processBlockWords]
          clear h_addition
          norm_num at ⊢ h_compress
          constructor
          · dsimp only [BLAKE3.BLAKE3State.value] at h_compress
            simp only [h_compress.1]
            clear h_compress
            simp only [U32_zero_value, startFlag, U32_blockLen_value]
            norm_num at h_iszero
            rw [eval_acc_blocks_compressed (acc_chaining_value := acc_chaining_value) (acc_chunk_counter := acc_chunk_counter)
                  (acc_var_blocks_compressed := acc_var_blocks_compressed) (acc_blocks_compressed := acc_blocks_compressed) (h_iszero := h_iszero)]
            · norm_num
            · simp only [h_eval]
            · simp only [spec_previous]
          · simp only [U32_one_value]
            simp only [ProcessBlocksState.toChunkState] at spec_previous
            simp only [List.concat_eq_append, List.length_append, List.length_cons, List.length_nil,
              zero_add, Nat.reducePow] at inputs_short
            omega
        · simp only [ProcessBlocksState.Normalized]
          constructor
          · aesop
          · simp only [↓reduceIte, Nat.reduceMul, List.sum_cons, List.sum_nil, add_zero,
            Nat.reduceAdd, id_eq, Pi.zero_apply] at ⊢ h_addition
            simp only [h_addition.2]
            dsimp only [ProcessBlocksState.Normalized] at spec_previous
            simp only [spec_previous]
            trivial
      simp only [one_op]
      constructor
      · simp only [processBlockWords]
        simp only [List.concat_eq_append, List.length_append, List.length_cons, List.length_nil,
          zero_add, add_lt_add_iff_right]
        omega
      simp only [spec_previous, List.map_append, List.map_cons, List.map_nil, processBlocksWords, List.foldl_append, List.foldl_cons, List.foldl_nil]
      trivial
    · simp only [h_x, decide_false, cond_false, List.append_nil]
      have no_op : (eval env ((step acc_var x_var).output (size ProcessBlocksState + size BlockInput))) = acc := by
        simp only [circuit_norm, step] at h_holds
        provable_struct_simp
        rcases h_holds with ⟨ hh0, hh1 ⟩
        have x_block_exists_zero : x_block_exists = 0 := by
          simp only [h_eval] at hh0
          rw [mul_eq_zero (M₀ := F p)] at hh0
          cases hh0 with
          | inl hh0 => assumption
          | inr hh0 =>
              rw [add_neg_eq_zero] at hh0
              contradiction
        simp only [x_block_exists_zero] at *
        simp only [Conditional.circuit, Conditional.Assumptions, Conditional.Spec, h_eval, step, circuit_norm] at hh1 ⊢
        norm_num at hh1 ⊢
        simp only [step, circuit_norm, hh1, h_eval]
      simp only [no_op]
      constructor
      · simp only [List.concat_eq_append, List.length_append, List.length_cons, List.length_nil,
        zero_add]
        omega
      · simp [spec_previous]
  · aesop

def InitialStateAssumptions (initialState : ProcessBlocksState (F p)) := initialState.Normalized

def InputAssumptions (i : ℕ) (input : BlockInput (F p)) :=
    input.Normalized ∧ i < 2^32

lemma completeness : InductiveTable.Completeness (F p) ProcessBlocksState BlockInput InputAssumptions InitialStateAssumptions Spec step := by
    intro initialState row_index env acc_var x_var acc x xs xs_len h_eval h_witnesses h_assumptions
    dsimp only [InitialStateAssumptions, InputAssumptions] at *
    rcases h_assumptions with ⟨ h_init, ⟨ h_inputs, ⟨ h_assumptions, ⟨ h_input, h_small ⟩ ⟩ ⟩ ⟩
    specialize h_assumptions (by assumption)
    specialize h_assumptions (by
      intro input input_mem
      obtain ⟨ i, h_i, get_input ⟩ := List.getElem_of_mem input_mem
      rw [← get_input]
      specialize h_inputs i (by omega)
      simp only [h_inputs])
    specialize h_assumptions (by omega)
    have h_assumptions : (_ ∧ _ ∧ _ ∧ _) := ⟨ h_init, ⟨ h_inputs, ⟨ h_assumptions, h_input ⟩⟩⟩
    simp only [circuit_norm, step] at ⊢ h_witnesses
    provable_struct_simp
    simp only [h_eval] at ⊢ h_witnesses
    dsimp only [BlockInput.Normalized, ProcessBlocksState.Normalized] at h_assumptions
    dsimp only [IsZeroU32.circuit, IsZeroU32.Assumptions, BLAKE3.Compress.circuit, BLAKE3.Compress.Assumptions, BLAKE3.ApplyRounds.Assumptions]
    constructor
    · have : x_block_exists = 0 ∨ x_block_exists = 1 := by tauto
      cases this with
      | inl h =>
          simp only [h]
          ring_nf
      | inr h =>
          simp only [h]
          ring_nf
    constructor
    · simp_all
    constructor
    · constructor
      · simp_all
      constructor
      · simp only [h_assumptions]
        native_decide
      constructor
      · -- goal looks lemma-worthy
        simp only [U32_zero_is_Normalized]
      constructor
      · simp_all
      constructor
      · -- goal looks lemma-worthy
        simp only [U32_blockLen_is_Normalized]
      simp only [chunkStart]
      rcases h_witnesses with ⟨ h_witnesses_iszero, h_witnesses ⟩
      simp only [IsZeroU32.circuit, IsZeroU32.Assumptions] at h_witnesses_iszero
      specialize h_witnesses_iszero (by simp_all)
      simp only [IsZeroU32.Spec] at h_witnesses_iszero
      simp only [U32_Normalized_componentwise]
      constructor
      · rw [eval_env_mul]
        split at h_witnesses_iszero
        · simp only [h_witnesses_iszero, Expression.eval]
          norm_num
          simp only [ZMod.val_one]
          omega
        · simp only [h_witnesses_iszero, Expression.eval]
          norm_num
      · norm_num
        simp only [ProvableType.eval, explicit_provable_type, toVars, Vector.map,
          List.map_toArray, List.map_cons, List.map_nil, Expression.eval,
          ZMod.val_zero, Nat.ofNat_pos]
    constructor
    · dsimp only [BLAKE3StateFirstHalf.circuit]
      dsimp only [BLAKE3.Compress.circuit, BLAKE3.Compress.Assumptions, BLAKE3.Compress.Spec, BLAKE3.ApplyRounds.Assumptions] at h_witnesses
      rcases h_witnesses with ⟨ h_witnesses_iszero, ⟨ h_compress, _ ⟩ ⟩
      -- The following is a repetition of the above
      simp only [IsZeroU32.circuit, IsZeroU32.Assumptions] at h_witnesses_iszero
      specialize h_witnesses_iszero (by simp_all)
      simp only [IsZeroU32.Spec] at h_witnesses_iszero
      specialize h_compress (by
        simp only [h_assumptions]
        simp only [U32_blockLen_is_Normalized, U32_zero_is_Normalized]
        constructor
        · trivial
        constructor
        · trivial
        constructor
        · trivial
        constructor
        · trivial
        constructor
        · trivial
        simp only [U32_Normalized_componentwise, chunkStart]
        constructor
        · rw [eval_env_mul]
          split at h_witnesses_iszero
          · simp only [h_witnesses_iszero, Expression.eval]
            norm_num
            simp only [ZMod.val_one]
            omega
          · simp only [h_witnesses_iszero, Expression.eval]
            norm_num
        · norm_num
          simp only [ProvableType.eval, explicit_provable_type, toVars, Vector.map,
            List.map_toArray, List.map_cons, List.map_nil, Expression.eval,
            ZMod.val_zero, Nat.ofNat_pos])
      simp only [h_compress]
    simp_all [Addition32.circuit, Addition32.Assumptions, h_assumptions, U32_one_is_Normalized, Conditional.circuit, Conditional.Assumptions, IsBool]

/--
The InductiveTable for processBlocks.
-/
def table : InductiveTable (F p) ProcessBlocksState BlockInput where
  step

  Spec

  InitialStateAssumptions initialState := initialState.Normalized
  InputAssumptions i input :=
    input.Normalized ∧ i < 2^32

  soundness
  completeness
  subcircuitsConsistent := by
    intros
    dsimp only [step]
    simp only [circuit_norm]
    omega

/--
Create a trace for processBlocks with given input blocks.
Pads with empty blocks to reach exactly 17 rows.
-/
def createTrace (_initialCV : Vector (U32 (F p)) 8) (_chunkCounter : U32 (F p))
    (blocks : List (List Nat)) : List (BlockInput (F p)) :=
  -- Convert blocks to BlockInput format
  let blockInputs := blocks.map (fun block =>
    let words := (List.range 16).map (fun i =>
      let bytes := block.drop (i * 4) |>.take 4
      let value := bytes.zipIdx.foldl (fun acc (byte, idx) =>
        acc + byte * 256^idx
      ) 0
      U32.fromByte ⟨value % 256, by omega⟩  -- Simplified: just use first byte
    )
    { block_exists := 1
    , block_data := Vector.mk words.toArray (by
      simp only [List.length_map, List.length_range, List.size_toArray]
      rfl) }
  )
  -- Pad with empty blocks
  let emptyBlock : BlockInput (F p) :=
    { block_exists := 0
    , block_data := Vector.mk (List.replicate 16 (U32.fromByte 0)).toArray (by simp) }
  let paddedInputs := blockInputs ++ List.replicate (16 - blocks.length) emptyBlock
  paddedInputs

-- TODO: Define extractFinalState once we have the proper trace type
-- This would extract the final state from row 16 of the table

end Tables.BLAKE3.ProcessBlocksInductive
