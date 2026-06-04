/-
InductiveTable implementation for BLAKE3's processBlocks function.
This table has exactly 17 rows:
- Rows 0-15: Process up to 16 blocks (64 bytes each)
- Row 16: Final output containing the result of processBlocks
-/
import Clean.Table.Inductive
import Clean.Circuit.Loops
import Clean.Gadgets.BLAKE3.Compress
import Clean.Specs.BLAKE3
import Clean.Gadgets.Addition32.Addition32
import Clean.Gadgets.Conditional
import Clean.Gadgets.IsZero

namespace Tables.BLAKE3.ProcessBlocksInductive
open Gadgets
open Specs.BLAKE3

section
variable {p : ℕ} [Fact p.Prime] [p_large: Fact (p > 2^32)]
-- Add the additional constraint needed by Compress
instance : Fact (p > 2^16 + 2^8) := .mk (by
  cases p_large
  linarith
)

private lemma ZMod_val_64 :
    ZMod.val (n:=p) 64 = 64 := by
  rw [ZMod.val_ofNat_of_lt]
  have := p_large.elim
  linarith

attribute [local circuit_norm] blockLen ZMod.val_zero ZMod.val_one ZMod_val_64 add_zero zero_add chunkStart List.concat_eq_append List.length_append List.length_cons List.length_nil
  id_eq List.sum_cons List.sum_nil List.mem_append List.mem_cons or_false List.filter_append List.filter_singleton pow_zero -- only in the current section

/--
State maintained during block processing.
Corresponds to a simplified version of ChunkState.
-/
structure ProcessBlocksState (F : Type) where
  chaining_value : Vector (U32 F) 8    -- Current chaining value (8 × 32-bit words)
  chunk_counter : U32 F                 -- Which chunk number this is
  blocks_compressed : U32 F             -- Number of blocks compressed so far
deriving ProvableStruct

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

namespace BLAKE3ProcessBlocksStateNormalized

def main (x : Var ProcessBlocksState (F p)) : Circuit (F p) Unit := do
  Circuit.forEach x.chaining_value U32.AssertNormalized.circuit
  U32.AssertNormalized.circuit x.chunk_counter
  U32.AssertNormalized.circuit x.blocks_compressed

def circuit : FormalAssertion (F p) ProcessBlocksState where
  main
  Spec x := x.Normalized

  soundness := by
    circuit_proof_start [ProcessBlocksState.Normalized, U32.AssertNormalized.circuit]
    simp_all [← h_input, eval_vector]

  completeness := by
    circuit_proof_start [U32.AssertNormalized.circuit, getElem_eval_vector] -- provable_vector_simp wanted
    simp only [ProcessBlocksState.Normalized] at h_spec
    constructor
    · rintro ⟨i, h_i⟩
      rcases h_spec with ⟨h_spec, _⟩
      specialize h_spec ⟨ i, h_i ⟩
      convert h_spec
    simp_all

end BLAKE3ProcessBlocksStateNormalized

/--
Input for each row: either a block to process or nothing.
A chunk might contain less than 16 blocks, and `block_exists` indicates empty rows.
-/
structure BlockInput (F : Type) where
  block_exists : F                      -- 0 or 1 (boolean flag)
  block_data : Vector (U32 F) 16        -- 16 words = 64 bytes when exists
deriving ProvableStruct

def BlockInput.Normalized (input : BlockInput (F p)) : Prop :=
  IsBool input.block_exists ∧
  (∀ i : Fin 16, input.block_data[i].Normalized)

-- A circuit that asserts `BlockInput.Normalized`
namespace BLAKE3BlockInputNormalized

def main (x : Var BlockInput (F p)) : Circuit (F p) Unit := do
  assertBool x.block_exists
  Circuit.forEach x.block_data U32.AssertNormalized.circuit

def circuit : FormalAssertion (F p) BlockInput where
  main
  Spec x := x.Normalized

  soundness := by
    circuit_proof_start [BlockInput.Normalized, U32.AssertNormalized.circuit]
    constructor
    · simp_all
    simp only [←h_input, eval_vector] -- provable_vector_simp wanted
    simp_all

  completeness := by
    circuit_proof_start [U32.AssertNormalized.circuit]
    simp only [BlockInput.Normalized] at h_spec
    constructor
    · simp_all
    simp only [←h_input, eval_vector] at h_spec -- provable_vector_simp wanted
    simp_all

end BLAKE3BlockInputNormalized

attribute [local circuit_norm] eval_vector_takeShort Vector.map_takeShort

/--
The step function that processes one block or passes through the state.
-/
def step (state : Var ProcessBlocksState (F p)) (input : Var BlockInput (F p)) :
    Circuit (F p) (Var ProcessBlocksState (F p)) := do

  BLAKE3ProcessBlocksStateNormalized.circuit state -- redundant except in the first step
  BLAKE3BlockInputNormalized.circuit input

  -- Compute CHUNK_START flag (1 if blocks_compressed = 0, else 0)
  let isFirstBlock ← IsZero.circuit state.blocks_compressed

  let startFlagU32 : Var U32 (F p) :=  ⟨isFirstBlock * (Expression.const (F:=F p) chunkStart), 0, 0, 0⟩

  -- Prepare constants
  let zeroU32 : Var U32 (F p) := ⟨0, 0, 0, 0⟩
  let blockLenU32 : Var U32 (F p) := ⟨(blockLen : F p), 0, 0, 0⟩

  -- Prepare inputs for compress
  let compressInput : Var BLAKE3.ApplyRounds.Inputs (F p) := {
    chaining_value := state.chaining_value
    block_words := input.block_data
    counter_high := zeroU32
    counter_low := state.chunk_counter
    block_len := blockLenU32
    flags := startFlagU32
  }

  -- Apply compress to get new chaining value
  let newCV16 ← BLAKE3.Compress.circuit compressInput

  -- Increment blocks_compressed
  let one32 : Var U32 (F p) := ⟨1, 0, 0, 0⟩
  let newBlocksCompressed ← Addition32.circuit { x := state.blocks_compressed, y := one32 }

  -- Conditionally select between new state and old state based on block_exists
  -- If block_exists = 1, use newState; if block_exists = 0, use state
  let muxedCV ← Conditional.circuit (M := ProvableVector U32 8) {
    selector := input.block_exists
    ifTrue := newCV16.takeShort 8 (by omega)
    ifFalse := state.chaining_value
  }

  let muxedBlocksCompressed ← Conditional.circuit {
    selector := input.block_exists
    ifTrue := newBlocksCompressed
    ifFalse := state.blocks_compressed
  }

  return {
    chaining_value := muxedCV
    chunk_counter := state.chunk_counter  -- Never changes
    blocks_compressed := muxedBlocksCompressed
  }

def Spec (initialState : ProcessBlocksState (F p)) (inputs : List (BlockInput (F p))) i
  (_ : inputs.length = i) (state : ProcessBlocksState (F p)) (_ : ProverData (F p)) :=
    inputs.length < 2^32 →
    initialState.Normalized ∧
    (∀ input ∈ inputs, input.Normalized) ∧
    -- The spec relates the current state to the mathematical processBlocksWords function
    -- applied to the first i blocks from inputs (where block_exists = 1)
    let validBlocks := inputs |>.filter (·.block_exists = 1)
    let blockWords := validBlocks.map (fun b => b.block_data.map (·.value))
    let finalState := processBlocksWords initialState.toChunkState blockWords
    -- Current state matches the result of processing all valid blocks so far
    state.toChunkState.blocks_compressed < inputs.length ∧
    state.toChunkState = finalState ∧
    state.Normalized

omit [Fact p.Prime] p_large in
private lemma takeShort8_normalized {v : BLAKE3.BLAKE3State (F p)} (h8 : 8 < 16)
    (hv : v.Normalized) : ∀ i : Fin 8, (v.takeShort 8 h8)[i].Normalized := by
  intro i
  convert hv ⟨i.val, by omega⟩ using 1
  exact Vector.getElem_takeShort _ 8 h8 i.val i.isLt

-- The block-exists case is handled directly in `soundness` below.

lemma soundness : InductiveTable.Soundness (F p) ProcessBlocksState BlockInput Spec step := by
  intro _ _ env acc_var x_var acc x _ _ h_input h_holds spec_previous inputs_short
  simp only [circuit_norm, step] at inputs_short spec_previous h_holds ⊢
  simp only [circuit_norm] at h_input
  specialize spec_previous (by omega)
  have input_normalized : x.Normalized := by
    simp only [circuit_norm, BLAKE3BlockInputNormalized.circuit] at h_holds
    provable_struct_simp
    simp_all
  provable_struct_simp
  simp only [h_input] at h_holds spec_previous ⊢
  simp only [circuit_norm, BLAKE3BlockInputNormalized.circuit, IsZero.circuit,
    BLAKE3ProcessBlocksStateNormalized.circuit, BLAKE3.Compress.circuit, Addition32.circuit,
    seval] at inputs_short spec_previous h_holds ⊢
  simp only [IsZero.Assumptions, IsZero.Spec, Addition32.Assumptions, Addition32.Spec,
    BLAKE3.Compress.Assumptions, BLAKE3.Compress.Spec,
    BLAKE3.ApplyRounds.Assumptions
  ] at h_holds
  constructor
  · simp_all
  constructor
  · intro input
    rintro (_ | _) <;> simp_all
  by_cases h_x : x_block_exists = 1
  · simp only [h_x, decide_true, cond_true, circuit_norm] at *
    have h_state_norm := h_holds.1
    have h_input_norm := h_holds.2.1
    have h_iszero := h_holds.2.2.1
    have h_compress := h_holds.2.2.2.1
    have h_addition := h_holds.2.2.2.2.1
    have h_cv_cond := h_holds.2.2.2.2.2.1
    have h_blocks_cond := h_holds.2.2.2.2.2.2
    simp only [ProcessBlocksState.Normalized] at h_state_norm
    simp only [BlockInput.Normalized] at h_input_norm
    specialize h_compress (by
      rcases h_state_norm with ⟨h_cv_norm, h_counter_norm, h_blocks_norm⟩
      rcases h_input_norm with ⟨_, h_block_norm⟩
      exact ⟨h_cv_norm, h_block_norm, by norm_num, h_counter_norm,
        ⟨by norm_num, by norm_num⟩,
        by
          simp only [h_iszero]
          split <;> simp [ZMod.val_one, ZMod.val_zero],
        by norm_num⟩)
    specialize h_addition (by
      exact ⟨h_state_norm.2.2, by norm_num, by norm_num⟩)
    simp only [h_cv_cond, h_blocks_cond]
    simp only [ProcessBlocksState.toChunkState, processBlocksWords]
    rcases spec_previous with ⟨h_init_norm, h_inputs_norm, h_acc_lt, h_acc_eq, h_acc_norm⟩
    rcases h_compress with ⟨h_compress_value, h_compress_norm⟩
    rcases h_addition with ⟨h_add_value, h_add_norm⟩
    dsimp only [BLAKE3.BLAKE3State.value] at h_compress_value
    simp only [U32.value] at h_add_value
    simp only [ProcessBlocksState.toChunkState, U32.value] at h_acc_lt
    simp only [ProcessBlocksState.toChunkState] at h_acc_eq
    have h_add_value_nowrap :
        ZMod.val (env.get 5553) + ZMod.val (env.get 5555) * 256 +
            ZMod.val (env.get 5557) * 256 ^ 2 + ZMod.val (env.get 5559) * 256 ^ 3 =
          ZMod.val acc_blocks_compressed.x0 + ZMod.val acc_blocks_compressed.x1 * 256 +
              ZMod.val acc_blocks_compressed.x2 * 256 ^ 2 +
            ZMod.val acc_blocks_compressed.x3 * 256 ^ 3 + 1 := by
      rw [h_add_value]
      apply Nat.mod_eq_of_lt
      omega
    constructor
    · simp only [U32.value] at h_add_value ⊢
      rw [h_add_value_nowrap]
      omega
    constructor
    · simp only [List.map_append, List.foldl_append]
      simp only [processBlocksWords] at h_acc_eq ⊢
      rw [← h_acc_eq]
      simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil,
        processBlockWords, startFlag, blockLen]
      split
      · rename_i h_blocks_zero
        have h_blocks_zero' : acc_blocks_compressed = { x0 := 0, x1 := 0, x2 := 0, x3 := 0 } :=
          (U32.value_zero_iff_zero h_state_norm.2.2).mp h_blocks_zero
        subst acc_blocks_compressed
        simp only [Vector.map_takeShort, h_compress_value, h_iszero, ↓reduceIte, circuit_norm]
        rw [h_add_value_nowrap]
        dsimp only [U32.value]
        simp only [ZMod.val_zero, ChunkState.mk.injEq]
        norm_num
        ext i
        simp only [Vector.getElem_takeShort]
        rfl
      · rename_i h_blocks_nonzero
        have h_blocks_nonzero' : ¬acc_blocks_compressed = { x0 := 0, x1 := 0, x2 := 0, x3 := 0 } := by
          intro h_zero
          apply h_blocks_nonzero
          simp only [h_zero, circuit_norm, U32.value, ZMod.val_zero]
          ring
        simp only [Vector.map_takeShort, h_compress_value, h_iszero, h_blocks_nonzero', ↓reduceIte, circuit_norm]
        rw [h_add_value_nowrap]
        dsimp only [U32.value]
        simp only [ChunkState.mk.injEq]
        norm_num
        ext i
        simp only [Vector.getElem_takeShort]
        rfl
    constructor
    · exact takeShort8_normalized step._proof_2 h_compress_norm
    constructor
    · exact h_state_norm.2.1
    change ({ x0 := env.get 5553, x1 := env.get 5555, x2 := env.get 5557, x3 := env.get 5559 } : U32 (F p)).Normalized
    exact h_add_norm
  · simp only [h_x, decide_false, cond_false]
    simp only [circuit_norm] at h_holds
    have x_block_exists_zero : x_block_exists = 0 := by
      simp only [BlockInput.Normalized] at input_normalized
      cases input_normalized.1 with
      | inl _ => assumption
      | inr _ => contradiction
    simp only [x_block_exists_zero] at *
    simp only [circuit_norm] at h_holds ⊢
    simp only [circuit_norm, h_holds, ProcessBlocksState.toChunkState] at ⊢ spec_previous
    norm_num at h_holds ⊢
    simp_all only [circuit_norm]
    omega

def InitialStateAssumptions (initialState : ProcessBlocksState (F p)) (_ : ProverData (F p)) :=
  initialState.Normalized

def InputAssumptions (i : ℕ) (input : BlockInput (F p)) (_ : ProverData (F p)) :=
  input.Normalized ∧ i < 2^32

lemma completeness : InductiveTable.Completeness (F p) ProcessBlocksState BlockInput InputAssumptions InitialStateAssumptions Spec step := by
    have := p_large.elim
    intro _ _ _ _ _ _ _ _ _ h_eval h_witnesses h_assumptions
    dsimp only [InitialStateAssumptions, InputAssumptions, Addition32.Assumptions] at *
    rcases h_assumptions with ⟨ h_init, ⟨ h_assumptions, ⟨ h_input, h_small ⟩ ⟩ ⟩
    specialize h_assumptions (by omega)
    have h_assumptions : (_ ∧ _ ∧ _ ∧ _) := ⟨ h_init, ⟨ h_assumptions, h_input ⟩⟩
    simp only [circuit_norm, step] at ⊢ h_witnesses h_eval
    provable_struct_simp
    simp only [circuit_norm, h_eval] at ⊢ h_witnesses
    dsimp only [ProcessBlocksState.Normalized] at h_assumptions
    dsimp only [IsZero.circuit, IsZero.Assumptions, BLAKE3.Compress.circuit, BLAKE3.Compress.Assumptions, BLAKE3.ApplyRounds.Assumptions]
    constructor
    · simp_all [BLAKE3ProcessBlocksStateNormalized.circuit]
    constructor
    · simp_all [BLAKE3BlockInputNormalized.circuit]
    constructor
    · simp_all
    constructor
    · constructor
      · simp_all
      constructor
      · simp only [h_assumptions]
        trivial
      simp_all only [circuit_norm]
      constructor
      · omega
      constructor
      · omega
      rcases h_witnesses with ⟨ h_witnesses_iszero, h_witnesses ⟩
      simp only [IsZero.circuit, IsZero.Assumptions] at h_witnesses_iszero
      specialize h_witnesses_iszero (by simp_all)
      simp only [IsZero.Spec] at h_witnesses_iszero
      constructor
      · split at h_witnesses_iszero
        · simp only [circuit_norm] at h_witnesses_iszero
          simp only [h_witnesses_iszero]
          norm_num
          simp only [circuit_norm]
          omega
        · simp only [circuit_norm] at h_witnesses_iszero
          simp only [h_witnesses_iszero]
          norm_num
      · norm_num
    simp_all only [Addition32.circuit, Addition32.Assumptions]
    constructor
    · dsimp only [BLAKE3.Compress.circuit, BLAKE3.Compress.Assumptions, BLAKE3.Compress.Spec, BLAKE3.ApplyRounds.Assumptions] at h_witnesses
      rcases h_witnesses with ⟨ h_witnesses_iszero, ⟨ h_compress, _ ⟩ ⟩
      -- The following is a repetition of the above
      simp only [IsZero.circuit, IsZero.Assumptions] at h_witnesses_iszero
      specialize h_witnesses_iszero (by simp_all)
      simp only [IsZero.Spec] at h_witnesses_iszero
      specialize h_compress (by
        simp only [h_assumptions]
        simp only [circuit_norm]
        constructor
        · omega
        constructor
        · omega
        constructor
        · split at h_witnesses_iszero
          · simp only [IsZero.circuit, circuit_norm] at h_witnesses_iszero ⊢
            rw [h_witnesses_iszero]
            simp [ZMod.val_one]
          · simp only [IsZero.circuit, circuit_norm] at h_witnesses_iszero ⊢
            rw [h_witnesses_iszero]
            simp [ZMod.val_zero]
        · norm_num)
      simp_all [circuit_norm]
    trivial

/--
The InductiveTable for processBlocks.
-/
def table : InductiveTable (F p) ProcessBlocksState BlockInput where
  step
  Spec
  InitialStateAssumptions initialState _ := initialState.Normalized
  InputAssumptions i input _ := input.Normalized ∧ i < 2^32
  soundness
  completeness
  subcircuitsConsistent := by
    simp only [step, circuit_norm]
    omega
end
end Tables.BLAKE3.ProcessBlocksInductive
