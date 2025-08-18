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
  id_eq List.sum_cons List.sum_nil List.mem_append List.mem_cons or_false List.filter_append List.filter_singleton -- only in the current section

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

/--
Input for each row: either a block to process or nothing.
A chunk might contain less than 16 blocks, and `block_exists` indicates empty rows.
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
  localLength_eq := by
    simp only [circuit_norm, main, U32.AssertNormalized.circuit]
  subcircuitsConsistent := by
    simp only [circuit_norm, main, U32.AssertNormalized.circuit]
  Assumptions _ := True
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

namespace BLAKE3StateFirstHalf

def main (x : Var BLAKE3.BLAKE3State (F p)) : Circuit (F p) (Var (ProvableVector U32 8) (F p)) := do
  return x.take 8

/--
A subcircuit that takes the first eight elements of BLAKE3State
-/
def circuit : FormalCircuit (F p) BLAKE3.BLAKE3State (ProvableVector U32 8) where
  main
  localLength := 0
  Assumptions input := input.Normalized
  Spec input output := output = input.take 8 ∧ ∀ i : Fin 8, output[i].Normalized
  soundness := by
    circuit_proof_start [eval_vector_take]
    simp only [BLAKE3.BLAKE3State.Normalized] at h_assumptions
    rintro ⟨ i, h_i ⟩
    specialize h_assumptions i
    simp only [BLAKE3.BLAKE3State, ProvableVector] at ⊢ input
    change (input.take 8)[i].Normalized -- What is changed here?
    rw [Vector.getElem_take]
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
  -- Take first 8 elements for the chaining value
  let newCV8 ← BLAKE3StateFirstHalf.circuit newCV16

  -- Increment blocks_compressed
  let one32 : Var U32 (F p) := ⟨1, 0, 0, 0⟩
  let newBlocksCompressed ← Addition32.circuit { x := state.blocks_compressed, y := one32 }

  -- Conditionally select between new state and old state based on block_exists
  -- If block_exists = 1, use newState; if block_exists = 0, use state
  let muxedCV ← Conditional.circuit (M := ProvableVector U32 8) {
    selector := input.block_exists
    ifTrue := newCV8
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

def Spec (initialState : ProcessBlocksState (F p)) (inputs : List (BlockInput (F p))) i (_ : inputs.length = i) (state : ProcessBlocksState (F p)) :=
    initialState.Normalized →
    inputs.length < 2^32 →
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

/--
Lemma that handles the case when block_exists = 1 in the step function.
Shows that the step correctly processes a block using processBlockWords.
-/
private lemma step_process_block (env : Environment (F p))
    (acc_var : Var ProcessBlocksState (F p)) (x_var : Var BlockInput (F p))
    (acc : ProcessBlocksState (F p)) (x : BlockInput (F p))
    (h_eval : eval env acc_var = acc ∧ eval env x_var = x)
    (h_x : x.block_exists = 1)
    (h_holds : Circuit.ConstraintsHold.Soundness env ((step acc_var x_var).operations (size ProcessBlocksState + size BlockInput)))
    (acc_Normalized : acc.Normalized)
    (x_Normalized : x.Normalized)
    (blocks_compressed_not_many : acc.toChunkState.blocks_compressed < 2^32 - 1) :
    (eval env ((step acc_var x_var).output (size ProcessBlocksState + size BlockInput))).toChunkState =
      processBlockWords acc.toChunkState (x.block_data.map (·.value)) ∧
    (eval env ((step acc_var x_var).output (size ProcessBlocksState + size BlockInput))).Normalized := by
  have := p_large.elim
  simp only [step, circuit_norm, BLAKE3StateFirstHalf.circuit, BLAKE3.Compress.circuit, BLAKE3BlockInputNormalized.circuit, Addition32.circuit, IsZero.circuit, Conditional.circuit,
    BLAKE3StateFirstHalf.circuit, Conditional.Assumptions, IsZero.Assumptions, IsZero.Spec] at ⊢ h_holds
  provable_struct_simp
  simp only [h_eval, h_x] at ⊢ h_holds
  rcases h_holds with ⟨ h_assert_normalized, h_holds ⟩
  rcases h_holds with ⟨ h_iszero, h_holds ⟩
  rcases h_holds with ⟨ h_compress, h_holds ⟩
  dsimp only [BLAKE3.Compress.Assumptions, BLAKE3.Compress.Spec, BLAKE3.ApplyRounds.Assumptions] at h_compress
  simp only [ProcessBlocksState.Normalized] at acc_Normalized
  simp only [BlockInput.Normalized] at x_Normalized
  simp only [circuit_norm] at acc_Normalized x_Normalized
  specialize h_compress (by
    simp only [acc_Normalized, x_Normalized, Nat.ofNat_pos, circuit_norm, explicit_provable_type]
    constructor
    · linarith
    · split at h_iszero
      · norm_num at h_iszero ⊢
        simp only [h_iszero, circuit_norm]
        omega
      · norm_num at h_iszero ⊢
        simp only [h_iszero]
        norm_num
    )
  rcases h_holds with ⟨ h_first_half, h_holds ⟩
  specialize h_first_half (by simp only [h_compress])
  rcases h_holds with ⟨ h_addition, h_holds ⟩
  specialize h_addition (by
    simp only [Addition32.Assumptions, circuit_norm, ZMod.val_one]
    simp [acc_Normalized, circuit_norm])
  dsimp only [Addition32.Spec] at h_addition ⊢
  rcases h_holds with ⟨ h_vector_cond, h_u32_cond ⟩
  dsimp only [Conditional.Spec] at h_vector_cond h_u32_cond
  specialize h_vector_cond (by simp only [circuit_norm])
  specialize h_u32_cond (by simp only [circuit_norm])
  simp only [h_vector_cond, h_u32_cond, h_first_half] at h_addition ⊢
  simp only [ProcessBlocksState.Normalized] at ⊢ acc_Normalized
  simp only [ProcessBlocksState.toChunkState] at ⊢ h_addition blocks_compressed_not_many
  dsimp only [BLAKE3.BLAKE3State.value] at h_compress
  simp only [↓reduceIte, Nat.reduceMul,
      Nat.reduceAdd, Vector.take_eq_extract, Vector.map_extract, Pi.zero_apply] at ⊢ h_addition
  simp only [h_addition, processBlockWords]
  norm_num at ⊢ h_compress h_iszero
  simp only [h_compress.1, startFlag, circuit_norm]
  constructor
  · norm_num
    constructor
    · congr
      simp only [IsZero.circuit, circuit_norm, h_iszero]
      conv_rhs =>
        arg 1
        rw [U32.value_zero_iff_zero (by simp_all)]
      split <;> simp only [circuit_norm]
    · omega
  · aesop

lemma soundness : InductiveTable.Soundness (F p) ProcessBlocksState BlockInput Spec step := by
  intro initialState row_index env acc_var x_var acc x xs xs_len h_eval h_holds spec_previous initial_Normalized inputs_short
  specialize spec_previous (by assumption)
  specialize spec_previous (by
    simp only [circuit_norm] at inputs_short
    omega)
  simp only [circuit_norm]
  have input_normalized : x.Normalized := by
    simp only [circuit_norm, step] at h_holds ⊢
    rcases h_holds with ⟨ h_normalized, h_holds ⟩
    specialize h_normalized trivial
    simp only [BLAKE3BlockInputNormalized.circuit] at h_normalized
    provable_struct_simp
    simp_all
  constructor
  · intro input
    rintro (_ | _) <;> simp_all
  by_cases h_x : x.block_exists = 1
  · simp only [h_x, decide_true, cond_true]
    have one_op := step_process_block env acc_var x_var acc x h_eval h_x h_holds
      spec_previous.2.2.2 input_normalized
        (by
          simp only [circuit_norm, Nat.reducePow] at inputs_short
          omega)
    simp only [circuit_norm] at one_op
    simp only [one_op]
    constructor
    · simp only [processBlockWords, circuit_norm]
      omega
    simp [spec_previous, processBlocksWords]
  · simp only [h_x, decide_false, cond_false]
    simp only [circuit_norm, step] at h_holds
    provable_struct_simp
    have x_block_exists_zero : x_block_exists = 0 := by
      simp only [BlockInput.Normalized] at input_normalized
      cases input_normalized.1 with
      | inl _ => assumption
      | inr _ => contradiction
    simp only [x_block_exists_zero] at *
    simp only [Conditional.circuit, Conditional.Assumptions, Conditional.Spec, h_eval, step, circuit_norm] at h_holds ⊢
    norm_num at h_holds ⊢ spec_previous
    simp only [step, circuit_norm, h_holds, h_eval, ProcessBlocksState.toChunkState] at h_holds ⊢ spec_previous
    simp_all only [circuit_norm]
    omega

def InitialStateAssumptions (initialState : ProcessBlocksState (F p)) := initialState.Normalized

def InputAssumptions (i : ℕ) (input : BlockInput (F p)) :=
    input.Normalized ∧ i < 2^32

lemma completeness : InductiveTable.Completeness (F p) ProcessBlocksState BlockInput InputAssumptions InitialStateAssumptions Spec step := by
    intro initialState row_index env acc_var x_var acc x xs xs_len h_eval h_witnesses h_assumptions
    dsimp only [InitialStateAssumptions, InputAssumptions, Addition32.Assumptions] at *
    rcases h_assumptions with ⟨ h_init, ⟨ h_assumptions, ⟨ h_input, h_small ⟩ ⟩ ⟩
    specialize h_assumptions (by assumption)
    have := p_large.elim
    specialize h_assumptions (by omega)
    have h_assumptions : (_ ∧ _ ∧ _ ∧ _) := ⟨ h_init, ⟨ h_assumptions, h_input ⟩⟩
    simp only [circuit_norm, step] at ⊢ h_witnesses
    provable_struct_simp
    simp only [h_eval] at ⊢ h_witnesses
    dsimp only [ProcessBlocksState.Normalized] at h_assumptions
    dsimp only [IsZero.circuit, IsZero.Assumptions, BLAKE3.Compress.circuit, BLAKE3.Compress.Assumptions, BLAKE3.ApplyRounds.Assumptions]
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
      constructor
      · simp only [circuit_norm]
        omega
      constructor
      · simp_all
      constructor
      · simp only [circuit_norm]
        omega
      rcases h_witnesses with ⟨ h_witnesses_iszero, h_witnesses ⟩
      simp only [IsZero.circuit, IsZero.Assumptions] at h_witnesses_iszero
      specialize h_witnesses_iszero (by simp_all)
      simp only [IsZero.Spec] at h_witnesses_iszero
      constructor
      · split at h_witnesses_iszero
        · simp only [h_witnesses_iszero]
          norm_num
          simp only [circuit_norm]
          omega
        · simp only [h_witnesses_iszero]
          norm_num
      · norm_num
    constructor
    · dsimp only [BLAKE3StateFirstHalf.circuit]
      dsimp only [BLAKE3.Compress.circuit, BLAKE3.Compress.Assumptions, BLAKE3.Compress.Spec, BLAKE3.ApplyRounds.Assumptions] at h_witnesses
      rcases h_witnesses with ⟨ h_witnesses_iszero, ⟨ h_compress, _ ⟩ ⟩
      -- The following is a repetition of the above
      simp only [IsZero.circuit, IsZero.Assumptions] at h_witnesses_iszero
      specialize h_witnesses_iszero (by simp_all)
      simp only [IsZero.Spec] at h_witnesses_iszero
      specialize h_compress (by
        simp only [h_assumptions]
        constructor
        · trivial
        constructor
        · trivial
        constructor
        · simp only [circuit_norm]
          omega
        constructor
        · trivial
        simp only [circuit_norm]
        constructor
        · omega
        constructor
        · split at h_witnesses_iszero
          · simp only [h_witnesses_iszero]
            norm_num
            simp only [circuit_norm]
            omega
          · simp only [h_witnesses_iszero]
            norm_num
        · norm_num)
      simp only [h_compress]
    simp_all [Addition32.circuit, Addition32.Assumptions, h_assumptions, circuit_norm, Conditional.circuit, Conditional.Assumptions]

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

end
end Tables.BLAKE3.ProcessBlocksInductive
