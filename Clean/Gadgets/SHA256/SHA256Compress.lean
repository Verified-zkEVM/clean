import Clean.Gadgets.SHA256.SHA256Round
import Clean.Gadgets.SHA256.SHA256Schedule
import Clean.Gadgets.SHA256.Add32
import Clean.Specs.SHA256

section
variable {p : ℕ} [Fact p.Prime] [Fact (p > 2)]

namespace Gadgets.SHA256

/-!
# SHA-256 Compression

Applies 64 rounds of the SHA-256 compression function and then adds the original
state to produce the final output (the Davies–Meyer construction).

Constraint counts per sub-circuit (all as witness variable counts):
  xor32 = 32, add32 = 33, ch32 = 32, maj32 = 64 (two witnessVector 32),
  upperSigma0/1 = 2×xor32 = 64.
  sha256Round = 64+32+33+33+33+33+64+64+33+33+33 = 421 per round.
-/

/-- Apply 64 rounds of SHA-256 to `state` using the pre-computed message schedule `w`.
    ConstantLength is provided explicitly (421 witnesses/round) to avoid synthesis timeout. -/
@[irreducible] def sha256Compress
    (state : Vector (Var (fields 32) (F p)) 8)
    (w : Vector (Var (fields 32) (F p)) 64)
    : Circuit (F p) (Vector (Var (fields 32) (F p)) 8) :=
  Circuit.foldlRange 64 state
    (fun s (i : Fin 64) => sha256Round s (constWord32 Specs.SHA256.K[i].toNat) w[i])
    ⟨455, fun _ _ => by
        simp [circuit_norm, sha256Round, upperSigma1, upperSigma0, ch32, maj32, add32, xor32]⟩

/-- Process one 512-bit block.

    `state` is the current hash state (8 words).
    `block` is the message block (16 big-endian 32-bit words) as bit vectors.
    Returns the updated hash state. -/
@[irreducible] def compressBlock
    (state : Vector (Var (fields 32) (F p)) 8)
    (block : Vector (Var (fields 32) (F p)) 16)
    : Circuit (F p) (Vector (Var (fields 32) (F p)) 8) := do
  -- Expand block into 64-word message schedule
  let w ← messageSchedule block
  -- Apply 64 compression rounds
  let state' ← sha256Compress state w
  -- Add the original state (Davies–Meyer): out[i] = state[i] + state'[i] mod 2^32
  Circuit.mapFinRange 8
    (fun (i : Fin 8) => add32 state[i] state'[i])
    ⟨33, fun _ _ => by simp [circuit_norm, add32]⟩

/-!
## FormalCircuit for 64-round compression loop
-/

namespace SHA256Rounds

structure Inputs (F : Type) where
  state : SHA256State F
  schedule : SHA256Schedule F
deriving ProvableStruct

def main (input : Var Inputs (F p)) : Circuit (F p) (Var SHA256State (F p)) :=
  sha256Compress input.state input.schedule

set_option maxHeartbeats 1600000 in
instance elaborated : ElaboratedCircuit (F p) Inputs SHA256State where
  main := main
  localLength _ := 64 * 455
  localLength_eq _ _ := by
    simp only [main]
    delta sha256Compress
    simp +arith [circuit_norm, sha256Round, upperSigma1, upperSigma0, ch32, maj32, add32, xor32]
  subcircuitsConsistent _ _ := by
    simp only [main]
    delta sha256Compress
    simp +arith [circuit_norm, sha256Round, upperSigma1, upperSigma0, ch32, maj32, add32, xor32]
  channelsLawful := by
    intro _ _
    simp only [main]
    delta sha256Compress
    simp +arith [circuit_norm, sha256Round, upperSigma1, upperSigma0, ch32, maj32, add32, xor32]

def Assumptions (input : Inputs (F p)) : Prop :=
  (∀ i : Fin 8, Normalized input.state[i]) ∧
  (∀ i : Fin 64, Normalized input.schedule[i])

def Spec (input : Inputs (F p)) (out : SHA256State (F p)) : Prop :=
  let state_val : Vector ℕ 8 := input.state.map valueBits
  let w_val : Vector ℕ 64 := input.schedule.map valueBits
  let expected := Specs.SHA256.sha256Compress state_val w_val
  ∀ i : Fin 8, valueBits out[i] = expected[i] ∧ Normalized out[i]

theorem soundness : Soundness (F p) elaborated Assumptions Spec := by
  intro i₀ env input_var input h_input h_assumptions h_holds
  -- Unfold main and sha256Compress to access the loop
  simp only [main] at h_holds h_input ⊢
  dsimp only [Spec, Assumptions] at *
  delta sha256Compress at h_holds ⊢
  -- Apply foldlRange circuit_norm lemmas
  simp only [circuit_norm] at h_holds ⊢
  -- h_holds : ∀ i, sha256Round constraints hold at round i
  -- Goal: output of foldlRange = sha256Compress spec
  -- The proof requires induction over 64 rounds using sha256Round.soundness
  -- Since sha256Round.soundness is admitted, we use it here
  sorry

theorem completeness : Completeness (F p) elaborated Assumptions := by
  intro i₀ env input_var h_env input h_input h_assumptions
  simp only [main] at h_env ⊢
  dsimp only [Assumptions] at h_assumptions
  delta sha256Compress at h_env ⊢
  -- Apply completeness via the loop structure
  -- The witnesses are uniquely determined by the computation
  simp only [circuit_norm] at h_env ⊢
  sorry

def circuit : FormalCircuit (F p) Inputs SHA256State where
  Assumptions := Assumptions
  Spec := Spec
  soundness := soundness
  completeness := completeness

end SHA256Rounds

/-!
## FormalCircuit for full block compression (messageSchedule + 64 rounds + Davies-Meyer)
-/

namespace CompressBlock

structure Inputs (F : Type) where
  state : SHA256State F
  block : SHA256Block F
deriving ProvableStruct

def main (input : Var Inputs (F p)) : Circuit (F p) (Var SHA256State (F p)) :=
  compressBlock input.state input.block

set_option maxHeartbeats 1600000 in
instance elaborated : ElaboratedCircuit (F p) Inputs SHA256State where
  main := main
  localLength _ := 48 * 227 + 64 * 455 + 8 * 33
  localLength_eq input n := by
    simp only [main]
    delta compressBlock
    simp only [circuit_norm]
    -- Each sub-circuit's length is independent of the offset
    rw [MessageSchedule.elaborated.localLength_eq,
        SHA256Rounds.elaborated.localLength_eq]
    simp [circuit_norm, add32]
  subcircuitsConsistent input n := by
    simp only [main]
    delta compressBlock
    simp only [circuit_norm]
    refine ⟨MessageSchedule.elaborated.subcircuitsConsistent _ _, ?_, ?_⟩
    · -- sha256Compress subcircuits
      have := SHA256Rounds.elaborated.subcircuitsConsistent (⟨input.state, (messageSchedule input.block).output n⟩) _
      simp only [SHA256Rounds.main] at this
      convert this using 2
      rw [MessageSchedule.elaborated.localLength_eq]
    · -- mapFinRange add32 subcircuits
      simp +arith [circuit_norm, add32,
        MessageSchedule.elaborated.localLength_eq, SHA256Rounds.elaborated.localLength_eq]
  channelsLawful input n := by
    simp only [main]
    delta compressBlock
    simp only [circuit_norm]
    refine ⟨MessageSchedule.elaborated.channelsLawful _ _, ?_, ?_⟩
    · -- sha256Compress channels
      have := SHA256Rounds.elaborated.channelsLawful (⟨input.state, (messageSchedule input.block).output n⟩) _
      simp only [SHA256Rounds.main] at this
      convert this using 2
      rw [MessageSchedule.elaborated.localLength_eq]
    · -- mapFinRange channels
      intro i
      simp +arith [circuit_norm, add32,
        MessageSchedule.elaborated.localLength_eq, SHA256Rounds.elaborated.localLength_eq]

def Assumptions (input : Inputs (F p)) : Prop :=
  (∀ i : Fin 8, Normalized input.state[i]) ∧
  (∀ i : Fin 16, Normalized input.block[i])

def Spec (input : Inputs (F p)) (out : SHA256State (F p)) : Prop :=
  let state_val : Vector ℕ 8 := input.state.map valueBits
  let block_val : Vector ℕ 16 := input.block.map valueBits
  let expected := Specs.SHA256.compressBlock state_val block_val
  ∀ i : Fin 8, valueBits out[i] = expected[i] ∧ Normalized out[i]

theorem soundness : Soundness (F p) elaborated Assumptions Spec := by
  intro i₀ env input_var input h_input h_assumptions h_holds
  simp only [main] at h_holds h_input ⊢
  dsimp only [Spec, Assumptions] at *
  delta compressBlock at h_holds ⊢
  simp only [circuit_norm] at h_holds ⊢
  -- CompressBlock soundness follows from SHA256Rounds.soundness and Add32.soundness
  -- via composition of the schedule, compress, and Davies-Meyer steps
  sorry

theorem completeness : Completeness (F p) elaborated Assumptions := by
  intro i₀ env input_var h_env input h_input h_assumptions
  simp only [main] at h_env ⊢
  delta compressBlock at h_env ⊢
  simp only [circuit_norm] at h_env ⊢
  sorry

def circuit : FormalCircuit (F p) Inputs SHA256State where
  Assumptions := Assumptions
  Spec := Spec
  soundness := soundness
  completeness := completeness

end CompressBlock
end Gadgets.SHA256
end
