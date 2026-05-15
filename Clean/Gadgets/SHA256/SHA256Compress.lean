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
    ⟨421, fun _ _ => by sorry⟩

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
    ⟨33, fun _ _ => by sorry⟩

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

instance elaborated : ElaboratedCircuit (F p) Inputs SHA256State where
  main := main
  localLength _ := 64 * 421
  localLength_eq _ _ := by sorry
  subcircuitsConsistent _ _ := by sorry
  channelsLawful := by sorry

def Assumptions (input : Inputs (F p)) : Prop :=
  (∀ i : Fin 8, Normalized input.state[i]) ∧
  (∀ i : Fin 64, Normalized input.schedule[i])

def Spec (input : Inputs (F p)) (out : SHA256State (F p)) : Prop :=
  let state_val : Vector ℕ 8 := input.state.map valueBits
  let w_val : Vector ℕ 64 := input.schedule.map valueBits
  let expected := Specs.SHA256.sha256Compress state_val w_val
  ∀ i : Fin 8, valueBits out[i] = expected[i] ∧ Normalized out[i]

theorem soundness : Soundness (F p) elaborated Assumptions Spec := by sorry
theorem completeness : Completeness (F p) elaborated Assumptions := by sorry

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

instance elaborated : ElaboratedCircuit (F p) Inputs SHA256State where
  main := main
  localLength _ := 48 * 227 + 64 * 421 + 8 * 33
  localLength_eq _ _ := by sorry
  subcircuitsConsistent _ _ := by sorry
  channelsLawful := by sorry

def Assumptions (input : Inputs (F p)) : Prop :=
  (∀ i : Fin 8, Normalized input.state[i]) ∧
  (∀ i : Fin 16, Normalized input.block[i])

def Spec (input : Inputs (F p)) (out : SHA256State (F p)) : Prop :=
  let state_val : Vector ℕ 8 := input.state.map valueBits
  let block_val : Vector ℕ 16 := input.block.map valueBits
  let expected := Specs.SHA256.compressBlock state_val block_val
  ∀ i : Fin 8, valueBits out[i] = expected[i] ∧ Normalized out[i]

theorem soundness : Soundness (F p) elaborated Assumptions Spec := by sorry
theorem completeness : Completeness (F p) elaborated Assumptions := by sorry

def circuit : FormalCircuit (F p) Inputs SHA256State where
  Assumptions := Assumptions
  Spec := Spec
  soundness := soundness
  completeness := completeness

end CompressBlock
end Gadgets.SHA256
end
