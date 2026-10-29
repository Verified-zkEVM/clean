module

public import CleanCompStark.Soundness
public import CleanCompStark.KeccakAir.Bridgeable
public import CleanCompStark.Fields
public import Clean.Examples.KeccakAir.Ensemble
public import CompStark.KoalaBear.Challenge

/-!
# Plonky3's Keccak-f AIR as a CompStark STARK

Clean's Keccak-f component (Plonky3's `keccak-air`) over KoalaBear, with what the backend's
knowledge soundness theorems (`knowledgeSoundness_of_secure`, `knowledgeSoundness_ro_of_secureRo`)
ask of it: it is bridgeable (`bridgeable_component`), it fits every trace domain of KoalaBear
(`fits`), and its circuit proves of its tables that every 24-row block starting at round 0
computes Keccak-f (`tableSound`, `BlocksCorrect`).
-/
@[expose] public section

namespace CleanCompStark.KeccakAir
open Air.Flat _root_.KeccakAir CompStark CompStark.Iop Specs.Keccak256

/-- Clean's KoalaBear field. -/
abbrev F : Type := _root_.F KoalaBear.fieldSize

/-- The Keccak-f component on `2 ^ logN` rows. -/
abbrev component (logN : ℕ) : Component F := _root_.KeccakAir.component (UInt64.ofNat (2 ^ logN))

/-- Every 24-row block of the rows that starts at round 0 computes Keccak-f of the preimage of its
first row. -/
def BlocksCorrect (rows : List (Array F)) : Prop :=
  ∀ i (hi : i + 23 < rows.length), (traceRow rows[i]).stepFlags[0] = 1 →
    let first := traceRow rows[i]
    let last := traceRow rows[i + 23]
    last.stepFlags[23] = 1 ∧ last.preimage = first.preimage ∧ first.PreimageNormalized ∧
      last.outputState = keccakPermutation first.preimageState

theorem tableSound (height : UInt64) :
    TableSound (_root_.KeccakAir.component (p := KoalaBear.fieldSize) height) BlocksCorrect :=
  fun _ hcomponent consistent satisfied => table_block_soundness hcomponent consistent satisfied

/-- The Keccak-f component fits every trace domain of KoalaBear. -/
theorem fits {logN : ℕ} (h : logN ≤ 24) :
    Fits (K := KoalaBear.Fast.Field) (component logN) logN where
  twoAdic := by rw [KoalaBear.twoAdicity_eq]; exact h
  height_le := by omega
  fixedHeight := by
    rintro _ ⟨⟩
    exact UInt64.toNat_ofNat_of_lt' (Nat.lt_of_le_of_lt (Nat.pow_le_pow_right (by norm_num) h)
      (by decide))

end CleanCompStark.KeccakAir
