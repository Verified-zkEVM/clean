import Clean.Types.U32
import Clean.Circuit.Provable
import Clean.Specs.BLAKE3

namespace Gadgets.BLAKE3
open Specs.BLAKE3

variable {p : ℕ} [Fact p.Prime]
variable [p_large_enough: Fact (p > 512)]

-- definitions

@[reducible] def BLAKE3State := ProvableVector U32 16

def BLAKE3State.Normalized (state : BLAKE3State (F p)) :=
  ∀ i : Fin 16, state[i.val].Normalized

def BLAKE3State.value (state : BLAKE3State (F p)) := state.map U32.value

def BLAKE3State.rawValue (state : BLAKE3State (F p)) := state.map U32.rawValueU32

omit [Fact (Nat.Prime p)] p_large_enough in
lemma BLAKE3STate.rawValueNormalized (state : BLAKE3State (F p)) (h : state.Normalized) :
    state.rawValue.map UInt32.toNat = state.value := by
  simp only [BLAKE3State.value, BLAKE3State.rawValue, Vector.map_map]
  ext
  rename_i i h_i
  simp only [Vector.getElem_map]
  rw [Function.comp_apply, U32.rawValueU32]
  simp only [BLAKE3State.Normalized] at h
  rw [UInt32.toNat_ofNat_of_lt']
  apply U32.value_lt_of_normalized
  convert h i
  norm_num
  omega

instance (F : Type) [Inhabited F] : Inhabited (BLAKE3State F) where
  default := .replicate 16 default

end Gadgets.BLAKE3
