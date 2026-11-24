import Midnight.SHA256.WitnessSemantics
import Midnight.SHA256.Semantics.Decomposition
import Midnight.SHA256.Semantics.Lookup

/-! Bounded-integer facts for the actual word-preparation witnesses. These
lemmas establish the lookup and reconstruction obligations from the computed
limbs; they never assume that the desired output equation already holds.
Gate and cell extraction from the source is in `PrepareGates`. -/

namespace Midnight.SHA256.Semantics.Prepare
open Midnight.SHA256.Semantics Decomposition

/-- A supported-width integer and its actual spread witness form a real row
of the native table. No field alias is accepted in place of the integer. -/
theorem honest_spread_lookup (value width : Nat) (hw : width ∈ spreadWidths)
    (hv : value < 2 ^ width) :
    SpreadLookup (width : F) (value : F) (Witness.spread32 value : F) := by
  have hw32 : width ≤ 32 := (spreadWidth_le_twelve hw).trans (by decide)
  have hv32 : value < 2 ^ 32 := hv.trans_le (Nat.pow_le_pow_right (by decide) hw32)
  rw [Witness.spread32_eq_spread value hv32]
  exact List.mem_map.mpr ⟨(width, value, spread value),
    (mem_spreadRows_iff _ _ _).mpr ⟨hw, hv, rfl⟩, rfl⟩

def aLimbs (word : Nat) : List Limb :=
  Decomposition.aLimbs (Witness.limb word (22,10)) (Witness.limb word (13,9))
    (Witness.limb word (2,11)) (Witness.limb word (0,2))

def eLimbs (word : Nat) : List Limb :=
  Decomposition.eLimbs (Witness.limb word (25,7)) (Witness.limb word (13,12))
    (Witness.limb word (11,2)) (Witness.limb word (6,5)) (Witness.limb word (0,6))

def messageLimbs (word : Nat) : List Limb :=
  Decomposition.messageLimbs (Witness.limb word (20,12)) (Witness.limb word (19,1))
    (Witness.limb word (18,1)) (Witness.limb word (17,1)) (Witness.limb word (10,7))
    (Witness.limb word (7,3)) (Witness.limb word (3,4)) (Witness.limb word (0,3))

def parityLimbs (word : Nat) : List Limb :=
  Decomposition.parityLimbs (Witness.limb word (21,11)) (Witness.limb word (10,11))
    (Witness.limb word (0,10))

theorem a_bounded (word : Nat) : Bounded (aLimbs word) := by
  simp only [Bounded, aLimbs, Decomposition.aLimbs, List.mem_cons,
    List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨Witness.limb_lt _ _, Witness.limb_lt _ _, Witness.limb_lt _ _, Witness.limb_lt _ _⟩

theorem e_bounded (word : Nat) : Bounded (eLimbs word) := by
  simp only [Bounded, eLimbs, Decomposition.eLimbs, List.mem_cons,
    List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨Witness.limb_lt _ _, Witness.limb_lt _ _, Witness.limb_lt _ _,
    Witness.limb_lt _ _, Witness.limb_lt _ _⟩

theorem parity_bounded (word : Nat) : Bounded (parityLimbs word) := by
  simp only [Bounded, parityLimbs, Decomposition.parityLimbs, List.mem_cons,
    List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨Witness.limb_lt _ _, Witness.limb_lt _ _, Witness.limb_lt _ _⟩

theorem pack_a (word : Nat) (hw : word < 2 ^ 32) : pack (aLimbs word) = word := by
  rw [aLimbs, Decomposition.pack_a]
  simp only [Witness.limb, Nat.shiftRight_eq_div_pow]
  norm_num at *
  omega

theorem pack_e (word : Nat) (hw : word < 2 ^ 32) : pack (eLimbs word) = word := by
  rw [eLimbs, Decomposition.pack_e]
  simp only [Witness.limb, Nat.shiftRight_eq_div_pow]
  norm_num at *
  omega

theorem pack_message (word : Nat) (hw : word < 2 ^ 32) : pack (messageLimbs word) = word := by
  rw [messageLimbs, Decomposition.pack_message]
  simp only [Witness.limb, Nat.shiftRight_eq_div_pow]
  norm_num at *
  omega

theorem pack_parity (word : Nat) (hw : word < 2 ^ 32) : pack (parityLimbs word) = word := by
  rw [parityLimbs, Decomposition.pack_parity]
  simp only [Witness.limb, Nat.shiftRight_eq_div_pow]
  norm_num at *
  omega

theorem spread_a (word : Nat) (hw : word < 2 ^ 32) :
    packSpread (aLimbs word) = Witness.spread32 word := by
  rw [← spread_pack _ (a_bounded word), pack_a word hw, Witness.spread32_eq_spread word hw]

theorem spread_e (word : Nat) (hw : word < 2 ^ 32) :
    packSpread (eLimbs word) = Witness.spread32 word := by
  rw [← spread_pack _ (e_bounded word), pack_e word hw, Witness.spread32_eq_spread word hw]

/-- The actual modulo/division witnesses meet both the carry lookup and the
addition gate for every admitted list of at most seven 32-bit summands. -/
theorem honest_addMod (values : List Nat) (hcount : values.length ≤ 7)
    (hvalues : ∀ value ∈ values, value < 2 ^ 32) :
    Witness.sum32 values < 2 ^ 32 ∧
    SpreadLookup 3 (Witness.carry32 values : F)
      (Witness.spread32 (Witness.carry32 values) : F) ∧
    (values.sum : F) - (Witness.sum32 values : F) -
      (Witness.carry32 values : F) * (2 ^ 32 : F) = 0 := by
  refine ⟨Witness.sum32_lt values, ?_, add32_gate_complete values.sum⟩
  exact honest_spread_lookup _ 3 (by simp [spreadWidths])
    (Witness.carry32_lt_eight values hcount hvalues)

end Midnight.SHA256.Semantics.Prepare
