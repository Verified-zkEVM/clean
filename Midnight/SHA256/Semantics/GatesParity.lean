import Midnight.SHA256.Semantics.GatesSource
import Midnight.SHA256.Semantics.GatesLookup
import Midnight.SHA256.Semantics.Decomposition

/-! Lookup-derived meaning of the actual three-row 11/11/10 bit planes. -/
namespace Midnight.SHA256.Semantics.Gates
open Halo2
open Midnight.SHA256.Semantics Decomposition

theorem lookup_values {width : Nat} (small : width < BLS12_381.scalarFieldSize)
    {plain expanded : F} (member : SpreadLookup (width : F) plain expanded) :
    plain.val < 2 ^ width ∧ expanded = (spread plain.val : F) := by
  have h := (spreadLookup_iff _ _ _).mp member
  rw [ZMod.val_natCast_of_lt small] at h
  refine ⟨h.2.1, ?_⟩
  have hs := congrArg (fun n : Nat => (n : F)) h.2.2
  simpa only [ZMod.natCast_zmod_val] using hs

/-- Lookup facts at the three native limb positions, with the fixed width tags. -/
def ParityLookups (env : Environment F) (absolute : Int) (plain expanded : Fin 8) : Prop :=
  SpreadLookup 11 (read env absolute plain (-1)) (read env absolute expanded (-1)) ∧
  SpreadLookup 11 (read env absolute plain 0) (read env absolute expanded 0) ∧
  SpreadLookup 10 (read env absolute plain 1) (read env absolute expanded 1)

def parityWord (env : Environment F) (absolute : Int) (plain : Fin 8) : Nat :=
  pack (parityLimbs (read env absolute plain (-1)).val
    (read env absolute plain 0).val (read env absolute plain 1).val)

/-- All payload and zero-interleaving claims come from the actual table relation. -/
theorem parityLookups_sound {env : Environment F} {absolute : Int} {plain expanded : Fin 8}
    (lookups : ParityLookups env absolute plain expanded) :
    parityWord env absolute plain < 2 ^ 32 ∧
      parityPlane env absolute expanded = (spread (parityWord env absolute plain) : F) := by
  have h₀ := lookup_values (width := 11) (by norm_num [BLS12_381.scalarFieldSize]) lookups.1
  have h₁ := lookup_values (width := 11) (by norm_num [BLS12_381.scalarFieldSize]) lookups.2.1
  have h₂ := lookup_values (width := 10) (by norm_num [BLS12_381.scalarFieldSize]) lookups.2.2
  let limbs := parityLimbs (read env absolute plain (-1)).val
    (read env absolute plain 0).val (read env absolute plain 1).val
  have bounded : Bounded limbs := by
    intro limb member
    simp only [limbs, parityLimbs, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact h₀.1
    · exact h₁.1
    · exact h₂.1
  constructor
  · simpa [parityWord, limbs, width, parityLimbs] using pack_lt limbs bounded
  · unfold parityPlane
    rw [h₀.2, h₁.2, h₂.2]
    change _ = (spread (pack limbs) : F)
    rw [spread_pack limbs bounded]
    norm_num [packSpread, limbs, parityLimbs, width]
    ring

/-- Casting the reconstructed plain word returns the same actual plain cells. -/
theorem parityWord_cast (env : Environment F) (absolute : Int) (plain : Fin 8) :
    (parityWord env absolute plain : F) =
      (2 ^ 21 : F) * read env absolute plain (-1) +
        (2 ^ 10 : F) * read env absolute plain 0 + read env absolute plain 1 := by
  simp only [parityWord, pack_parity, Nat.cast_add, Nat.cast_mul, Nat.cast_pow,
    Nat.cast_ofNat, ZMod.natCast_zmod_val]

end Midnight.SHA256.Semantics.Gates
