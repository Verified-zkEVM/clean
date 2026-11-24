import Midnight.SHA256.Semantics.Decomposition
import Midnight.SHA256.Semantics.Bitwise
import Midnight.SHA256.Witness
import Clean.Specs.SHA256
import Clean.Utils.Rotation

/-! The native sigma recipes rearrange bounded limbs before adding their
spread encodings. These lemmas relate those exact recipes to SHA rotations and
shifts, and infer the XOR result from a satisfied parity equation. -/

namespace Midnight.SHA256.Semantics.Rotations
open Midnight.SHA256.Semantics Decomposition

@[simp] theorem width_append (high low : List Limb) :
    width (high ++ low) = width high + width low := by
  simp [width]

theorem pack_append (high low : List Limb) :
    pack (high ++ low) = pack high * 2 ^ width low + pack low := by
  induction high with
  | nil => simp [pack]
  | cons limb rest ih =>
    simp only [List.cons_append, pack, width_append, pow_add, ih]
    ring

theorem bounded_append_left {high low : List Limb} (h : Bounded (high ++ low)) :
    Bounded high := fun limb hm => h limb (List.mem_append_left _ hm)

theorem bounded_append_right {high low : List Limb} (h : Bounded (high ++ low)) :
    Bounded low := fun limb hm => h limb (List.mem_append_right _ hm)

theorem bounded_append_swap {high low : List Limb} (h : Bounded (high ++ low)) :
    Bounded (low ++ high) := by
  intro limb hm
  exact h limb (by simpa only [List.mem_append, or_comm] using hm)

theorem shift_pack (high low : List Limb) (h : Bounded (high ++ low)) :
    pack (high ++ low) / 2 ^ width low = pack high := by
  have hl := pack_lt low (bounded_append_right h)
  have hp : 0 < 2 ^ width low := by positivity
  rw [pack_append, Nat.mul_comm (pack high), Nat.mul_add_div hp, Nat.div_eq_of_lt hl, Nat.add_zero]

theorem rotate_pack (high low : List Limb) (h : Bounded (high ++ low))
    (hwidth : width (high ++ low) = 32) (hlow : width low < 32) :
    rotRight32 (pack (high ++ low)) (width low) = pack (low ++ high) := by
  have hl := pack_lt low (bounded_append_right h)
  have hw : 32 - width low = width high := by rw [width_append] at hwidth; omega
  simp only [rotRight32, Nat.mod_eq_of_lt hlow]
  rw [shift_pack high low h, pack_append low high, hw]
  congr 1
  rw [pack_append]
  simp [Nat.add_mod, Nat.mod_eq_of_lt hl]

theorem spread_shift_pack (high low : List Limb) (h : Bounded (high ++ low)) :
    spread (pack (high ++ low) / 2 ^ width low) = packSpread high := by
  rw [shift_pack high low h, spread_pack high (bounded_append_left h)]

theorem spread_rotate_pack (high low : List Limb) (h : Bounded (high ++ low))
    (hwidth : width (high ++ low) = 32) (hlow : width low < 32) :
    spread (rotRight32 (pack (high ++ low)) (width low)) = packSpread (low ++ high) := by
  rw [rotate_pack high low h hwidth hlow, spread_pack _ (bounded_append_swap h)]

theorem rotRight32_lt {word : Nat} (bound : word < 2 ^ 32) (offset : Nat) :
    rotRight32 word offset < 2 ^ 32 :=
  Utils.Rotation.rotRight32_lt word offset bound

/-- Exact native bigSigma0 weighted recipe as three spread rotations/shifts. -/
theorem bigSigma0_recipe (a b c d : Nat) (bounded : Bounded (aLimbs a b c d)) :
    Witness.spreadedBigSigma0 #v[spread a, spread b, spread c, spread d] =
      spread (rotRight32 (pack (aLimbs a b c d)) 2) +
      spread (rotRight32 (pack (aLimbs a b c d)) 13) +
      spread (rotRight32 (pack (aLimbs a b c d)) 22) := by
  have r1 : spread (rotRight32 (pack (aLimbs a b c d)) 2) = packSpread [(2,d), (10,a), (9,b), (11,c)] :=
    spread_rotate_pack [(10,a), (9,b), (11,c)] [(2,d)] bounded (by rfl) (by norm_num [width])
  have r2 : spread (rotRight32 (pack (aLimbs a b c d)) 13) = packSpread [(11,c), (2,d), (10,a), (9,b)] :=
    spread_rotate_pack [(10,a), (9,b)] [(11,c), (2,d)] bounded (by rfl) (by norm_num [width])
  have r3 : spread (rotRight32 (pack (aLimbs a b c d)) 22) = packSpread [(9,b), (11,c), (2,d), (10,a)] :=
    spread_rotate_pack [(10,a)] [(9,b), (11,c), (2,d)] bounded (by rfl) (by norm_num [width])
  rw [r1, r2, r3]
  norm_num [Witness.spreadedBigSigma0, Witness.bigSigma0Recipe, Witness.weighted, packSpread, width]
  ring

/-- Exact native bigSigma1 weighted recipe as three spread rotations/shifts. -/
theorem bigSigma1_recipe (a b c d e : Nat) (bounded : Bounded (eLimbs a b c d e)) :
    Witness.spreadedBigSigma1 #v[spread a, spread b, spread c, spread d, spread e] =
      spread (rotRight32 (pack (eLimbs a b c d e)) 6) +
      spread (rotRight32 (pack (eLimbs a b c d e)) 11) +
      spread (rotRight32 (pack (eLimbs a b c d e)) 25) := by
  have r1 : spread (rotRight32 (pack (eLimbs a b c d e)) 6) = packSpread [(6,e), (7,a), (12,b), (2,c), (5,d)] :=
    spread_rotate_pack [(7,a), (12,b), (2,c), (5,d)] [(6,e)] bounded (by rfl) (by norm_num [width])
  have r2 : spread (rotRight32 (pack (eLimbs a b c d e)) 11) = packSpread [(5,d), (6,e), (7,a), (12,b), (2,c)] :=
    spread_rotate_pack [(7,a), (12,b), (2,c)] [(5,d), (6,e)] bounded (by rfl) (by norm_num [width])
  have r3 : spread (rotRight32 (pack (eLimbs a b c d e)) 25) = packSpread [(12,b), (2,c), (5,d), (6,e), (7,a)] :=
    spread_rotate_pack [(7,a)] [(12,b), (2,c), (5,d), (6,e)] bounded (by rfl) (by norm_num [width])
  rw [r1, r2, r3]
  norm_num [Witness.spreadedBigSigma1, Witness.bigSigma1Recipe, Witness.weighted, packSpread, width]
  ring

/-- Exact native sigma0 weighted recipe as three spread rotations/shifts. -/
theorem sigma0_recipe (a b c d e f g h : Nat) (bounded : Bounded (messageLimbs a b c d e f g h)) :
    Witness.spreadedSigma0 #v[spread a, spread b, spread c, spread d, spread e, spread f, spread g, spread h] =
      spread (pack (messageLimbs a b c d e f g h) / 2 ^ 3) +
      spread (rotRight32 (pack (messageLimbs a b c d e f g h)) 7) +
      spread (rotRight32 (pack (messageLimbs a b c d e f g h)) 18) := by
  have r1 : spread (pack (messageLimbs a b c d e f g h) / 2 ^ 3) = packSpread [(12,a), (1,b), (1,c), (1,d), (7,e), (3,f), (4,g)] :=
    spread_shift_pack [(12,a), (1,b), (1,c), (1,d), (7,e), (3,f), (4,g)] [(3,h)] bounded
  have r2 : spread (rotRight32 (pack (messageLimbs a b c d e f g h)) 7) = packSpread [(4,g), (3,h), (12,a), (1,b), (1,c), (1,d), (7,e), (3,f)] :=
    spread_rotate_pack [(12,a), (1,b), (1,c), (1,d), (7,e), (3,f)] [(4,g), (3,h)] bounded (by rfl) (by norm_num [width])
  have r3 : spread (rotRight32 (pack (messageLimbs a b c d e f g h)) 18) = packSpread [(1,d), (7,e), (3,f), (4,g), (3,h), (12,a), (1,b), (1,c)] :=
    spread_rotate_pack [(12,a), (1,b), (1,c)] [(1,d), (7,e), (3,f), (4,g), (3,h)] bounded (by rfl) (by norm_num [width])
  rw [r1, r2, r3]
  dsimp only [Witness.spreadedSigma0, Witness.sigma0Recipe, Witness.weighted, packSpread, width]
  generalize spread a = sa, spread b = sb, spread c = sc, spread d = sd,
    spread e = se, spread f = sf, spread g = sg, spread h = sh
  simp only [List.foldr_cons, List.foldr_nil,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  simp only [
    show #v[sa, sb, sc, sd, se, sf, sg, sh][(0 : Fin 8)] = sa from rfl,
    show #v[sa, sb, sc, sd, se, sf, sg, sh][(1 : Fin 8)] = sb from rfl,
    show #v[sa, sb, sc, sd, se, sf, sg, sh][(2 : Fin 8)] = sc from rfl,
    show #v[sa, sb, sc, sd, se, sf, sg, sh][(3 : Fin 8)] = sd from rfl,
    show #v[sa, sb, sc, sd, se, sf, sg, sh][(4 : Fin 8)] = se from rfl,
    show #v[sa, sb, sc, sd, se, sf, sg, sh][(5 : Fin 8)] = sf from rfl,
    show #v[sa, sb, sc, sd, se, sf, sg, sh][(6 : Fin 8)] = sg from rfl,
    show #v[sa, sb, sc, sd, se, sf, sg, sh][(7 : Fin 8)] = sh from rfl]
  ring

/-- Exact native sigma1 weighted recipe as three spread rotations/shifts. -/
theorem sigma1_recipe (a b c d e f g h : Nat) (bounded : Bounded (messageLimbs a b c d e f g h)) :
    Witness.spreadedSigma1 #v[spread a, spread b, spread c, spread d, spread e, spread f, spread g, spread h] =
      spread (pack (messageLimbs a b c d e f g h) / 2 ^ 10) +
      spread (rotRight32 (pack (messageLimbs a b c d e f g h)) 17) +
      spread (rotRight32 (pack (messageLimbs a b c d e f g h)) 19) := by
  have r1 : spread (pack (messageLimbs a b c d e f g h) / 2 ^ 10) = packSpread [(12,a), (1,b), (1,c), (1,d), (7,e)] :=
    spread_shift_pack [(12,a), (1,b), (1,c), (1,d), (7,e)] [(3,f), (4,g), (3,h)] bounded
  have r2 : spread (rotRight32 (pack (messageLimbs a b c d e f g h)) 17) = packSpread [(7,e), (3,f), (4,g), (3,h), (12,a), (1,b), (1,c), (1,d)] :=
    spread_rotate_pack [(12,a), (1,b), (1,c), (1,d)] [(7,e), (3,f), (4,g), (3,h)] bounded (by rfl) (by norm_num [width])
  have r3 : spread (rotRight32 (pack (messageLimbs a b c d e f g h)) 19) = packSpread [(1,c), (1,d), (7,e), (3,f), (4,g), (3,h), (12,a), (1,b)] :=
    spread_rotate_pack [(12,a), (1,b)] [(1,c), (1,d), (7,e), (3,f), (4,g), (3,h)] bounded (by rfl) (by norm_num [width])
  rw [r1, r2, r3]
  dsimp only [Witness.spreadedSigma1, Witness.sigma1Recipe, Witness.weighted, packSpread, width]
  generalize spread a = sa, spread b = sb, spread c = sc, spread d = sd,
    spread e = se, spread f = sf, spread g = sg, spread h = sh
  simp only [List.foldr_cons, List.foldr_nil,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  simp only [
    show #v[sa, sb, sc, sd, se, sf, sg, sh][(0 : Fin 8)] = sa from rfl,
    show #v[sa, sb, sc, sd, se, sf, sg, sh][(1 : Fin 8)] = sb from rfl,
    show #v[sa, sb, sc, sd, se, sf, sg, sh][(2 : Fin 8)] = sc from rfl,
    show #v[sa, sb, sc, sd, se, sf, sg, sh][(3 : Fin 8)] = sd from rfl,
    show #v[sa, sb, sc, sd, se, sf, sg, sh][(4 : Fin 8)] = se from rfl,
    show #v[sa, sb, sc, sd, se, sf, sg, sh][(5 : Fin 8)] = sf from rfl,
    show #v[sa, sb, sc, sd, se, sf, sg, sh][(6 : Fin 8)] = sg from rfl,
    show #v[sa, sb, sc, sd, se, sf, sg, sh][(7 : Fin 8)] = sh from rfl]
  ring

/-- Soundness of the native bigSigma0 parity equation, after lookup/decomposition
lemmas supply the bounded plain limbs and their spread values. -/
theorem bigSigma0_field_sound (a b c d : Nat)
    (bounded : Bounded (aLimbs a b c d)) {even odd : Nat}
    (he : even < 2 ^ 32) (ho : odd < 2 ^ 32)
    (equation : (Witness.spreadedBigSigma0 #v[spread a, spread b, spread c, spread d] : F) =
      (spread even : F) + 2 * (spread odd : F)) :
    even = Specs.SHA256.upperSigma0 (pack (aLimbs a b c d)) := by
  have hw : pack (aLimbs a b c d) < 2 ^ 32 := by
    simpa [width, aLimbs] using pack_lt (aLimbs a b c d) bounded
  rw [bigSigma0_recipe a b c d bounded] at equation
  push_cast at equation
  have h := spread_triple_field_sound
    (rotRight32_lt hw 2)
    (rotRight32_lt hw 13)
    (rotRight32_lt hw 22)
    he ho sha256_parity_capacity equation
  simpa [Specs.SHA256.upperSigma0, Nat.xor_assoc, Nat.xor_comm, Nat.xor_left_comm] using h.1

/-- Soundness of the native bigSigma1 parity equation, after lookup/decomposition
lemmas supply the bounded plain limbs and their spread values. -/
theorem bigSigma1_field_sound (a b c d e : Nat)
    (bounded : Bounded (eLimbs a b c d e)) {even odd : Nat}
    (he : even < 2 ^ 32) (ho : odd < 2 ^ 32)
    (equation : (Witness.spreadedBigSigma1 #v[spread a, spread b, spread c, spread d, spread e] : F) =
      (spread even : F) + 2 * (spread odd : F)) :
    even = Specs.SHA256.upperSigma1 (pack (eLimbs a b c d e)) := by
  have hw : pack (eLimbs a b c d e) < 2 ^ 32 := by
    simpa [width, eLimbs] using pack_lt (eLimbs a b c d e) bounded
  rw [bigSigma1_recipe a b c d e bounded] at equation
  push_cast at equation
  have h := spread_triple_field_sound
    (rotRight32_lt hw 6)
    (rotRight32_lt hw 11)
    (rotRight32_lt hw 25)
    he ho sha256_parity_capacity equation
  simpa [Specs.SHA256.upperSigma1, Nat.xor_assoc, Nat.xor_comm, Nat.xor_left_comm] using h.1

/-- Soundness of the native sigma0 parity equation, after lookup/decomposition
lemmas supply the bounded plain limbs and their spread values. -/
theorem sigma0_field_sound (a b c d e f g h : Nat)
    (bounded : Bounded (messageLimbs a b c d e f g h)) {even odd : Nat}
    (he : even < 2 ^ 32) (ho : odd < 2 ^ 32)
    (equation : (Witness.spreadedSigma0 #v[spread a, spread b, spread c, spread d, spread e, spread f, spread g, spread h] : F) =
      (spread even : F) + 2 * (spread odd : F)) :
    even = Specs.SHA256.lowerSigma0 (pack (messageLimbs a b c d e f g h)) := by
  have hw : pack (messageLimbs a b c d e f g h) < 2 ^ 32 := by
    simpa [width, messageLimbs] using pack_lt (messageLimbs a b c d e f g h) bounded
  rw [sigma0_recipe a b c d e f g h bounded] at equation
  push_cast at equation
  have h := spread_triple_field_sound
    (lt_of_le_of_lt (Nat.div_le_self _ _) hw)
    (rotRight32_lt hw 7)
    (rotRight32_lt hw 18)
    he ho sha256_parity_capacity equation
  simpa [Specs.SHA256.lowerSigma0, Nat.xor_assoc, Nat.xor_comm, Nat.xor_left_comm] using h.1

/-- Soundness of the native sigma1 parity equation, after lookup/decomposition
lemmas supply the bounded plain limbs and their spread values. -/
theorem sigma1_field_sound (a b c d e f g h : Nat)
    (bounded : Bounded (messageLimbs a b c d e f g h)) {even odd : Nat}
    (he : even < 2 ^ 32) (ho : odd < 2 ^ 32)
    (equation : (Witness.spreadedSigma1 #v[spread a, spread b, spread c, spread d, spread e, spread f, spread g, spread h] : F) =
      (spread even : F) + 2 * (spread odd : F)) :
    even = Specs.SHA256.lowerSigma1 (pack (messageLimbs a b c d e f g h)) := by
  have hw : pack (messageLimbs a b c d e f g h) < 2 ^ 32 := by
    simpa [width, messageLimbs] using pack_lt (messageLimbs a b c d e f g h) bounded
  rw [sigma1_recipe a b c d e f g h bounded] at equation
  push_cast at equation
  have h := spread_triple_field_sound
    (lt_of_le_of_lt (Nat.div_le_self _ _) hw)
    (rotRight32_lt hw 17)
    (rotRight32_lt hw 19)
    he ho sha256_parity_capacity equation
  simpa [Specs.SHA256.lowerSigma1, Nat.xor_assoc, Nat.xor_comm, Nat.xor_left_comm] using h.1

/-- One-bit message limbs are used directly in the source sigma gate, because
spreading an actual bit does not change it. -/
theorem spread_one_bit {value : Nat} (bound : value < 2) : spread value = value := by
  have h : value = 0 ∨ value = 1 := by omega
  rcases h with rfl | rfl <;> norm_num [spread]

end Midnight.SHA256.Semantics.Rotations
