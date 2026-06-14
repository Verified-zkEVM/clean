import Batteries.Data.Vector.Lemmas
import Clean.Orchard.Sinsemilla.HashToPoint
import Clean.Orchard.Utilities

/-!
Reference:
`halo2@halo2_gadgets-0.5.0/halo2_gadgets/src/sinsemilla/merkle/chip.rs`
- `MerkleInstructions::hash_layer`

`MerkleCRH^Orchard(l, left, right) = SinsemillaHash(Q, l⋆ || left⋆ || right⋆)`: the
520-bit message is witnessed as three Sinsemilla pieces

- `a = a_0 || a_1` = `l` (10 bits) `||` bits 0..240 of `left` (25 words),
- `b = b_0 || b_1 || b_2` = bits 240..250 of `left` `||` bits 250..255 of `left` `||`
  bits 0..5 of `right` (2 words),
- `c` = bits 5..255 of `right` (25 words),

with the short sub-pieces `b_1`, `b_2` witnessed separately and range-checked to
5 bits. The `q_decompose` gate (`Merkle.circuit`, the `Decomposition check`) ties the
pieces to `(l, left, right)` through the hash's own `z_1` running-sum cells, which
`hash_to_point` exposes.
-/

namespace Orchard.Sinsemilla.Merkle

open CompElliptic.Curves.Pasta CompElliptic.CurveForms.ShortWeierstrass
open CompElliptic.Fields.Pasta (PALLAS_BASE_CARD)
open Orchard.Specs.Sinsemilla (K Generators merkleChunks)


/-! ### Digit toolkit

`K`-bit little-endian digit sums: extraction of single digits, recombination, bounds.
-/

/-- Factor the lowest digit out of a digit sum. -/
private theorem sum_head_shift (Kb m : ℕ) (d : ℕ → ℕ) :
    ∑ j ∈ Finset.range (m + 1), d j * 2 ^ (Kb * j)
      = d 0 + 2 ^ Kb * ∑ j ∈ Finset.range m, d (j + 1) * 2 ^ (Kb * j) := by
  rw [Finset.sum_range_succ', Finset.mul_sum]
  have hstep : ∀ j : ℕ,
      d (j + 1) * 2 ^ (Kb * (j + 1)) = 2 ^ Kb * (d (j + 1) * 2 ^ (Kb * j)) := by
    intro j
    rw [show Kb * (j + 1) = Kb + Kb * j from by ring, pow_add]
    ring
  simp only [hstep, Nat.mul_zero, pow_zero, Nat.mul_one]
  ring

/-- A digit sum of `n` digits fits in `Kb · n` bits. -/
private theorem sum_digits_lt {Kb : ℕ} {d : ℕ → ℕ} (hd : ∀ j, d j < 2 ^ Kb) (n : ℕ) :
    ∑ j ∈ Finset.range n, d j * 2 ^ (Kb * j) < 2 ^ (Kb * n) := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ]
    have hterm : d m * 2 ^ (Kb * m) + 2 ^ (Kb * m) ≤ 2 ^ (Kb * (m + 1)) := by
      rw [show Kb * (m + 1) = Kb * m + Kb from by ring, pow_add]
      calc d m * 2 ^ (Kb * m) + 2 ^ (Kb * m) = (d m + 1) * 2 ^ (Kb * m) := by ring
        _ ≤ 2 ^ Kb * 2 ^ (Kb * m) := Nat.mul_le_mul_right _ (hd m)
        _ = 2 ^ (Kb * m) * 2 ^ Kb := by ring
    omega

/-- Concatenating a `Kb·m`-bit value with high bits stays within bounds. -/
private theorem append_lt {m n x y : ℕ} (hx : x < 2 ^ m) (hy : y < 2 ^ n) :
    x + 2 ^ m * y < 2 ^ (m + n) := by
  have h1 : x + 2 ^ m * y < 2 ^ m * (1 + y) := by
    rw [Nat.mul_add, Nat.mul_one]
    omega
  have h2 : 2 ^ m * (1 + y) ≤ 2 ^ m * 2 ^ n := Nat.mul_le_mul_left _ (by omega)
  rw [pow_add]
  omega

/-- Each digit of a bounded-digit sum is recovered by shift-and-mask. -/
private theorem digit_of_sum (Kb : ℕ) :
    ∀ (i n : ℕ) (d : ℕ → ℕ), (∀ j, d j < 2 ^ Kb) → i < n →
      (∑ j ∈ Finset.range n, d j * 2 ^ (Kb * j)) / 2 ^ (Kb * i) % 2 ^ Kb = d i := by
  intro i
  induction i with
  | zero =>
    intro n d hd hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [sum_head_shift, Nat.mul_zero, pow_zero, Nat.div_one,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hd 0)]
  | succ i ih =>
    intro n d hd hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [sum_head_shift,
      show Kb * (i + 1) = Kb + Kb * i from by ring, pow_add,
      ← Nat.div_div_eq_div_mul,
      Nat.add_mul_div_left _ _ (Nat.two_pow_pos Kb),
      Nat.div_eq_of_lt (hd 0), Nat.zero_add]
    exact ih m (fun j => d (j + 1)) (fun j => hd (j + 1)) (by omega)

/-- A `Kb·n`-bit value is the sum of its shift-and-mask digits. -/
private theorem sum_words (Kb : ℕ) :
    ∀ (n x : ℕ), x < 2 ^ (Kb * n) →
      ∑ j ∈ Finset.range n, (x / 2 ^ (Kb * j) % 2 ^ Kb) * 2 ^ (Kb * j) = x := by
  intro n
  induction n with
  | zero =>
    intro x hx
    simp only [Nat.mul_zero, pow_zero, Nat.lt_one_iff] at hx
    simp [hx]
  | succ m ih =>
    intro x hx
    rw [sum_head_shift]
    have hdig : ∀ j : ℕ, x / 2 ^ (Kb * (j + 1)) % 2 ^ Kb
        = (x / 2 ^ Kb) / 2 ^ (Kb * j) % 2 ^ Kb := by
      intro j
      rw [show Kb * (j + 1) = Kb + Kb * j from by ring, pow_add,
        Nat.div_div_eq_div_mul]
    simp only [hdig]
    rw [ih (x / 2 ^ Kb) (by
      rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos Kb),
        ← pow_add]
      rw [show Kb * m + Kb = Kb * (m + 1) from by ring]
      exact hx)]
    rw [Nat.mul_zero, pow_zero, Nat.div_one, Nat.mod_add_div]

set_option exponentiation.threshold 600 in
/-- Split a 52-digit sum into the `a`/`b`/`c` segments of the `MerkleCRH` message. -/
private theorem merkle_sum_split (D : ℕ → ℕ) :
    ∑ j ∈ Finset.range 52, D j * 2 ^ (K * j)
      = ∑ j ∈ Finset.range 25, D j * 2 ^ (K * j)
        + 2 ^ 250 * (∑ j ∈ Finset.range 2, D (25 + j) * 2 ^ (K * j))
        + 2 ^ 270 * (∑ j ∈ Finset.range 25, D (27 + j) * 2 ^ (K * j)) := by
  have h1 : ∑ j ∈ Finset.range 52, D j * 2 ^ (K * j)
      = ∑ j ∈ Finset.range 27, D j * 2 ^ (K * j)
        + ∑ j ∈ Finset.range 25, D (27 + j) * 2 ^ (K * (27 + j)) := by
    rw [← Finset.sum_range_add]
  have h2 : ∑ j ∈ Finset.range 27, D j * 2 ^ (K * j)
      = ∑ j ∈ Finset.range 25, D j * 2 ^ (K * j)
        + ∑ j ∈ Finset.range 2, D (25 + j) * 2 ^ (K * (25 + j)) := by
    rw [← Finset.sum_range_add]
  have h3 : ∀ j, D (25 + j) * 2 ^ (K * (25 + j))
      = 2 ^ 250 * (D (25 + j) * 2 ^ (K * j)) := by
    intro j
    rw [show K * (25 + j) = 250 + K * j from by
        simp only [show (K : ℕ) = 10 from rfl]; ring, pow_add]
    ring
  have h4 : ∀ j, D (27 + j) * 2 ^ (K * (27 + j))
      = 2 ^ 270 * (D (27 + j) * 2 ^ (K * j)) := by
    intro j
    rw [show K * (27 + j) = 270 + K * j from by
        simp only [show (K : ℕ) = 10 from rfl]; ring, pow_add]
    ring
  rw [h1, h2]
  simp only [h3, h4, ← Finset.mul_sum]

set_option exponentiation.threshold 600 in
/--
The `MerkleCRH` chunk list is the concatenation of the three pieces' chunk lists,
given that the packed message value decomposes into the pieces' digits.
-/
private theorem merkleChunks_eq {dA dB dC : ℕ → ℕ}
    (hA : ∀ j, dA j < 2 ^ K) (hB : ∀ j, dB j < 2 ^ K) (hC : ∀ j, dC j < 2 ^ K)
    {l lv rv : ℕ}
    (hm : l + 2 ^ 10 * lv + 2 ^ 265 * rv
      = ∑ j ∈ Finset.range 25, dA j * 2 ^ (K * j)
        + 2 ^ 250 * (∑ j ∈ Finset.range 2, dB j * 2 ^ (K * j))
        + 2 ^ 270 * (∑ j ∈ Finset.range 25, dC j * 2 ^ (K * j))) :
    merkleChunks l lv rv
      = (List.range 25).map dA ++ ((List.range 2).map dB ++ (List.range 25).map dC) := by
  -- the concatenated digit function
  set D : ℕ → ℕ := fun i => if i < 25 then dA i else if i < 27 then dB (i - 25)
    else dC (i - 27) with hD
  have hDlt : ∀ j, D j < 2 ^ K := by
    intro j
    rw [hD]
    dsimp only
    split
    · exact hA j
    split
    · exact hB (j - 25)
    · exact hC (j - 27)
  have hsum : l + 2 ^ 10 * lv + 2 ^ 265 * rv
      = ∑ j ∈ Finset.range 52, D j * 2 ^ (K * j) := by
    rw [merkle_sum_split, hm]
    have e1 : ∑ j ∈ Finset.range 25, D j * 2 ^ (K * j)
        = ∑ j ∈ Finset.range 25, dA j * 2 ^ (K * j) :=
      Finset.sum_congr rfl fun j hj => by
        have hj' : j < 25 := Finset.mem_range.mp hj
        simp only [hD]
        rw [if_pos hj']
    have e2 : ∑ j ∈ Finset.range 2, D (25 + j) * 2 ^ (K * j)
        = ∑ j ∈ Finset.range 2, dB j * 2 ^ (K * j) :=
      Finset.sum_congr rfl fun j hj => by
        have hj' : j < 2 := Finset.mem_range.mp hj
        simp only [hD]
        rw [if_neg (by omega), if_pos (by omega), Nat.add_sub_cancel_left]
    have e3 : ∑ j ∈ Finset.range 25, D (27 + j) * 2 ^ (K * j)
        = ∑ j ∈ Finset.range 25, dC j * 2 ^ (K * j) :=
      Finset.sum_congr rfl fun j hj => by
        simp only [hD]
        rw [if_neg (by omega), if_neg (by omega), Nat.add_sub_cancel_left]
    rw [e1, e2, e3]
  apply List.ext_getElem
  · simp [merkleChunks]
  intro i hi hi'
  have hi52 : i < 52 := by
    simp only [merkleChunks, List.length_map, List.length_range] at hi
    exact hi
  rw [show (merkleChunks l lv rv)[i]
      = (l + 2 ^ 10 * lv + 2 ^ 265 * rv) / 2 ^ (K * i) % 2 ^ K from by
    simp [merkleChunks]]
  rw [hsum, digit_of_sum K i 52 D hDlt hi52]
  rcases Nat.lt_or_ge i 25 with h25 | h25
  · rw [List.getElem_append_left (by simpa using h25)]
    simp only [hD]
    rw [if_pos h25]
    simp
  rw [List.getElem_append_right (by simpa using h25)]
  rcases Nat.lt_or_ge i 27 with h27 | h27
  · rw [List.getElem_append_left (by simp; omega)]
    simp only [hD]
    rw [if_neg (by omega), if_pos h27]
    simp
  · rw [List.getElem_append_right (by simp; omega)]
    simp only [hD]
    rw [if_neg (by omega), if_neg (by omega)]
    simp only [List.getElem_map, List.getElem_range]
    congr 1

/-! ### Field-level helpers -/

private theorem natCast_inj_lt {a b : ℕ} (ha : a < 2 ^ 10) (hb : b < 2 ^ 10)
    (h : (a : Ecc.Fp) = (b : Ecc.Fp)) : a = b := by
  have hp : (2 ^ 10 : ℕ) < PALLAS_BASE_CARD := by norm_num [PALLAS_BASE_CARD]
  have hv := congrArg ZMod.val h
  rwa [ZMod.val_natCast_of_lt (by omega), ZMod.val_natCast_of_lt (by omega)] at hv


/-! ### Assembling the soundness-side encodings

From the decomposition-gate equations, the pieces' chunk sums, and the range-checked
sub-pieces, the 255-bit encodings of `left` and `right` are recovered, and the
`MerkleCRH` message chunks are exactly the pieces' chunks.
-/

set_option exponentiation.threshold 600 in
private theorem assemble {msA msB msC : ℕ → ℕ}
    (hmsA : ∀ j, msA j < 2 ^ K) (hmsB : ∀ j, msB j < 2 ^ K) (hmsC : ∀ j, msC j < 2 ^ K)
    {l b1n b2n : ℕ} (hl : l < 2 ^ 10) (hb1n : b1n < 2 ^ 5) (hb2n : b2n < 2 ^ 5)
    {aCell bCell cCell b1Cell b2Cell z1A z1B left right : Ecc.Fp}
    (haval : aCell = ((∑ r ∈ Finset.range 25, msA r * 2 ^ (K * r) : ℕ) : Ecc.Fp))
    (hbval : bCell = ((∑ r ∈ Finset.range 2, msB r * 2 ^ (K * r) : ℕ) : Ecc.Fp))
    (hcval : cCell = ((∑ r ∈ Finset.range 25, msC r * 2 ^ (K * r) : ℕ) : Ecc.Fp))
    (hb1 : b1Cell = ((b1n : ℕ) : Ecc.Fp)) (hb2 : b2Cell = ((b2n : ℕ) : Ecc.Fp))
    (hz1A : z1A = ((∑ j ∈ Finset.range 24, msA (j + 1) * 2 ^ (K * j) : ℕ) : Ecc.Fp))
    (hz1B : z1B = ((msB 1 : ℕ) : Ecc.Fp))
    (hg1 : (l : Ecc.Fp) = aCell - z1A * twoPow10)
    (hg2 : left = z1A + (bCell - z1B * twoPow10 + b1Cell * twoPow10) * twoPow240)
    (hg3 : right = b2Cell + cCell * twoPow5)
    (hg4 : z1B = b1Cell + b2Cell * twoPow5) :
    ∃ lv rv : ℕ, lv < 2 ^ 255 ∧ rv < 2 ^ 255 ∧
      ((lv : ℕ) : Ecc.Fp) = left ∧ ((rv : ℕ) : Ecc.Fp) = right ∧
      merkleChunks l lv rv
        = (List.range 25).map msA
          ++ ((List.range 2).map msB ++ (List.range 25).map msC) := by
  subst haval hbval hcval hb1 hb2 hz1A hz1B
  have hK : Orchard.Specs.Sinsemilla.K = 10 := rfl
  have e5 : (twoPow5 : Ecc.Fp) = ((2 ^ 5 : ℕ) : Ecc.Fp) := by norm_num [twoPow5]
  have e10 : (twoPow10 : Ecc.Fp) = ((2 ^ 10 : ℕ) : Ecc.Fp) := by norm_num [twoPow10]
  have e240 : (twoPow240 : Ecc.Fp) = ((2 ^ 240 : ℕ) : Ecc.Fp) := by
    norm_num [twoPow240]
  rw [e10] at hg1
  rw [e10, e240] at hg2
  rw [e5] at hg3
  rw [e5] at hg4
  set lvA := ∑ j ∈ Finset.range 24, msA (j + 1) * 2 ^ (K * j) with hlvA
  set cnv := ∑ r ∈ Finset.range 25, msC r * 2 ^ (K * r) with hcnv
  have hlvA_lt : lvA < 2 ^ 240 := by
    have h := sum_digits_lt (d := fun j => msA (j + 1)) (fun j => hmsA (j + 1)) 24
    rw [hK] at h
    norm_num at h
    exact h
  have hcnv_lt : cnv < 2 ^ 250 := by
    have h := sum_digits_lt (d := msC) hmsC 25
    rw [hK] at h
    norm_num at h
    exact h
  have hSA : (∑ r ∈ Finset.range 25, msA r * 2 ^ (K * r)) = msA 0 + 2 ^ 10 * lvA := by
    have h := sum_head_shift K 24 msA
    rw [hK] at h ⊢
    norm_num at h ⊢
    exact h
  have hSB : (∑ r ∈ Finset.range 2, msB r * 2 ^ (K * r)) = msB 0 + 2 ^ 10 * msB 1 := by
    have h := sum_head_shift K 1 msB
    rw [hK] at h ⊢
    norm_num [Finset.sum_range_one] at h ⊢
    exact h
  have hl0 : l = msA 0 := by
    apply natCast_inj_lt hl (by rw [← hK]; exact hmsA 0)
    rw [hSA] at hg1
    push_cast at hg1
    linear_combination hg1
  have hmsB1 : msB 1 = b1n + 2 ^ 5 * b2n := by
    apply natCast_inj_lt (by rw [← hK]; exact hmsB 1)
      (by have := append_lt hb1n hb2n; norm_num at this; exact this)
    push_cast
    linear_combination hg4
  refine ⟨lvA + 2 ^ 240 * (msB 0 + 2 ^ 10 * b1n), b2n + 2 ^ 5 * cnv,
    ?_, ?_, ?_, ?_, ?_⟩
  · have hin : msB 0 + 2 ^ 10 * b1n < 2 ^ 15 := by
      have h := append_lt (show msB 0 < 2 ^ 10 from by rw [← hK]; exact hmsB 0) hb1n
      norm_num at h
      exact h
    have h := append_lt hlvA_lt hin
    norm_num at h
    exact h
  · have h := append_lt hb2n hcnv_lt
    norm_num at h
    exact h
  · rw [hg2, hSB]
    push_cast
    ring
  · rw [hg3]
    push_cast
    ring
  · apply merkleChunks_eq hmsA hmsB hmsC
    rw [hSA, hSB, ← hl0, hmsB1]
    ring

/-! ### The honest decomposition -/

set_option exponentiation.threshold 600 in
/-- Decomposing the packed message value into the three honest piece values. -/
private theorem merkle_honest_sum (l lv rv : ℕ) :
    l + 2 ^ 10 * lv + 2 ^ 265 * rv
      = (l + 2 ^ 10 * (lv % 2 ^ 240))
        + 2 ^ 250 * (lv / 2 ^ 240 % 2 ^ 10 + 2 ^ 10 * (lv / 2 ^ 250)
            + 2 ^ 15 * (rv % 2 ^ 5))
        + 2 ^ 270 * (rv / 2 ^ 5) := by
  omega

set_option exponentiation.threshold 600 in
/-- The `MerkleCRH` chunks of the canonical encodings are the honest pieces' chunks. -/
private theorem honest_chunks {l lv rv : ℕ} (hl : l < 2 ^ 10) (hlv : lv < 2 ^ 255)
    (hrv : rv < 2 ^ 255) :
    merkleChunks l lv rv
      = (List.range 25).map
          (fun j => (l + 2 ^ 10 * (lv % 2 ^ 240)) / 2 ^ (K * j) % 2 ^ K)
        ++ ((List.range 2).map
            (fun j => (lv / 2 ^ 240 % 2 ^ 10 + 2 ^ 10 * (lv / 2 ^ 250)
                + 2 ^ 15 * (rv % 2 ^ 5)) / 2 ^ (K * j) % 2 ^ K)
          ++ (List.range 25).map (fun j => rv / 2 ^ 5 / 2 ^ (K * j) % 2 ^ K)) := by
  have hK : Orchard.Specs.Sinsemilla.K = 10 := rfl
  have haN : l + 2 ^ 10 * (lv % 2 ^ 240) < 2 ^ (K * 25) := by
    rw [hK]
    have h := append_lt hl (Nat.mod_lt lv (y := 2 ^ 240) (by positivity))
    norm_num at h ⊢
    exact h
  have hb1n : lv / 2 ^ 250 < 2 ^ 5 := by
    apply Nat.div_lt_of_lt_mul
    rw [← pow_add]
    exact hlv
  have hbN : lv / 2 ^ 240 % 2 ^ 10 + 2 ^ 10 * (lv / 2 ^ 250)
      + 2 ^ 15 * (rv % 2 ^ 5) < 2 ^ (K * 2) := by
    rw [hK]
    have hin : lv / 2 ^ 250 + 2 ^ 5 * (rv % 2 ^ 5) < 2 ^ 10 := by
      have h := append_lt hb1n (Nat.mod_lt rv (y := 2 ^ 5) (by positivity))
      norm_num at h
      exact h
    have h := append_lt (Nat.mod_lt (lv / 2 ^ 240) (y := 2 ^ 10) (by positivity)) hin
    norm_num at h ⊢
    calc lv / 2 ^ 240 % 2 ^ 10 + 2 ^ 10 * (lv / 2 ^ 250) + 2 ^ 15 * (rv % 2 ^ 5)
        = lv / 2 ^ 240 % 2 ^ 10
          + 2 ^ 10 * (lv / 2 ^ 250 + 2 ^ 5 * (rv % 2 ^ 5)) := by ring
      _ < 1048576 := h
  have hcN : rv / 2 ^ 5 < 2 ^ (K * 25) := by
    rw [hK]
    apply Nat.div_lt_of_lt_mul
    rw [← pow_add]
    exact hrv
  apply merkleChunks_eq (fun j => Nat.mod_lt _ (by positivity))
    (fun j => Nat.mod_lt _ (by positivity))
    (fun j => Nat.mod_lt _ (by positivity))
  rw [sum_words K 25 _ haN, sum_words K 2 _ hbN, sum_words K 25 _ hcN]
  exact merkle_honest_sum l lv rv

private theorem p_lt_two_pow_255 : PALLAS_BASE_CARD < 2 ^ 255 := by
  norm_num [PALLAS_BASE_CARD]

private theorem two_pow_250_lt_p : (2 : ℕ) ^ 250 < PALLAS_BASE_CARD := by
  norm_num [PALLAS_BASE_CARD]

set_option exponentiation.threshold 600 in
/-- The honest piece values are in range and their chunk words make up the
`MerkleCRH` message. -/
private theorem honest_pieces {l lv rv : ℕ} (hl : l < 2 ^ 10)
    (hlv : lv < 2 ^ 255) (hrv : rv < 2 ^ 255)
    {aCell bCell cCell : Ecc.Fp}
    (haw : aCell = ((l + 2 ^ 10 * (lv % 2 ^ 240) : ℕ) : Ecc.Fp))
    (hbw : bCell = ((lv / 2 ^ 240 % 2 ^ 10 + 2 ^ 10 * (lv / 2 ^ 250)
      + 2 ^ 15 * (rv % 2 ^ 5) : ℕ) : Ecc.Fp))
    (hcw : cCell = ((rv / 2 ^ 5 : ℕ) : Ecc.Fp)) :
    (ZMod.val aCell < 2 ^ (K * 25) ∧ ZMod.val bCell < 2 ^ (K * 2)
      ∧ ZMod.val cCell < 2 ^ (K * 25))
    ∧ List.map (pieceWord aCell) (List.range 25)
        ++ (List.map (pieceWord bCell) (List.range 2)
          ++ List.map (pieceWord cCell) (List.range 25))
        = merkleChunks l lv rv := by
  subst haw hbw hcw
  have hK : Orchard.Specs.Sinsemilla.K = 10 := rfl
  have hvalA : ZMod.val ((l + 2 ^ 10 * (lv % 2 ^ 240) : ℕ) : Ecc.Fp)
      = l + 2 ^ 10 * (lv % 2 ^ 240) :=
    ZMod.val_natCast_of_lt (lt_trans (by omega) two_pow_250_lt_p)
  have hvalB : ZMod.val ((lv / 2 ^ 240 % 2 ^ 10 + 2 ^ 10 * (lv / 2 ^ 250)
        + 2 ^ 15 * (rv % 2 ^ 5) : ℕ) : Ecc.Fp)
      = lv / 2 ^ 240 % 2 ^ 10 + 2 ^ 10 * (lv / 2 ^ 250) + 2 ^ 15 * (rv % 2 ^ 5) :=
    ZMod.val_natCast_of_lt (lt_trans (by omega) two_pow_250_lt_p)
  have hvalC : ZMod.val ((rv / 2 ^ 5 : ℕ) : Ecc.Fp) = rv / 2 ^ 5 :=
    ZMod.val_natCast_of_lt (lt_trans (by omega) two_pow_250_lt_p)
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · rw [hvalA, hK]
    omega
  · rw [hvalB, hK]
    omega
  · rw [hvalC, hK]
    omega
  · rw [honest_chunks hl hlv hrv]
    congr 1
    · exact List.map_congr_left fun j _ => by
        show ZMod.val ((l + 2 ^ 10 * (lv % 2 ^ 240) : ℕ) : Ecc.Fp)
          / 2 ^ (K * j) % 2 ^ K = _
        rw [hvalA]
    congr 1
    · exact List.map_congr_left fun j _ => by
        show ZMod.val ((lv / 2 ^ 240 % 2 ^ 10 + 2 ^ 10 * (lv / 2 ^ 250)
            + 2 ^ 15 * (rv % 2 ^ 5) : ℕ) : Ecc.Fp) / 2 ^ (K * j) % 2 ^ K = _
        rw [hvalB]
    · exact List.map_congr_left fun j _ => by
        show ZMod.val ((rv / 2 ^ 5 : ℕ) : Ecc.Fp) / 2 ^ (K * j) % 2 ^ K = _
        rw [hvalC]

set_option exponentiation.threshold 600 in
/-- The decomposition-gate equations hold on the honest witness values. -/
private theorem honest_gate {l lv rv : ℕ} (hl : l < 2 ^ 10)
    (hlv : lv < 2 ^ 255) (_hrv : rv < 2 ^ 255)
    {aCell bCell b1Cell b2Cell cCell z1A z1B left right : Ecc.Fp}
    (haw : aCell = ((l + 2 ^ 10 * (lv % 2 ^ 240) : ℕ) : Ecc.Fp))
    (hb1w : b1Cell = ((lv / 2 ^ 250 : ℕ) : Ecc.Fp))
    (hb2w : b2Cell = ((rv % 2 ^ 5 : ℕ) : Ecc.Fp))
    (hbw : bCell = ((lv / 2 ^ 240 % 2 ^ 10 + 2 ^ 10 * (lv / 2 ^ 250)
      + 2 ^ 15 * (rv % 2 ^ 5) : ℕ) : Ecc.Fp))
    (hcw : cCell = ((rv / 2 ^ 5 : ℕ) : Ecc.Fp))
    (hz1A : z1A = pieceZ aCell 1) (hz1B : z1B = pieceZ bCell 1)
    (hleft : ((lv : ℕ) : Ecc.Fp) = left) (hright : ((rv : ℕ) : Ecc.Fp) = right) :
    ((l : ℕ) : Ecc.Fp) = aCell - z1A * twoPow10
      ∧ left = z1A + (bCell - z1B * twoPow10 + b1Cell * twoPow10) * twoPow240
      ∧ right = b2Cell + cCell * twoPow5
      ∧ z1B = b1Cell + b2Cell * twoPow5 := by
  have e5 : (twoPow5 : Ecc.Fp) = ((2 ^ 5 : ℕ) : Ecc.Fp) := by norm_num [twoPow5]
  have e10 : (twoPow10 : Ecc.Fp) = ((2 ^ 10 : ℕ) : Ecc.Fp) := by norm_num [twoPow10]
  have e240 : (twoPow240 : Ecc.Fp) = ((2 ^ 240 : ℕ) : Ecc.Fp) := by
    norm_num [twoPow240]
  have hvalA : ZMod.val ((l + 2 ^ 10 * (lv % 2 ^ 240) : ℕ) : Ecc.Fp)
      = l + 2 ^ 10 * (lv % 2 ^ 240) :=
    ZMod.val_natCast_of_lt (lt_trans (by omega) two_pow_250_lt_p)
  have hvalB : ZMod.val ((lv / 2 ^ 240 % 2 ^ 10 + 2 ^ 10 * (lv / 2 ^ 250)
        + 2 ^ 15 * (rv % 2 ^ 5) : ℕ) : Ecc.Fp)
      = lv / 2 ^ 240 % 2 ^ 10 + 2 ^ 10 * (lv / 2 ^ 250) + 2 ^ 15 * (rv % 2 ^ 5) :=
    ZMod.val_natCast_of_lt (lt_trans (by omega) two_pow_250_lt_p)
  have hzA : pieceZ aCell 1 = ((lv % 2 ^ 240 : ℕ) : Ecc.Fp) := by
    simp only [pieceZ, haw, hvalA]
    congr 1
    rw [show Orchard.Specs.Sinsemilla.K * 1 = 10 from rfl]
    omega
  have hzB : pieceZ bCell 1
      = ((lv / 2 ^ 250 + 2 ^ 5 * (rv % 2 ^ 5) : ℕ) : Ecc.Fp) := by
    simp only [pieceZ, hbw, hvalB]
    congr 1
    rw [show Orchard.Specs.Sinsemilla.K * 1 = 10 from rfl]
    omega
  subst hleft hright
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [haw, hz1A, hzA, e10]
    push_cast
    ring
  · rw [hz1A, hzA, hbw, hz1B, hzB, hb1w, e10, e240]
    have hnat : lv = lv % 2 ^ 240 + 2 ^ 240 * (lv / 2 ^ 240 % 2 ^ 10)
        + 2 ^ 250 * (lv / 2 ^ 250) := by omega
    have hc := congrArg (Nat.cast (R := Ecc.Fp)) hnat
    push_cast at hc ⊢
    linear_combination hc
  · rw [hb2w, hcw, e5]
    have hnat : rv = rv % 2 ^ 5 + 2 ^ 5 * (rv / 2 ^ 5) := by omega
    have hc := congrArg (Nat.cast (R := Ecc.Fp)) hnat
    push_cast at hc ⊢
    linear_combination hc
  · rw [hz1B, hzB, hb1w, hb2w, e5]
    push_cast
    ring

/-! ### `MerkleInstructions::hash_layer` -/

namespace HashLayer

/-- Inputs of one Merkle layer hash: the two child nodes. The layer index `l` is a
circuit parameter (a fixed column in the source). -/
structure Input (F : Type) where
  left : F
  right : F
deriving ProvableStruct

def main (G : Generators) (Q : SWPoint Pallas.curve) (hQ : Q ≠ 0) (l : ℕ)
    (input : Var Input Ecc.Fp) : Circuit Ecc.Fp (Expression Ecc.Fp) := do
  -- witness the three message pieces and the short sub-pieces b_1, b_2
  let a ← witnessField fun env =>
    ((l + 2 ^ 10 * ((env input.left).val % 2 ^ 240) : ℕ) : Ecc.Fp)
  let b1 ← witnessField fun env => (((env input.left).val / 2 ^ 250 : ℕ) : Ecc.Fp)
  let b2 ← witnessField fun env => (((env input.right).val % 2 ^ 5 : ℕ) : Ecc.Fp)
  let b ← witnessField fun env =>
    (((env input.left).val / 2 ^ 240 % 2 ^ 10
      + 2 ^ 10 * ((env input.left).val / 2 ^ 250)
      + 2 ^ 15 * ((env input.right).val % 2 ^ 5) : ℕ) : Ecc.Fp)
  let c ← witnessField fun env => (((env input.right).val / 2 ^ 5 : ℕ) : Ecc.Fp)
  -- constrain b_1 and b_2 to 5 bits
  Utilities.LookupRangeCheck.shortRangeCircuit 5 (by decide) { word := b1 }
  Utilities.LookupRangeCheck.shortRangeCircuit 5 (by decide) { word := b2 }
  -- hash = SinsemillaHashToPoint(Q, a || b || c)
  let out ← Entry.circuit G Q hQ 24 [1, 24] #v[a, b, c]
  -- the decomposition gate ties the pieces to (l, left, right)
  Merkle.circuit {
    aWhole := a, bWhole := b, cWhole := c,
    leftNode := input.left, rightNode := input.right,
    z1A := out.z1s[0], z1B := out.z1s[1],
    b1 := b1, b2 := b2,
    lWhole := Expression.const (l : Ecc.Fp) }
  return out.point.x

-- Hand-written elaboration data (NOT `elaborate_circuit`): the generated all-in-one
-- instance for this circuit produces a proof term whose kernel check exceeds the
-- default heartbeat budget (the hash subcircuit is large). Splitting the fields, with
-- an explicit `localLength`, keeps each kernel check small.
instance elaborated (G : Generators) (Q : SWPoint Pallas.curve) (hQ : Q ≠ 0)
    (l : ℕ) :
    ElaboratedCircuit Ecc.Fp Input field (main G Q hQ l) where
  localLength _ := 269
  localLength_eq := by
    intro input offset
    have hEL : ∀ x, (Entry.circuit G Q hQ 24 [1, 24]).localLength x = 262 := fun _ => rfl
    simp only [main, circuit_norm, hEL, _root_.Orchard.Sinsemilla.Merkle.circuit,
      Utilities.LookupRangeCheck.shortRangeCircuit]
  channelsLawful := by
    dsimp only [ElaboratedCircuit.ChannelsLawful]
    dsimp only [main]
    have hECg : (Entry.circuit G Q hQ 24 [1, 24]).channelsWithGuarantees = [] := rfl
    have hECr : (Entry.circuit G Q hQ 24 [1, 24]).channelsWithRequirements = [] := rfl
    simp only [circuit_norm, seval, _root_.Orchard.Sinsemilla.Merkle.circuit,
      Utilities.LookupRangeCheck.shortRangeCircuit, hECg, hECr]
    try trivial

def Spec (G : Generators) (Q : SWPoint Pallas.curve) (l : ℕ)
    (input : Value Input Ecc.Fp) (output : Value field Ecc.Fp)
    (_ : ProverData Ecc.Fp) : Prop :=
  ∃ lv rv : ℕ, lv < 2 ^ 255 ∧ rv < 2 ^ 255 ∧
    ((lv : ℕ) : Ecc.Fp) = input.left ∧ ((rv : ℕ) : Ecc.Fp) = input.right ∧
    ∀ B, Orchard.Specs.Sinsemilla.hashToPoint G.S Q (merkleChunks l lv rv) = some B →
      output = B.x

def ProverAssumptions (G : Generators) (Q : SWPoint Pallas.curve) (l : ℕ)
    (input : ProverValue Input Ecc.Fp) (_ : ProverData Ecc.Fp)
    (_ : ProverHint Ecc.Fp) : Prop :=
  ∃ B, Orchard.Specs.Sinsemilla.hashToPoint G.S Q
    (merkleChunks l (ZMod.val (show Ecc.Fp from input.left))
      (ZMod.val (show Ecc.Fp from input.right))) = some B

def ProverSpec (G : Generators) (Q : SWPoint Pallas.curve) (l : ℕ)
    (input : ProverValue Input Ecc.Fp) (output : ProverValue field Ecc.Fp)
    (_ : ProverHint Ecc.Fp) : Prop :=
  ∀ B, Orchard.Specs.Sinsemilla.hashToPoint G.S Q
      (merkleChunks l (ZMod.val (show Ecc.Fp from input.left))
        (ZMod.val (show Ecc.Fp from input.right))) = some B →
    output = B.x

theorem soundness (G : Generators) (Q : SWPoint Pallas.curve) (hQ : Q ≠ 0)
    (l : ℕ) (hl : l < 2 ^ 10) :
    GeneralFormalCircuit.WithHint.Soundness Ecc.Fp (main G Q hQ l)
      (fun _ _ => True) (Spec G Q l) := by
  circuit_proof_start [main, Spec, Entry.circuit, Entry.Spec,
    Merkle.circuit, Merkle.Spec, Merkle.a0, Merkle.b0,
    Utilities.LookupRangeCheck.shortRangeCircuit,
    Utilities.LookupRangeCheck.shortRangeSpec,
    Chain.PieceChunks, Chain.Z1Facts]
  obtain ⟨h_b1, h_b2, ⟨chunks, hPC, hZ1, hfun⟩, hg1, hg2, hg3, hg4⟩ := h_holds
  obtain ⟨b1n, hb1n, hb1⟩ : ∃ b1n, b1n < 2 ^ 5 ∧ env.get (i₀ + 1) = ((b1n : ℕ) : Ecc.Fp) :=
    ⟨_, h_b1, (ZMod.natCast_zmod_val _).symm⟩
  obtain ⟨b2n, hb2n, hb2⟩ : ∃ b2n, b2n < 2 ^ 5 ∧ env.get (i₀ + 1 + 1) = ((b2n : ℕ) : Ecc.Fp) :=
    ⟨_, h_b2, (ZMod.natCast_zmod_val _).symm⟩
  obtain ⟨msA, hmsA, haval, t1, rfl, msB, hmsB, hbval, t2, rfl,
    msC, hmsC, hcval, t3, rfl, rfl⟩ := hPC
  obtain ⟨hz1A, hz1B, -⟩ := hZ1
  simp only [List.append_nil] at hfun hz1A hz1B
  have haval' : env.get i₀
      = ((∑ r ∈ Finset.range 25, msA r * 2 ^ (K * r) : ℕ) : Ecc.Fp) := haval
  have hbval' : env.get (i₀ + 1 + 1 + 1)
      = ((∑ r ∈ Finset.range 2, msB r * 2 ^ (K * r) : ℕ) : Ecc.Fp) := hbval
  have hcval' : env.get (i₀ + 1 + 1 + 1 + 1)
      = ((∑ r ∈ Finset.range 25, msC r * 2 ^ (K * r) : ℕ) : Ecc.Fp) := hcval
  rw [Chain.z1Facts_head_sum] at hz1A
  rw [Chain.chunks_drop_append, Chain.z1Facts_head_sum] at hz1B
  simp only [Finset.sum_range_one, Nat.mul_zero, pow_zero, Nat.mul_one] at hz1B
  -- restate the z1 facts with consistent length spellings, so that the vector
  -- indexing lemmas match (the raw hypotheses mix defeq spellings of the length)
  have hlen0 : (0 : ℕ) < [1, 24].length + 1 := by simp
  have hlenT : (0 : ℕ) < [1, 24].length + 1 - 1 := by simp
  have hz1A' : (Vector.map (Expression.eval env)
        (Entry.main G Q 24 [1, 24]
            #v[Expression.var ⟨i₀⟩, Expression.var ⟨i₀ + 1 + 1 + 1⟩,
              Expression.var ⟨i₀ + 1 + 1 + 1 + 1⟩]
            (i₀ + 1 + 1 + 1 + 1 + 1 + 1 + 1)).1.z1s)[0]'(by simp)
      = ((∑ j ∈ Finset.range 24, msA (j + 1) * 2 ^ (K * j) : ℕ) : Ecc.Fp) := hz1A
  have hz1B' : (Vector.map (Expression.eval env)
        (Entry.main G Q 24 [1, 24]
            #v[Expression.var ⟨i₀⟩, Expression.var ⟨i₀ + 1 + 1 + 1⟩,
              Expression.var ⟨i₀ + 1 + 1 + 1 + 1⟩]
            (i₀ + 1 + 1 + 1 + 1 + 1 + 1 + 1)).1.z1s).tail[0]'(by simp)
      = ((msB 1 : ℕ) : Ecc.Fp) := hz1B
  rw [Vector.getElem_tail hlenT] at hz1B'
  simp only [Vector.getElem_map] at hz1A' hz1B'
  have hasm := assemble hmsA hmsB hmsC hl hb1n hb2n
    haval' hbval' hcval' hb1 hb2 hz1A' hz1B' hg1 hg2 hg3 hg4
  obtain ⟨lv, rv, hlv, hrv, hlcast, hrcast, hchunks⟩ := hasm
  refine ⟨lv, rv, hlv, hrv, hlcast, hrcast, ?_⟩
  intro B hB
  rw [hchunks] at hB
  exact congrArg Ecc.Point.x (hfun B hB)

theorem completeness (G : Generators) (Q : SWPoint Pallas.curve) (hQ : Q ≠ 0)
    (l : ℕ) (hl : l < 2 ^ 10) :
    GeneralFormalCircuit.WithHint.Completeness Ecc.Fp (main G Q hQ l)
      (ProverAssumptions G Q l) (ProverSpec G Q l) := by
  circuit_proof_start [main, ProverSpec, ProverAssumptions, Entry.circuit,
    Entry.ProverAssumptions, Entry.ProverSpec, Merkle.circuit, Merkle.Spec,
    Merkle.a0, Merkle.b0, Utilities.LookupRangeCheck.shortRangeCircuit,
    Utilities.LookupRangeCheck.shortRangeSpec, Chain.PieceBounds,
    Chain.honestChunks, Chain.Z1sHonest,
    Vector.tail_eq_cast_extract, Vector.extract_mk, List.extract_toArray,
    List.extract_eq_drop_take, List.size_toArray, Vector.cast_rfl,
    Vector.getElem_map, Vector.getElem_extract, Nat.min_self, Vector.getElem_mk,
    List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ,
    List.length_cons, List.length_nil, List.drop_succ_cons, List.drop_zero,
    List.take_succ_cons, List.take_zero, List.take_nil]
  obtain ⟨B, hchain⟩ := h_assumptions
  obtain ⟨ha_w, hb1_w, hb2_w, hb_w, hc_w, h_entry_env⟩ := h_env
  have hlv : ZMod.val input_left < 2 ^ 255 :=
    lt_trans (ZMod.val_lt input_left) p_lt_two_pow_255
  have hrv : ZMod.val input_right < 2 ^ 255 :=
    lt_trans (ZMod.val_lt input_right) p_lt_two_pow_255
  have hp := honest_pieces (l := l) (lv := ZMod.val input_left)
    (rv := ZMod.val input_right) (aCell := env.get i₀)
    (bCell := env.get (i₀ + 1 + 1 + 1)) (cCell := env.get (i₀ + 1 + 1 + 1 + 1))
    hl hlv hrv ha_w hb_w hc_w
  have hex : ∃ B', Specs.Sinsemilla.hashToPoint G.S Q
      (List.map (pieceWord (env.get i₀)) (List.range 25)
        ++ (List.map (pieceWord (env.get (i₀ + 1 + 1 + 1))) (List.range 2)
          ++ List.map (pieceWord (env.get (i₀ + 1 + 1 + 1 + 1))) (List.range 25)))
      = some B' := ⟨B, by rw [hp.2]; exact hchain⟩
  obtain ⟨⟨hzh1, hzh2, -⟩, hBfun⟩ := (h_entry_env ⟨hp.1, hex⟩).2
  have hzh2' := (Vector.getElem_extract (by simp)).symm.trans hzh2
  have hzh2'' := (Vector.getElem_map (Expression.eval env.toEnvironment)
    (by simp)).symm.trans hzh2'
  have hg := honest_gate (l := l) (lv := ZMod.val input_left)
    (rv := ZMod.val input_right) (aCell := env.get i₀)
    (bCell := env.get (i₀ + 1 + 1 + 1)) (b1Cell := env.get (i₀ + 1))
    (b2Cell := env.get (i₀ + 1 + 1)) (cCell := env.get (i₀ + 1 + 1 + 1 + 1))
    (left := input_left) (right := input_right)
    hl hlv hrv ha_w hb1_w hb2_w hb_w hc_w hzh1 hzh2''
    (ZMod.natCast_zmod_val input_left) (ZMod.natCast_zmod_val input_right)
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [hb1_w]
    have hd : ZMod.val input_left / 2 ^ 250 < 2 ^ 5 :=
      Nat.div_lt_of_lt_mul (by rw [← pow_add]; exact hlv)
    rw [ZMod.val_natCast_of_lt (lt_trans hd (by norm_num [PALLAS_BASE_CARD]))]
    exact hd
  · rw [hb2_w]
    have hd : ZMod.val input_right % 2 ^ 5 < 2 ^ 5 := Nat.mod_lt _ (by norm_num)
    rw [ZMod.val_natCast_of_lt (lt_trans hd (by norm_num [PALLAS_BASE_CARD]))]
    exact hd
  · exact ⟨hp.1, hex⟩
  · exact hg.1
  · exact hg.2.1
  · exact hg.2.2.1
  · exact hg.2.2.2
  · intro B' hB'
    refine congrArg Ecc.Point.x (hBfun B' ?_)
    show Specs.Sinsemilla.hashToPoint G.S Q
      (List.map (pieceWord (env.get i₀)) (List.range 25)
        ++ (List.map (pieceWord (env.get (i₀ + 1 + 1 + 1))) (List.range 2)
          ++ List.map (pieceWord (env.get (i₀ + 1 + 1 + 1 + 1))) (List.range 25)))
      = some B'
    rw [hp.2]
    exact hB'

def circuit (G : Generators) (Q : SWPoint Pallas.curve) (hQ : Q ≠ 0)
    (l : ℕ) (hl : l < 2 ^ 10) :
    GeneralFormalCircuit.WithHint Ecc.Fp Input field where
  main := main G Q hQ l
  Spec := Spec G Q l
  ProverAssumptions := ProverAssumptions G Q l
  ProverSpec := ProverSpec G Q l
  soundness := soundness G Q hQ l hl
  completeness := completeness G Q hQ l hl

end HashLayer

def depth : ℕ := 32

def MerkleStep (G : Generators) (Q : SWPoint Pallas.curve) (l : ℕ)
    (node node' : Ecc.Fp) : Prop :=
  ∃ lv rv : ℕ, lv < 2 ^ 255 ∧ rv < 2 ^ 255 ∧
    ((lv : Ecc.Fp) = node ∨ (rv : Ecc.Fp) = node) ∧
    ∀ B, Specs.Sinsemilla.hashToPoint G.S Q (merkleChunks l lv rv) = some B →
      node' = B.x

def MerkleRoot (G : Generators) (Q : SWPoint Pallas.curve) :
    ℕ → Ecc.Fp → ℕ → Ecc.Fp → Prop
  | _, node, 0, root => root = node
  | l, node, k + 1, root =>
    ∃ mid, MerkleStep G Q l node mid ∧ MerkleRoot G Q (l + 1) mid k root

namespace Layer

structure Input (F : Type) where
  node : F
  sibling : UnconstrainedDep field F
  posBit : Unconstrained Bool F
deriving CircuitType

instance : Inhabited (Var Input Ecc.Fp) :=
  ⟨{ node := default, sibling := fun _ => default, posBit := fun _ => default }⟩

def main (G : Generators) (Q : SWPoint Pallas.curve) (hQ : Q ≠ 0) (l : ℕ) (hl : l < 2 ^ 10)
    (input : Var Input Ecc.Fp) : Circuit Ecc.Fp (Var field Ecc.Fp) := do
  let sw ← Utilities.CondSwap.Swap.circuit
    { a := input.node, b := input.sibling, swap := input.posBit }
  HashLayer.circuit G Q hQ l hl { left := sw.aSwapped, right := sw.bSwapped }

instance elaborated (G : Generators) (Q : SWPoint Pallas.curve) (hQ : Q ≠ 0)
    (l : ℕ) (hl : l < 2 ^ 10) :
    ElaboratedCircuit Ecc.Fp Input field (main G Q hQ l hl) where
  localLength _ := 274
  localLength_eq := by
    intro input offset
    have hHL : ∀ x, (HashLayer.circuit G Q hQ l hl).localLength x = 269 := fun _ => rfl
    simp only [main, circuit_norm, hHL, Utilities.CondSwap.Swap.circuit]
  channelsLawful := by
    dsimp only [ElaboratedCircuit.ChannelsLawful]
    dsimp only [main]
    have hHLg : (HashLayer.circuit G Q hQ l hl).channelsWithGuarantees = [] := rfl
    have hHLr : (HashLayer.circuit G Q hQ l hl).channelsWithRequirements = [] := rfl
    simp only [circuit_norm, seval, Utilities.CondSwap.Swap.circuit, hHLg, hHLr]
    try trivial

def Spec (G : Generators) (Q : SWPoint Pallas.curve) (l : ℕ)
    (input : Value Input Ecc.Fp) (output : Value field Ecc.Fp)
    (_ : ProverData Ecc.Fp) : Prop :=
  MerkleStep G Q l input.node output

theorem soundness (G : Generators) (Q : SWPoint Pallas.curve) (hQ : Q ≠ 0)
    (l : ℕ) (hl : l < 2 ^ 10) :
    GeneralFormalCircuit.WithHint.Soundness Ecc.Fp (main G Q hQ l hl)
      (fun _ _ => True) (Spec G Q l) := by
  circuit_proof_start [main, Spec, Utilities.CondSwap.Swap.circuit,
    Utilities.CondSwap.Swap.Spec, HashLayer.circuit, HashLayer.Spec, MerkleStep]
  obtain ⟨⟨b, swap, hbool, hsw⟩, lv, rv, hlv, hrv, hlv_eq, hrv_eq, hfun⟩ := h_holds
  refine ⟨lv, rv, hlv, hrv, ?_, hfun⟩
  rcases hbool with h0 | h1
  · rw [if_neg (by rw [h0]; exact zero_ne_one)] at hsw
    simp only [Utilities.CondSwapOutput.mk.injEq] at hsw
    exact Or.inl (by rw [hlv_eq]; exact hsw.1)
  · rw [if_pos h1] at hsw
    simp only [Utilities.CondSwapOutput.mk.injEq] at hsw
    exact Or.inr (by rw [hrv_eq]; exact hsw.2)

/-- The swapped pair (left, right) hashed by this layer, as `MerkleCRH` chunks: the
position bit selects which of `node`/`sibling` is the left child. -/
def proverChunks (l : ℕ) (input : ProverValue Input Ecc.Fp) : List ℕ :=
  merkleChunks l
    (ZMod.val (show Ecc.Fp from if input.posBit then input.sibling else input.node))
    (ZMod.val (show Ecc.Fp from if input.posBit then input.node else input.sibling))

def ProverAssumptions (G : Generators) (Q : SWPoint Pallas.curve) (l : ℕ)
    (input : ProverValue Input Ecc.Fp) (_ : ProverData Ecc.Fp) (_ : ProverHint Ecc.Fp) : Prop :=
  ∃ B, Specs.Sinsemilla.hashToPoint G.S Q (proverChunks l input) = some B

def ProverSpec (G : Generators) (Q : SWPoint Pallas.curve) (l : ℕ)
    (input : ProverValue Input Ecc.Fp) (output : ProverValue field Ecc.Fp)
    (_ : ProverHint Ecc.Fp) : Prop :=
  ∀ B, Specs.Sinsemilla.hashToPoint G.S Q (proverChunks l input) = some B → output = B.x

theorem completeness (G : Generators) (Q : SWPoint Pallas.curve) (hQ : Q ≠ 0)
    (l : ℕ) (hl : l < 2 ^ 10) :
    GeneralFormalCircuit.WithHint.Completeness Ecc.Fp (main G Q hQ l hl)
      (ProverAssumptions G Q l) (ProverSpec G Q l) := by
  circuit_proof_start [main, ProverSpec, ProverAssumptions, proverChunks,
    Utilities.CondSwap.Swap.circuit, Utilities.CondSwap.Swap.ProverSpec,
    Utilities.CondSwap.Swap.outputValue,
    HashLayer.circuit, HashLayer.ProverAssumptions, HashLayer.ProverSpec]
  -- the swap subcircuit pins its two output cells to the position-selected pair, so the
  -- hash subcircuit's prover assumption is exactly our hypothesis.
  obtain ⟨⟨-, hsw⟩, hHL⟩ := h_env
  injection hsw with h3 h4
  rw [h3, h4] at hHL ⊢
  exact ⟨h_assumptions, (hHL h_assumptions).2⟩

def circuit (G : Generators) (Q : SWPoint Pallas.curve) (hQ : Q ≠ 0)
    (l : ℕ) (hl : l < 2 ^ 10) :
    GeneralFormalCircuit.WithHint Ecc.Fp Input field where
  main := main G Q hQ l hl
  Spec := Spec G Q l
  ProverAssumptions := ProverAssumptions G Q l
  ProverSpec := ProverSpec G Q l
  soundness := soundness G Q hQ l hl
  completeness := completeness G Q hQ l hl

end Layer

/-- Forward induction: a chain of `MerkleStep`s assembles into a `MerkleRoot`. -/
private theorem merkleRoot_of_steps (G : Generators) (Q : SWPoint Pallas.curve)
    (f : ℕ → Ecc.Fp) (l : ℕ) :
    ∀ k, (∀ i, i < k → MerkleStep G Q (l + i) (f i) (f (i + 1))) →
      MerkleRoot G Q l (f 0) k (f k) := by
  intro k
  induction k generalizing l f with
  | zero => intro _; rfl
  | succ k ih =>
    intro h
    refine ⟨f 1, ?_, ?_⟩
    · have h0 := h 0 (Nat.succ_pos k)
      simpa using h0
    · have hres := ih (l := l + 1) (f := fun i => f (i + 1)) (fun i hi => by
        have hi' := h (i + 1) (by omega)
        have : l + 1 + i = l + (i + 1) := by omega
        rw [this]; exact hi')
      simpa using hres

namespace CalculateRoot

structure Input (F : Type) where
  leaf : F
  path : UnconstrainedDep (fields 32) F
  pos : Unconstrained (Vector Bool 32) F
deriving CircuitType

instance : Inhabited (Var Input Ecc.Fp) :=
  ⟨{ leaf := default, path := fun _ => default, pos := fun _ => default }⟩

def main (G : Generators) (Q : SWPoint Pallas.curve) (hQ : Q ≠ 0)
    (input : Var Input Ecc.Fp) : Circuit Ecc.Fp (Var field Ecc.Fp) :=
  Circuit.foldl (.finRange 32) input.leaf
    (fun node i => Layer.circuit G Q hQ i.val (by omega)
      { node := node,
        sibling := fun env => (show Vector Ecc.Fp 32 from input.path env)[i],
        posBit := fun env => (show Vector Bool 32 from input.pos env)[i] })

instance elaborated (G : Generators) (Q : SWPoint Pallas.curve) (hQ : Q ≠ 0) :
    ElaboratedCircuit Ecc.Fp Input field (main G Q hQ) where
  localLength _ := 32 * 274
  localLength_eq := by
    intro input offset
    have hL : ∀ (l : ℕ) (hl : l < 2 ^ 10) x,
        (Layer.circuit G Q hQ l hl).localLength x = 274 := fun _ _ _ => rfl
    simp only [main, circuit_norm, hL]
  subcircuitsConsistent := by
    intro input offset
    rw [Operations.SubcircuitsConsistent, ← Circuit.forAll_def]
    show (Circuit.foldl (.finRange 32) input.leaf _ _ _).forAll offset _
    rw [Circuit.foldl, Circuit.FoldlM.forAll_iff_finRange]
    · intro i
      simp only [circuit_norm, Layer.circuit]
    · apply Circuit.ConstantLength.fromConstantLength'
      intro acc i i' n
      rfl
  channelsLawful := by
    dsimp only [ElaboratedCircuit.ChannelsLawful]
    intro input_var offset
    dsimp only [main]
    have hLg : ∀ (l : ℕ) (hl : l < 2 ^ 10),
        (Layer.circuit G Q hQ l hl).channelsWithGuarantees = [] := fun _ _ => rfl
    have hLr : ∀ (l : ℕ) (hl : l < 2 ^ 10),
        (Layer.circuit G Q hQ l hl).channelsWithRequirements = [] := fun _ _ => rfl
    simp only [circuit_norm, seval, hLg, hLr]
    try trivial

def Spec (G : Generators) (Q : SWPoint Pallas.curve)
    (input : Value Input Ecc.Fp) (output : Value field Ecc.Fp)
    (_ : ProverData Ecc.Fp) : Prop :=
  MerkleRoot G Q 0 input.leaf depth output

theorem soundness (G : Generators) (Q : SWPoint Pallas.curve) (hQ : Q ≠ 0) :
    GeneralFormalCircuit.WithHint.Soundness Ecc.Fp (main G Q hQ)
      (fun _ _ => True) (Spec G Q) := by
  circuit_proof_start [main, Spec]
  obtain ⟨h0, hstep⟩ := h_holds
  refine ⟨?_, Or.inl rfl, fun i hi => Or.inl rfl⟩
  -- The per-layer output is a pure offset reference: independent of the layer index,
  -- the input record, and the well-formedness proof. So we canonicalize the running
  -- node to a single offset-indexed form. The bridging equalities below all hold by
  -- `rfl` (the kernel reduces the output lazily, ignoring the discarded fields), which
  -- is far cheaper than a `simp` traversal over the large fold expressions.
  have hpf : (0 : ℕ) < 2 ^ 10 := by norm_num
  have hlen : ∀ (l : ℕ) (hl : l < 2 ^ 10) (inp : Var Layer.Input Ecc.Fp),
      (Layer.circuit G Q hQ l hl).localLength inp = 274 := fun _ _ _ => rfl
  -- `bridge` is the key kernel-cheap rewrite. The per-layer output is a pure offset
  -- reference, so as a *value* it is independent of layer index, input record and
  -- well-formedness proof; `bridge` says so, with an offset-equality hypothesis folded
  -- in. It is proved by `rfl` over *opaque* arguments — the kernel checks that body once
  -- and every *application* is mere type instantiation, so no concrete fold output is
  -- ever reduced (which is what blew the budget). Offset gaps are discharged purely at
  -- the `ℕ` level via `hlen`, again touching no output subterm.
  have bridge : ∀ (l : ℕ) (hl : l < 2 ^ 10) (inp : Var Layer.Input Ecc.Fp) (o₁ o₂ : ℕ),
      o₁ = o₂ →
      Expression.eval env ((Layer.circuit G Q hQ l hl).output inp o₁)
        = Expression.eval env ((Layer.circuit G Q hQ 0 hpf).output default o₂) := by
    intro l hl inp o₁ o₂ h; subst h; rfl
  -- state function: f 0 = leaf, f (j+1) = canonical output value at offset i₀ + j*274
  let f : ℕ → Ecc.Fp := fun n => match n with
    | 0 => input_leaf
    | j + 1 => Expression.eval env
        ((Layer.circuit G Q hQ 0 hpf).output default (i₀ + j * 274))
  have hsteps : ∀ i, i < 32 → MerkleStep G Q (0 + i) (f i) (f (i + 1)) := by
    intro i hi
    rw [Nat.zero_add]
    obtain _ | j := i
    · obtain ⟨lv, rv, hlv, hrv, hcase, hfun⟩ := h0 trivial
      -- layer-0 input node is the leaf itself (`f 0`), so the node part is a definitional
      -- `rfl`; only the output goes through `bridge`.
      refine ⟨lv, rv, hlv, hrv,
        hcase.imp (fun h => h.trans rfl) (fun h => h.trans rfl),
        fun B hB => (bridge 0 hpf _ _ _ (by simp)).symm.trans (hfun B hB)⟩
    · obtain ⟨lv, rv, hlv, hrv, hcase, hfun⟩ := hstep j (by omega) trivial
      refine ⟨lv, rv, hlv, hrv,
        hcase.imp (fun h => h.trans (bridge j (by omega) _ _ _ (by simp [hlen])))
          (fun h => h.trans (bridge j (by omega) _ _ _ (by simp [hlen]))),
        fun B hB => (bridge (j + 1) (by omega) _ _ _ (by simp [hlen])).symm.trans (hfun B hB)⟩
  have hconcl : MerkleRoot G Q 0 (f 0) 32 (f 32) := merkleRoot_of_steps G Q f 0 32 hsteps
  -- the foldl output `goalOut` is the layer-31 canonical output; bridge it to `f 32`
  -- without reducing the output expression.
  refine Eq.mp (congrArg (MerkleRoot G Q 0 (f 0) 32) ?_) hconcl
  exact (bridge 31 (by omega) _ _ _ (by simp [hlen])).symm

end CalculateRoot

end Orchard.Sinsemilla.Merkle
