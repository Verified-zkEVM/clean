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
5 bits. The `q_decompose` gate (`Merkle.Gate.circuit`, the `Decomposition check`) ties the
pieces to `(l, left, right)` through the hash's own `z_1` running-sum cells, which
`hash_to_point` exposes.
-/

namespace Orchard.Sinsemilla.Merkle

open CompElliptic.Curves.Pasta
open CompElliptic.Fields.Pasta (PALLAS_BASE_CARD)
open Specs.Sinsemilla (Generators merkleChunks)
open Specs (K bitrange bitrange_lt bitrange_zero bitrange_eq_div_of_lt)

/-! ### MerkleCRH decomposition gate

Reference:
`halo2@halo2_gadgets-0.5.0/halo2_gadgets/src/sinsemilla/merkle/chip.rs`
- `Decomposition check`

Ports the `q_decompose` gate that connects the three Sinsemilla message pieces
`a`, `b`, `c` to `(l, left, right)`. -/

def twoPow5 {K : Type} [OfNat K (2 ^ 5)] : K := OfNat.ofNat (2 ^ 5)

def twoPow10 {K : Type} [OfNat K (2 ^ 10)] : K := OfNat.ofNat (2 ^ 10)

def twoPow240 {K : Type} [OfNat K (2 ^ 240)] : K := OfNat.ofNat (2 ^ 240)

namespace Gate

structure Row (F : Type) where
  aWhole : F
  bWhole : F
  cWhole : F
  leftNode : F
  rightNode : F
  z1A : F
  z1B : F
  b1 : F
  b2 : F
  lWhole : F
deriving ProvableStruct

def a0 {K : Type} [Sub K] [Mul K] [OfNat K (2 ^ 10)] (row : Row K) : K :=
  row.aWhole - row.z1A * twoPow10

def b1B2Check {K : Type} [Add K] [Sub K] [Mul K] [OfNat K (2 ^ 5)]
    (row : Row K) : K :=
  row.z1B - (row.b1 + row.b2 * twoPow5)

def b0 {K : Type} [Sub K] [Mul K] [OfNat K (2 ^ 10)] (row : Row K) : K :=
  row.bWhole - row.z1B * twoPow10

def leftCheck {K : Type} [Add K] [Sub K] [Mul K] [OfNat K (2 ^ 10)]
    [OfNat K (2 ^ 240)] (row : Row K) : K :=
  let reconstructed := row.z1A + (b0 row + row.b1 * twoPow10) * twoPow240
  reconstructed - row.leftNode

def rightCheck {K : Type} [Add K] [Sub K] [Mul K] [OfNat K (2 ^ 5)]
    (row : Row K) : K :=
  row.b2 + row.cWhole * twoPow5 - row.rightNode

def Spec (row : Row Fp) : Prop :=
  row.lWhole = a0 row ∧
  row.leftNode = row.z1A + (b0 row + row.b1 * twoPow10) * twoPow240 ∧
  row.rightNode = row.b2 + row.cWhole * twoPow5 ∧
  row.z1B = row.b1 + row.b2 * twoPow5

def main (row : Var Row Fp) : Circuit Fp Unit := do
  assertZero (a0 row - row.lWhole)
  assertZero (leftCheck row)
  assertZero (rightCheck row)
  assertZero (b1B2Check row)

def circuit : FormalAssertion Fp Row where
  name := "GATE Decomposition check"
  main
  Spec
  soundness := by
    circuit_proof_start [main, Spec, a0, leftCheck, rightCheck, b1B2Check,
      b0, twoPow5, twoPow10, twoPow240]
    rcases h_holds with ⟨hl, hleft, hright, hb⟩
    exact ⟨(sub_eq_zero.mp hl).symm, (sub_eq_zero.mp hleft).symm,
      (sub_eq_zero.mp hright).symm, sub_eq_zero.mp hb⟩
  completeness := by
    circuit_proof_start [main, Spec, a0, leftCheck, rightCheck, b1B2Check,
      b0, twoPow5, twoPow10, twoPow240]
    rcases h_spec with ⟨hl, hleft, hright, hb⟩
    constructor
    · rw [hl]
      ring
    constructor
    · rw [hleft]
      ring
    constructor
    · rw [hright]
      ring
    · rw [hb]
      ring

end Gate

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
    (h : (a : Fp) = (b : Fp)) : a = b := by
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
    {aCell bCell cCell b1Cell b2Cell z1A z1B left right : Fp}
    (haval : aCell = ((∑ r ∈ Finset.range 25, msA r * 2 ^ (K * r) : ℕ) : Fp))
    (hbval : bCell = ((∑ r ∈ Finset.range 2, msB r * 2 ^ (K * r) : ℕ) : Fp))
    (hcval : cCell = ((∑ r ∈ Finset.range 25, msC r * 2 ^ (K * r) : ℕ) : Fp))
    (hb1 : b1Cell = ((b1n : ℕ) : Fp)) (hb2 : b2Cell = ((b2n : ℕ) : Fp))
    (hz1A : z1A = ((∑ j ∈ Finset.range 24, msA (j + 1) * 2 ^ (K * j) : ℕ) : Fp))
    (hz1B : z1B = ((msB 1 : ℕ) : Fp))
    (hg1 : (l : Fp) = aCell - z1A * twoPow10)
    (hg2 : left = z1A + (bCell - z1B * twoPow10 + b1Cell * twoPow10) * twoPow240)
    (hg3 : right = b2Cell + cCell * twoPow5)
    (hg4 : z1B = b1Cell + b2Cell * twoPow5) :
    ∃ lv rv : ℕ, lv < 2 ^ 255 ∧ rv < 2 ^ 255 ∧
      ((lv : ℕ) : Fp) = left ∧ ((rv : ℕ) : Fp) = right ∧
      merkleChunks l lv rv
        = (List.range 25).map msA
          ++ ((List.range 2).map msB ++ (List.range 25).map msC) := by
  subst haval hbval hcval hb1 hb2 hz1A hz1B
  have hK : K = 10 := rfl
  have e5 : (twoPow5 : Fp) = ((2 ^ 5 : ℕ) : Fp) := by norm_num [twoPow5]
  have e10 : (twoPow10 : Fp) = ((2 ^ 10 : ℕ) : Fp) := by norm_num [twoPow10]
  have e240 : (twoPow240 : Fp) = ((2 ^ 240 : ℕ) : Fp) := by
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
  have hK : K = 10 := rfl
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
    {aCell bCell cCell : Fp}
    (haw : aCell = ((l + 2 ^ 10 * bitrange lv 0 240 : ℕ) : Fp))
    (hbw : bCell = ((bitrange lv 240 10 + 2 ^ 10 * bitrange lv 250 5
      + 2 ^ 15 * bitrange rv 0 5 : ℕ) : Fp))
    (hcw : cCell = ((bitrange rv 5 250 : ℕ) : Fp)) :
    (ZMod.val aCell < 2 ^ (K * 25) ∧ ZMod.val bCell < 2 ^ (K * 2)
      ∧ ZMod.val cCell < 2 ^ (K * 25))
    ∧ List.map (pieceWord aCell) (List.range 25)
        ++ (List.map (pieceWord bCell) (List.range 2)
          ++ List.map (pieceWord cCell) (List.range 25))
        = merkleChunks l lv rv := by
  have hb240 : bitrange lv 240 10 = lv / 2 ^ 240 % 2 ^ 10 := rfl
  have hb250 : bitrange lv 250 5 = lv / 2 ^ 250 :=
    bitrange_eq_div_of_lt (Nat.div_lt_of_lt_mul (by rw [← pow_add]; exact hlv))
  have hc5 : bitrange rv 5 250 = rv / 2 ^ 5 :=
    bitrange_eq_div_of_lt (Nat.div_lt_of_lt_mul (by rw [← pow_add]; exact hrv))
  simp only [bitrange_zero, hb240, hb250, hc5] at haw hbw hcw
  subst haw hbw hcw
  have hK : K = 10 := rfl
  have hvalA : ZMod.val ((l + 2 ^ 10 * (lv % 2 ^ 240) : ℕ) : Fp)
      = l + 2 ^ 10 * (lv % 2 ^ 240) :=
    ZMod.val_natCast_of_lt (lt_trans (by omega) two_pow_250_lt_p)
  have hvalB : ZMod.val ((lv / 2 ^ 240 % 2 ^ 10 + 2 ^ 10 * (lv / 2 ^ 250)
        + 2 ^ 15 * (rv % 2 ^ 5) : ℕ) : Fp)
      = lv / 2 ^ 240 % 2 ^ 10 + 2 ^ 10 * (lv / 2 ^ 250) + 2 ^ 15 * (rv % 2 ^ 5) :=
    ZMod.val_natCast_of_lt (lt_trans (by omega) two_pow_250_lt_p)
  have hvalC : ZMod.val ((rv / 2 ^ 5 : ℕ) : Fp) = rv / 2 ^ 5 :=
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
        show ZMod.val ((l + 2 ^ 10 * (lv % 2 ^ 240) : ℕ) : Fp)
          / 2 ^ (K * j) % 2 ^ K = _
        rw [hvalA]
    congr 1
    · exact List.map_congr_left fun j _ => by
        show ZMod.val ((lv / 2 ^ 240 % 2 ^ 10 + 2 ^ 10 * (lv / 2 ^ 250)
            + 2 ^ 15 * (rv % 2 ^ 5) : ℕ) : Fp) / 2 ^ (K * j) % 2 ^ K = _
        rw [hvalB]
    · exact List.map_congr_left fun j _ => by
        show ZMod.val ((rv / 2 ^ 5 : ℕ) : Fp) / 2 ^ (K * j) % 2 ^ K = _
        rw [hvalC]

set_option exponentiation.threshold 600 in
/-- The decomposition-gate equations hold on the honest witness values. -/
private theorem honest_gate {l lv rv : ℕ} (hl : l < 2 ^ 10)
    (hlv : lv < 2 ^ 255) (hrv : rv < 2 ^ 255)
    {aCell bCell b1Cell b2Cell cCell z1A z1B left right : Fp}
    (haw : aCell = ((l + 2 ^ 10 * bitrange lv 0 240 : ℕ) : Fp))
    (hb1w : b1Cell = ((bitrange lv 250 5 : ℕ) : Fp))
    (hb2w : b2Cell = ((bitrange rv 0 5 : ℕ) : Fp))
    (hbw : bCell = ((bitrange lv 240 10 + 2 ^ 10 * bitrange lv 250 5
      + 2 ^ 15 * bitrange rv 0 5 : ℕ) : Fp))
    (hcw : cCell = ((bitrange rv 5 250 : ℕ) : Fp))
    (hz1A : z1A = pieceZ aCell 1) (hz1B : z1B = pieceZ bCell 1)
    (hleft : ((lv : ℕ) : Fp) = left) (hright : ((rv : ℕ) : Fp) = right) :
    ((l : ℕ) : Fp) = aCell - z1A * twoPow10
      ∧ left = z1A + (bCell - z1B * twoPow10 + b1Cell * twoPow10) * twoPow240
      ∧ right = b2Cell + cCell * twoPow5
      ∧ z1B = b1Cell + b2Cell * twoPow5 := by
  have hb240 : bitrange lv 240 10 = lv / 2 ^ 240 % 2 ^ 10 := rfl
  have hb250 : bitrange lv 250 5 = lv / 2 ^ 250 :=
    bitrange_eq_div_of_lt (Nat.div_lt_of_lt_mul (by rw [← pow_add]; exact hlv))
  have hc5 : bitrange rv 5 250 = rv / 2 ^ 5 :=
    bitrange_eq_div_of_lt (Nat.div_lt_of_lt_mul (by rw [← pow_add]; exact hrv))
  simp only [bitrange_zero, hb240, hb250, hc5] at haw hb1w hb2w hbw hcw
  have e5 : (twoPow5 : Fp) = ((2 ^ 5 : ℕ) : Fp) := by norm_num [twoPow5]
  have e10 : (twoPow10 : Fp) = ((2 ^ 10 : ℕ) : Fp) := by norm_num [twoPow10]
  have e240 : (twoPow240 : Fp) = ((2 ^ 240 : ℕ) : Fp) := by
    norm_num [twoPow240]
  have hvalA : ZMod.val ((l + 2 ^ 10 * (lv % 2 ^ 240) : ℕ) : Fp)
      = l + 2 ^ 10 * (lv % 2 ^ 240) :=
    ZMod.val_natCast_of_lt (lt_trans (by omega) two_pow_250_lt_p)
  have hvalB : ZMod.val ((lv / 2 ^ 240 % 2 ^ 10 + 2 ^ 10 * (lv / 2 ^ 250)
        + 2 ^ 15 * (rv % 2 ^ 5) : ℕ) : Fp)
      = lv / 2 ^ 240 % 2 ^ 10 + 2 ^ 10 * (lv / 2 ^ 250) + 2 ^ 15 * (rv % 2 ^ 5) :=
    ZMod.val_natCast_of_lt (lt_trans (by omega) two_pow_250_lt_p)
  have hzA : pieceZ aCell 1 = ((lv % 2 ^ 240 : ℕ) : Fp) := by
    simp only [pieceZ, haw, hvalA]
    congr 1
    rw [show K * 1 = 10 from rfl]
    omega
  have hzB : pieceZ bCell 1
      = ((lv / 2 ^ 250 + 2 ^ 5 * (rv % 2 ^ 5) : ℕ) : Fp) := by
    simp only [pieceZ, hbw, hvalB]
    congr 1
    rw [show K * 1 = 10 from rfl]
    omega
  subst hleft hright
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [haw, hz1A, hzA, e10]
    push_cast
    ring
  · rw [hz1A, hzA, hbw, hz1B, hzB, hb1w, e10, e240]
    have hnat : lv = lv % 2 ^ 240 + 2 ^ 240 * (lv / 2 ^ 240 % 2 ^ 10)
        + 2 ^ 250 * (lv / 2 ^ 250) := by omega
    have hc := congrArg (Nat.cast (R := Fp)) hnat
    push_cast at hc ⊢
    linear_combination hc
  · rw [hb2w, hcw, e5]
    have hnat : rv = rv % 2 ^ 5 + 2 ^ 5 * (rv / 2 ^ 5) := by omega
    have hc := congrArg (Nat.cast (R := Fp)) hnat
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

def main (G : Generators) (Q : Point Fp) (hQ : Q.OnCurve) (l : ℕ)
    (input : Var Input Fp) : Circuit Fp (Expression Fp) := do
  -- witness the three message pieces and the short sub-pieces b_1, b_2
  let a ← witness (l + (2 ^ 10 : ℕ) * input.left.val.bitrange 0 240).toField
  let b1 ← witness (input.left.val.bitrange 250 5).toField
  let b2 ← witness (input.right.val.bitrange 0 5).toField
  let b ← witness (input.left.val.bitrange 240 10
    + (2 ^ 10 : ℕ) * input.left.val.bitrange 250 5
    + (2 ^ 15 : ℕ) * input.right.val.bitrange 0 5).toField
  let c ← witness (input.right.val.bitrange 5 250).toField
  -- constrain b_1 and b_2 to 5 bits
  Utilities.LookupRangeCheck.shortRangeCircuit 5 (by decide) { word := b1 }
  Utilities.LookupRangeCheck.shortRangeCircuit 5 (by decide) { word := b2 }
  -- hash = SinsemillaHashToPoint(Q, a || b || c)
  let out ← HashToPoint.Z1s.circuit G Q hQ 24 [1, 24] #v[a, b, c]
  -- the decomposition gate ties the pieces to (l, left, right)
  Merkle.Gate.circuit {
    aWhole := a, bWhole := b, cWhole := c,
    leftNode := input.left, rightNode := input.right,
    z1A := out.z1s[0], z1B := out.z1s[1],
    b1 := b1, b2 := b2,
    lWhole := Expression.const (l : Fp) }
  return out.point.x

-- Hand-written elaboration data (NOT `elaborate_circuit`): the generated all-in-one
-- instance for this circuit produces a proof term whose kernel check exceeds the
-- default heartbeat budget (the hash subcircuit is large). Splitting the fields, with
-- an explicit `localLength`, keeps each kernel check small.
instance elaborated (G : Generators) (Q : Point Fp) (hQ : Q.OnCurve)
    (l : ℕ) :
    ElaboratedCircuit Fp Input field (main G Q hQ l) where
  localLength _ := 269
  localLength_eq := by
    intro input offset
    have hEL : ∀ x, (HashToPoint.Z1s.circuit G Q hQ 24 [1, 24]).localLength x = 262 := fun _ => rfl
    simp only [main, circuit_norm, hEL, _root_.Orchard.Sinsemilla.Merkle.Gate.circuit,
      Utilities.LookupRangeCheck.shortRangeCircuit]
  channelsLawful := by
    dsimp only [ElaboratedCircuit.ChannelsLawful]
    dsimp only [main]
    have hECg : (HashToPoint.Z1s.circuit G Q hQ 24 [1, 24]).channelsWithGuarantees = [] := rfl
    simp only [circuit_norm, seval, _root_.Orchard.Sinsemilla.Merkle.Gate.circuit,
      Utilities.LookupRangeCheck.shortRangeCircuit, hECg]
    try trivial

def Spec (G : Generators) (Q : Point Fp) (l : ℕ)
    (input : Value Input Fp) (output : Value field Fp)
    (_ : ProverData Fp) : Prop :=
  ∃ lv rv : ℕ, lv < 2 ^ 255 ∧ rv < 2 ^ 255 ∧
    ((lv : ℕ) : Fp) = input.left ∧ ((rv : ℕ) : Fp) = input.right ∧
    ∀ B, Specs.Sinsemilla.hashToPoint G.S Q (merkleChunks l lv rv) = some B →
      output = B.x

def ProverAssumptions (G : Generators) (Q : Point Fp) (l : ℕ)
    (input : ProverValue Input Fp) (_ : ProverData Fp)
    (_ : ProverHint Fp) : Prop :=
  ∃ B, Specs.Sinsemilla.hashToPoint G.S Q
    (merkleChunks l (ZMod.val (show Fp from input.left))
      (ZMod.val (show Fp from input.right))) = some B

def ProverSpec (G : Generators) (Q : Point Fp) (l : ℕ)
    (input : ProverValue Input Fp) (output : ProverValue field Fp)
    (_ : ProverHint Fp) : Prop :=
  ∀ B, Specs.Sinsemilla.hashToPoint G.S Q
      (merkleChunks l (ZMod.val (show Fp from input.left))
        (ZMod.val (show Fp from input.right))) = some B →
    output = B.x

theorem soundness (G : Generators) (Q : Point Fp) (hQ : Q.OnCurve)
    (l : ℕ) (hl : l < 2 ^ 10) :
    GeneralFormalCircuit.WithHint.Soundness Fp (main G Q hQ l)
      (fun _ _ => True) (Spec G Q l) := by
  circuit_proof_start [HashToPoint.Z1s.circuit, HashToPoint.Z1s.Spec,
    Merkle.Gate.circuit, Merkle.Gate.Spec, Merkle.Gate.a0, Merkle.Gate.b0,
    Utilities.LookupRangeCheck.shortRangeCircuit,
    Utilities.LookupRangeCheck.shortRangeSpec,
    Chain.PieceChunks]
  obtain ⟨h_b1, h_b2, ⟨chunks, hPC, hZ1, hfun⟩, hg1, hg2, hg3, hg4⟩ := h_holds
  obtain ⟨b1n, hb1n, hb1⟩ : ∃ b1n, b1n < 2 ^ 5 ∧ env.get (i₀ + 1) = ((b1n : ℕ) : Fp) :=
    ⟨_, h_b1, (ZMod.natCast_zmod_val _).symm⟩
  obtain ⟨b2n, hb2n, hb2⟩ : ∃ b2n, b2n < 2 ^ 5 ∧ env.get (i₀ + 1 + 1) = ((b2n : ℕ) : Fp) :=
    ⟨_, h_b2, (ZMod.natCast_zmod_val _).symm⟩
  obtain ⟨msA, hmsA, haval, t1, rfl, msB, hmsB, hbval, t2, rfl,
    msC, hmsC, hcval, t3, rfl, rfl⟩ := hPC
  have hz1A := Chain.z1Facts_getElem_zero hZ1
  have hz1B := Chain.z1Facts_getElem_one hZ1
  have heoex : ∃ e, HashToPoint.Z1s.output G Q 24 [1, 24]
      #v[Expression.var ⟨i₀⟩, Expression.var ⟨i₀ + 1 + 1 + 1⟩,
        Expression.var ⟨i₀ + 1 + 1 + 1 + 1⟩]
      (i₀ + 1 + 1 + 1 + 1 + 1 + 1 + 1) = e := ⟨_, rfl⟩
  obtain ⟨eo, heo⟩ := heoex
  simp only [heo] at hz1A hz1B hfun hg1 hg2 hg3 hg4
  simp only [List.append_nil] at hfun hz1A hz1B
  have haval' : env.get i₀
      = ((∑ r ∈ Finset.range 25, msA r * 2 ^ (K * r) : ℕ) : Fp) := haval
  have hbval' : env.get (i₀ + 1 + 1 + 1)
      = ((∑ r ∈ Finset.range 2, msB r * 2 ^ (K * r) : ℕ) : Fp) := hbval
  have hcval' : env.get (i₀ + 1 + 1 + 1 + 1)
      = ((∑ r ∈ Finset.range 25, msC r * 2 ^ (K * r) : ℕ) : Fp) := hcval
  rw [Chain.z1Facts_head_sum] at hz1A
  simp only [Chain.chunks_drop_append, Chain.z1Facts_head_sum] at hz1B
  simp only [Finset.sum_range_one, Nat.mul_zero, pow_zero, Nat.mul_one, Vector.getElem_map]
    at hz1A hz1B
  have hasm := assemble hmsA hmsB hmsC hl hb1n hb2n
    haval' hbval' hcval' hb1 hb2 hz1A hz1B hg1 hg2 hg3 hg4
  obtain ⟨lv, rv, hlv, hrv, hlcast, hrcast, hchunks⟩ := hasm
  refine ⟨lv, rv, hlv, hrv, hlcast, hrcast, ?_⟩
  intro B hB
  rw [hchunks] at hB
  rw [heo]
  exact congrArg Point.x (hfun B hB)

-- Keep the `z₁` projection atomic: unfolding `Chain.z1sOfZs` over the full running-sum
-- `HVec` (50 cells) blows up `whnf` when the honest-value hypotheses are used.
attribute [local irreducible] Chain.z1sOfZs

theorem completeness (G : Generators) (Q : Point Fp) (hQ : Q.OnCurve)
    (l : ℕ) (hl : l < 2 ^ 10) :
    GeneralFormalCircuit.WithHint.Completeness Fp (main G Q hQ l)
      (ProverAssumptions G Q l) (ProverSpec G Q l) := by
  circuit_proof_start [HashToPoint.Z1s.circuit,
    HashToPoint.Z1s.ProverAssumptions, HashToPoint.Z1s.ProverSpec, Merkle.Gate.circuit, Merkle.Gate.Spec,
    Merkle.Gate.a0, Merkle.Gate.b0, Utilities.LookupRangeCheck.shortRangeCircuit,
    Utilities.LookupRangeCheck.shortRangeSpec, Chain.PieceBounds,
    Chain.honestChunks, Chain.Z1sHonest,
    Vector.tail_eq_cast_extract, Vector.extract_mk, List.extract_toArray,
    List.extract_eq_take_drop, List.size_toArray, Vector.cast_rfl,
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
  have hps := (h_entry_env ⟨hp.1, hex⟩).2
  have hBfun := hps.2
  have hzh1 := (Vector.getElem_map (Expression.eval env.toEnvironment)
    (by simp)).symm.trans hps.1.1
  have hzh2 := (Vector.getElem_map (Expression.eval env.toEnvironment)
    (by simp)).symm.trans hps.1.2.1
  have hg := honest_gate (l := l) (lv := ZMod.val input_left)
    (rv := ZMod.val input_right) (aCell := env.get i₀)
    (bCell := env.get (i₀ + 1 + 1 + 1)) (b1Cell := env.get (i₀ + 1))
    (b2Cell := env.get (i₀ + 1 + 1)) (cCell := env.get (i₀ + 1 + 1 + 1 + 1))
    (left := input_left) (right := input_right)
    hl hlv hrv ha_w hb1_w hb2_w hb_w hc_w hzh1 hzh2
    (ZMod.natCast_zmod_val input_left) (ZMod.natCast_zmod_val input_right)
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [hb1_w,
      ZMod.val_natCast_of_lt (lt_trans (bitrange_lt _ 250 5) (by norm_num [PALLAS_BASE_CARD]))]
    exact bitrange_lt _ 250 5
  · rw [hb2_w,
      ZMod.val_natCast_of_lt (lt_trans (bitrange_lt _ 0 5) (by norm_num [PALLAS_BASE_CARD]))]
    exact bitrange_lt _ 0 5
  · exact ⟨hp.1, hex⟩
  · exact hg.1
  · exact hg.2.1
  · exact hg.2.2.1
  · exact hg.2.2.2
  · intro B' hB'
    refine congrArg Point.x (hBfun B' ?_)
    show Specs.Sinsemilla.hashToPoint G.S Q
      (List.map (pieceWord (env.get i₀)) (List.range 25)
        ++ (List.map (pieceWord (env.get (i₀ + 1 + 1 + 1))) (List.range 2)
          ++ List.map (pieceWord (env.get (i₀ + 1 + 1 + 1 + 1))) (List.range 25)))
      = some B'
    rw [hp.2]
    exact hB'

def circuit (G : Generators) (Q : Point Fp) (hQ : Q.OnCurve)
    (l : ℕ) (hl : l < 2 ^ 10) :
    GeneralFormalCircuit.WithHint Fp Input field where
  main := main G Q hQ l
  elaborated := elaborated G Q hQ l
  Spec := Spec G Q l
  ProverAssumptions := ProverAssumptions G Q l
  ProverSpec := ProverSpec G Q l
  soundness := soundness G Q hQ l hl
  completeness := completeness G Q hQ l hl

end HashLayer

def depth : ℕ := 32

def MerkleStep (G : Generators) (Q : Point Fp) (l : ℕ)
    (node node' : Fp) : Prop :=
  ∃ lv rv : ℕ, lv < 2 ^ 255 ∧ rv < 2 ^ 255 ∧
    ((lv : Fp) = node ∨ (rv : Fp) = node) ∧
    ∀ B, Specs.Sinsemilla.hashToPoint G.S Q (merkleChunks l lv rv) = some B →
      node' = B.x

def MerkleRoot (G : Generators) (Q : Point Fp) :
    ℕ → Fp → ℕ → Fp → Prop
  | _, node, 0, root => root = node
  | l, node, k + 1, root =>
    ∃ mid, MerkleStep G Q l node mid ∧ MerkleRoot G Q (l + 1) mid k root

namespace Layer

structure Input (F : Type) where
  node : F
  sibling : Unconstrained field F
  posBit : UnconstrainedBool F
deriving CircuitType

instance : Inhabited (Var Input Fp) :=
  ⟨{ node := default, sibling := unconstrained (do return default),
     posBit := unconstrainedBool (do return .false) }⟩

def main (G : Generators) (Q : Point Fp) (hQ : Q.OnCurve) (l : ℕ) (hl : l < 2 ^ 10)
    (input : Var Input Fp) : Circuit Fp (Var field Fp) := do
  let sw ← Utilities.CondSwap.Swap.circuit
    { a := input.node, b := input.sibling, swap := input.posBit }
  HashLayer.circuit G Q hQ l hl { left := sw.aSwapped, right := sw.bSwapped }

instance elaborated (G : Generators) (Q : Point Fp) (hQ : Q.OnCurve)
    (l : ℕ) (hl : l < 2 ^ 10) :
    ElaboratedCircuit Fp Input field (main G Q hQ l hl) where
  localLength _ := 274
  localLength_eq := by
    intro input offset
    have hHL : ∀ x, (HashLayer.circuit G Q hQ l hl).localLength x = 269 := fun _ => rfl
    simp only [main, circuit_norm, hHL, Utilities.CondSwap.Swap.circuit]
  channelsLawful := by
    dsimp only [ElaboratedCircuit.ChannelsLawful]
    dsimp only [main]
    have hHLg : (HashLayer.circuit G Q hQ l hl).channelsWithGuarantees = [] := rfl
    simp only [circuit_norm, seval, Utilities.CondSwap.Swap.circuit, hHLg]
    try trivial

def Spec (G : Generators) (Q : Point Fp) (l : ℕ)
    (input : Value Input Fp) (output : Value field Fp)
    (_ : ProverData Fp) : Prop :=
  MerkleStep G Q l input.node output

theorem soundness (G : Generators) (Q : Point Fp) (hQ : Q.OnCurve)
    (l : ℕ) (hl : l < 2 ^ 10) :
    GeneralFormalCircuit.WithHint.Soundness Fp (main G Q hQ l hl)
      (fun _ _ => True) (Spec G Q l) := by
  circuit_proof_start [Utilities.CondSwap.Swap.circuit,
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
def proverChunks (l : ℕ) (input : ProverValue Input Fp) : List ℕ :=
  merkleChunks l
    (ZMod.val (show Fp from if input.posBit then input.sibling else input.node))
    (ZMod.val (show Fp from if input.posBit then input.node else input.sibling))

def ProverAssumptions (G : Generators) (Q : Point Fp) (l : ℕ)
    (input : ProverValue Input Fp) (_ : ProverData Fp) (_ : ProverHint Fp) : Prop :=
  ∃ B, Specs.Sinsemilla.hashToPoint G.S Q (proverChunks l input) = some B

def ProverSpec (G : Generators) (Q : Point Fp) (l : ℕ)
    (input : ProverValue Input Fp) (output : ProverValue field Fp)
    (_ : ProverHint Fp) : Prop :=
  ∀ B, Specs.Sinsemilla.hashToPoint G.S Q (proverChunks l input) = some B → output = B.x

theorem completeness (G : Generators) (Q : Point Fp) (hQ : Q.OnCurve)
    (l : ℕ) (hl : l < 2 ^ 10) :
    GeneralFormalCircuit.WithHint.Completeness Fp (main G Q hQ l hl)
      (ProverAssumptions G Q l) (ProverSpec G Q l) := by
  circuit_proof_start [proverChunks,
    Utilities.CondSwap.Swap.circuit, Utilities.CondSwap.Swap.ProverSpec,
    Utilities.CondSwap.Swap.outputValue,
    HashLayer.circuit, HashLayer.ProverAssumptions, HashLayer.ProverSpec]
  -- the swap subcircuit pins its two output cells to the position-selected pair, so the
  -- hash subcircuit's prover assumption is exactly our hypothesis.
  obtain ⟨⟨-, hsw⟩, hHL⟩ := h_env
  injection hsw with h3 h4
  rw [h3, h4] at hHL ⊢
  exact ⟨h_assumptions, (hHL h_assumptions).2⟩

def circuit (G : Generators) (Q : Point Fp) (hQ : Q.OnCurve)
    (l : ℕ) (hl : l < 2 ^ 10) :
    GeneralFormalCircuit.WithHint Fp Input field where
  main := main G Q hQ l hl
  elaborated := elaborated G Q hQ l hl
  Spec := Spec G Q l
  ProverAssumptions := ProverAssumptions G Q l
  ProverSpec := ProverSpec G Q l
  soundness := soundness G Q hQ l hl
  completeness := completeness G Q hQ l hl

end Layer

/-- Forward induction: a chain of `MerkleStep`s assembles into a `MerkleRoot`. -/
private theorem merkleRoot_of_steps (G : Generators) (Q : Point Fp)
    (f : ℕ → Fp) (l : ℕ) :
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
  /-- The 32 position bits, packed into a single natural number (bit `i` = the position
  bit of layer `i`): there is no `Unconstrained*` carrier for a field-independent vector
  hint, only the scalar `UnconstrainedBool`/`UnconstrainedNat` — so the packed-Nat form
  with per-layer `NExpr.testBit` unpacking is the IR-native representation. -/
  path : Unconstrained (fields 32) F
  pos : UnconstrainedNat F
deriving CircuitType

instance : Inhabited (Var Input Fp) :=
  ⟨{ leaf := default, path := unconstrained (do return default),
     pos := unconstrainedNat (do return 0) }⟩

def main (G : Generators) (Q : Point Fp) (hQ : Q.OnCurve)
    (input : Var Input Fp) : Circuit Fp (Var field Fp) :=
  Circuit.foldl (.finRange 32) input.leaf
    (fun node i => Layer.circuit G Q hQ i.val (by omega)
      { node := node,
        sibling := unconstrained (do return (← input.path)[i]),
        posBit := unconstrainedBool (do return (← input.pos).testBit i.val =? 1) })

def output (G : Generators) (Q : Point Fp) (offset : ℕ) :=
  HashToPoint.Z1s.output G Q 24 [1, 24]
    #v[var ⟨offset + 8499⟩, var ⟨offset + 8502⟩, var ⟨offset + 8503⟩]
    (offset + 8506)
  |>.point.x

-- TODO(perf): this instance gives an explicit `localLength` but inherits the default
-- `output`, which is the 32-layer `Circuit.foldl` of `main`. When a parent circuit passes
-- `CalculateRoot.circuit` to `simp`/`circuit_proof_start`, unfolding that foldl-based output
-- on the goal expands into a cast the kernel cannot re-check (a deterministic timeout — see
-- `Clean/Orchard/Action.lean`, where the soundness proof must omit this child from
-- the lemma list as a workaround). Providing an explicit closed-form `output` here (the
-- layer-31 output cell, e.g. `varFromOffset field (31 * 274 + 273)`) would keep the foldl
-- folded and let the plain tactic handle a parent that composes the Merkle path.
instance elaborated (G : Generators) (Q : Point Fp) (hQ : Q.OnCurve) :
    ElaboratedCircuit Fp Input field (main G Q hQ) where
  localLength _ := 32 * 274
  localLength_eq input offset := by
    simp only [main, circuit_norm, Layer.circuit]
  output input offset := output G Q offset
  output_eq input offset := by
    simp only [output, main, circuit_norm, Layer.circuit, Layer.main, HashLayer.circuit, Utilities.CondSwap.Swap.circuit,
      HashLayer.main, HashToPoint.Z1s.circuit, Utilities.LookupRangeCheck.shortRangeCircuit]
  subcircuitsConsistent input offset := by
    simp only [main, circuit_norm, Layer.circuit]
  channelsLawful := by
    simp only [main, circuit_norm, Layer.circuit]

def Spec (G : Generators) (Q : Point Fp)
    (input : Value Input Fp) (output : Value field Fp)
    (_ : ProverData Fp) : Prop :=
  MerkleRoot G Q 0 input.leaf depth output

theorem soundness (G : Generators) (Q : Point Fp) (hQ : Q.OnCurve) :
    GeneralFormalCircuit.WithHint.Soundness Fp (main G Q hQ)
      (fun _ _ => True) (Spec G Q) := by
  circuit_proof_start
  obtain ⟨h0, hstep⟩ := h_holds
  refine ⟨?_, Or.inl rfl, fun i hi => Or.inl rfl⟩
  -- The per-layer output is a pure offset reference: independent of the layer index,
  -- the input record, and the well-formedness proof. So we canonicalize the running
  -- node to a single offset-indexed form. The bridging equalities below all hold by
  -- `rfl` (the kernel reduces the output lazily, ignoring the discarded fields), which
  -- is far cheaper than a `simp` traversal over the large fold expressions.
  have hpf : (0 : ℕ) < 2 ^ 10 := by norm_num
  have hlen : ∀ (l : ℕ) (hl : l < 2 ^ 10) (inp : Var Layer.Input Fp),
      (Layer.circuit G Q hQ l hl).localLength inp = 274 := fun _ _ _ => rfl
  -- `bridge` is the key kernel-cheap rewrite. The per-layer output is a pure offset
  -- reference, so as a *value* it is independent of layer index, input record and
  -- well-formedness proof; `bridge` says so, with an offset-equality hypothesis folded
  -- in. It is proved by `rfl` over *opaque* arguments — the kernel checks that body once
  -- and every *application* is mere type instantiation, so no concrete fold output is
  -- ever reduced (which is what blew the budget). Offset gaps are discharged purely at
  -- the `ℕ` level via `hlen`, again touching no output subterm.
  have bridge : ∀ (l : ℕ) (hl : l < 2 ^ 10) (inp : Var Layer.Input Fp) (o₁ o₂ : ℕ),
      o₁ = o₂ →
      Expression.eval env ((Layer.circuit G Q hQ l hl).output inp o₁)
        = Expression.eval env ((Layer.circuit G Q hQ 0 hpf).output default o₂) := by
    intro l hl inp o₁ o₂ h; subst h; rfl
  -- state function: f 0 = leaf, f (j+1) = canonical output value at offset i₀ + j*274
  let f : ℕ → Fp := fun n => match n with
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
  simp only [circuit_norm, output, f, Layer.circuit, Layer.main, HashLayer.circuit, Utilities.CondSwap.Swap.circuit,
    HashLayer.main, HashToPoint.Z1s.circuit, Utilities.LookupRangeCheck.shortRangeCircuit]

/-- The honest running node after `k` layers (`none` if any layer hash is undefined).
Index-based to mirror the circuit's `Circuit.foldl`. -/
def honestNode (G : Generators) (Q : Point Fp)
    (input : ProverValue Input Fp) : ℕ → Option Fp
  | 0 => some (show Fp from input.leaf)
  | k + 1 =>
    if hk : k < 32 then
      (honestNode G Q input k).bind fun node =>
        (Specs.Sinsemilla.hashToPoint G.S Q
          (Layer.proverChunks k
            { node := node,
              sibling := (show Vector Fp 32 from input.path)[k]'(by omega),
              posBit := decide ((show ℕ from input.pos) >>> k % 2 = 1) })).map (·.x)
    else none

def ProverAssumptions (G : Generators) (Q : Point Fp)
    (input : ProverValue Input Fp) (_ : ProverData Fp) (_ : ProverHint Fp) : Prop :=
  (honestNode G Q input 32).isSome

def ProverSpec (G : Generators) (Q : Point Fp)
    (input : ProverValue Input Fp) (output : ProverValue field Fp)
    (_ : ProverHint Fp) : Prop :=
  ∀ root, honestNode G Q input 32 = some root → (show Fp from output) = root

/-- `honestNode` is downward-monotone in success: if it succeeds after `k+1` layers, it
already succeeds after `k`. -/
theorem honestNode_isSome_of_succ (G : Generators) (Q : Point Fp)
    (input : ProverValue Input Fp) (k : ℕ)
    (h : (honestNode G Q input (k + 1)).isSome) : (honestNode G Q input k).isSome := by
  rw [honestNode] at h
  split at h
  · rcases hb : honestNode G Q input k with _ | v
    · rw [hb] at h; simp at h
    · simp
  · simp at h

theorem honestNode_isSome_le (G : Generators) (Q : Point Fp)
    (input : ProverValue Input Fp) {i j : ℕ} (hij : i ≤ j)
    (h : (honestNode G Q input j).isSome) : (honestNode G Q input i).isSome := by
  induction j with
  | zero => rw [Nat.le_zero.mp hij]; exact h
  | succ m ih =>
    rcases Nat.lt_or_ge i (m + 1) with hlt | hge
    · exact ih (by omega) (honestNode_isSome_of_succ G Q input m h)
    · have : i = m + 1 := by omega
      rwa [this]

theorem completeness (G : Generators) (Q : Point Fp) (hQ : Q.OnCurve) :
    GeneralFormalCircuit.WithHint.Completeness Fp (main G Q hQ)
      (ProverAssumptions G Q) (ProverSpec G Q) := by
  circuit_proof_start [Layer.circuit,
    Layer.ProverAssumptions, Layer.ProverSpec, Layer.proverChunks]
  obtain ⟨hL0, hLstep⟩ := h_env
  have hpf : (0 : ℕ) < 2 ^ 10 := by norm_num
  have hlen : ∀ (l : ℕ) (hl : l < 2 ^ 10) (inp : Var Layer.Input Fp),
      (Layer.circuit G Q hQ l hl).localLength inp = 274 := fun _ _ _ => rfl
  -- output-value canonicalization (see soundness `bridge`): independent of layer / input
  -- record / proof, with the offset gap folded into a ℕ equation.
  have bridge : ∀ (l : ℕ) (hl : l < 2 ^ 10) (inp : Var Layer.Input Fp) (o₁ o₂ : ℕ),
      o₁ = o₂ →
      Expression.eval env.toEnvironment (Layer.main G Q hQ l hl inp o₁).1
        = Expression.eval env.toEnvironment (Layer.main G Q hQ 0 hpf default o₂).1 := by
    intro l hl inp o₁ o₂ h; subst h; rfl
  -- the canonical running node after `n` layers
  let acc : ℕ → Fp := fun n => match n with
    | 0 => input_leaf
    | k + 1 => Expression.eval env.toEnvironment
        (Layer.main G Q hQ 0 hpf default (i₀ + k * 274)).1
  set I : ProverValue Input Fp := { leaf := input_leaf, path := input_path, pos := input_pos }
    with hI
  -- the chunk list hashed at layer `k` with running node `acc k`
  have key : ∀ k, k ≤ 32 → honestNode G Q I k = some (acc k) := by
    intro k
    induction k with
    | zero => intro _; rfl
    | succ k ih =>
      intro hk
      have hk' : k < 32 := by omega
      have hik : honestNode G Q I k = some (acc k) := ih (by omega)
      -- honestNode (k+1) reduces to the layer-k hash, mapped to its x-coordinate
      have hred : honestNode G Q I (k + 1) = (Specs.Sinsemilla.hashToPoint G.S Q
          (Layer.proverChunks k
            { node := acc k, sibling := (show Vector Fp 32 from I.path)[k]'hk',
              posBit := decide ((show ℕ from I.pos) >>> k % 2 = 1) })).map (·.x) := by
        rw [honestNode, dif_pos hk', hik]; rfl
      have hsome : (honestNode G Q I (k + 1)).isSome :=
        honestNode_isSome_le G Q I (by omega) h_assumptions
      rw [hred] at hsome ⊢
      -- the layer-k hash exists
      set chunks : List ℕ := Layer.proverChunks k
        { node := acc k, sibling := (show Vector Fp 32 from I.path)[k]'hk',
          posBit := decide ((show ℕ from I.pos) >>> k % 2 = 1) } with hchunks
      obtain ⟨B, hB⟩ : ∃ B, Specs.Sinsemilla.hashToPoint G.S Q chunks = some B := by
        rcases h : Specs.Sinsemilla.hashToPoint G.S Q chunks with _ | B
        · rw [h] at hsome; simp at hsome
        · exact ⟨B, rfl⟩
      rw [hB]
      show some B.x = some (acc (k + 1))
      congr 1
      -- align `hB` with the propositional condition spelling of `hL0`/`hLstep`
      -- (their `decide _ = true` conditions are `circuit_norm`-normalized)
      rw [hchunks] at hB
      simp only [Layer.proverChunks, hI, decide_eq_true_eq] at hB
      -- now show `B.x = acc (k+1)` via the per-layer prover spec
      rcases k with _ | j
      · -- layer 0: feed `hL0` the existence we just produced
        have spec := (hL0 ⟨B, hB⟩).2 B hB
        rw [← spec]
        exact bridge 0 (by norm_num) _ _ _ (by simp)
      · -- layer j+1: the running node equals the canonical `acc (j+1)` (bridge)
        have hbe : Expression.eval env.toEnvironment
            (Layer.main G Q hQ j (by omega)
              { node := default,
                sibling := fun s => ((input_var.path s).1[j], (input_var.path s).2),
                posBit := fun s => ((input_var.pos s).1.testBit (Witgen.NExpr.const j) =? 1,
                  (input_var.pos s).2) } (i₀ + j * 274)).1 = acc (j + 1) :=
          bridge j (by omega) _ _ _ rfl
        have spec := (hLstep j hk' ⟨B, by rw [hbe]; exact hB⟩).2 B (by rw [hbe]; exact hB)
        rw [← spec]
        exact bridge (j + 1) (by omega) _ _ _ rfl
  -- each layer's hash exists (the running node is the honest one, via `key`)
  have hAsm : ∀ k (hk : k < 32), ∃ B, Specs.Sinsemilla.hashToPoint G.S Q
      (Layer.proverChunks k
        { node := acc k, sibling := (show Vector Fp 32 from I.path)[k]'hk,
          posBit := decide ((show ℕ from I.pos) >>> k % 2 = 1) }) = some B := by
    intro k hk
    have h1 : (Specs.Sinsemilla.hashToPoint G.S Q (Layer.proverChunks k
        { node := acc k, sibling := (show Vector Fp 32 from I.path)[k]'hk,
          posBit := decide ((show ℕ from I.pos) >>> k % 2 = 1) })).map (·.x) = some (acc (k + 1)) := by
      have hk1 := key (k + 1) (by omega)
      rw [honestNode, dif_pos hk, key k (by omega)] at hk1
      exact hk1
    rcases hh : Specs.Sinsemilla.hashToPoint G.S Q (Layer.proverChunks k
        { node := acc k, sibling := (show Vector Fp 32 from I.path)[k]'hk,
          posBit := decide ((show ℕ from I.pos) >>> k % 2 = 1) }) with _ | B
    · rw [hh] at h1; simp at h1
    · exact ⟨B, rfl⟩
  -- align with the propositional condition spelling of the goals
  simp only [Layer.proverChunks, hI, decide_eq_true_eq] at hAsm
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · -- layer-0 assumption
    exact hAsm 0 (by norm_num)
  · -- layer-(i+1) assumptions
    intro i hi
    have hbe : Expression.eval env.toEnvironment
        (Layer.main G Q hQ i (by omega)
          { node := default,
            sibling := fun s => ((input_var.path s).1[i], (input_var.path s).2),
            posBit := fun s => ((input_var.pos s).1.testBit (Witgen.NExpr.const i) =? 1,
              (input_var.pos s).2) } (i₀ + i * 274)).1 = acc (i + 1) :=
      bridge i (by omega) _ _ _ rfl
    rw [hbe]
    exact hAsm (i + 1) (by omega)
  · -- the output is the honest root
    intro root hroot
    rw [key 32 (le_refl 32)] at hroot
    obtain rfl : acc 32 = root := Option.some.inj hroot
    simp only [acc, output, circuit_norm, Layer.main, HashLayer.circuit, Utilities.CondSwap.Swap.circuit,
      HashLayer.main, HashToPoint.Z1s.circuit, Utilities.LookupRangeCheck.shortRangeCircuit]

def circuit (G : Generators) (Q : Point Fp) (hQ : Q.OnCurve) :
    GeneralFormalCircuit.WithHint Fp Input field where
  main := main G Q hQ
  elaborated := elaborated G Q hQ
  Spec := Spec G Q
  ProverAssumptions := ProverAssumptions G Q
  ProverSpec := ProverSpec G Q
  soundness := soundness G Q hQ
  completeness := completeness G Q hQ
end CalculateRoot

end Orchard.Sinsemilla.Merkle
