import Clean.Circuit
import Clean.Utils.Bits
import Clean.Circomlib.Bitify

namespace Circomlib
open Utils.Bits
variable {p : ℕ} [Fact p.Prime] [Fact (p < 2^254)] [Fact (p > 2^253)]

namespace CompConstant

/-! ## Helper Definitions -/

/-- The b coefficient for iteration i: b_i = 2^128 - 2^i -/
@[reducible] def bCoeff (i : ℕ) : ℤ := 2^128 - 2^i

/-- The a coefficient for iteration i: a_i = 2^i -/
@[reducible] def aCoeff (i : ℕ) : ℤ := 2^i

/-- Compute the part value for iteration i -/
def computePart (i : ℕ) (slsb smsb : F p) (ct : ℕ) : F p :=
  let clsb := (ct >>> (i * 2)) &&& 1
  let cmsb := (ct >>> (i * 2 + 1)) &&& 1
  let b_val : F p := (bCoeff i : F p)
  let a_val : F p := (aCoeff i : F p)
  if cmsb == 0 && clsb == 0 then
    -b_val * smsb * slsb + b_val * smsb + b_val * slsb
  else if cmsb == 0 && clsb == 1 then
    a_val * smsb * slsb - a_val * slsb + b_val * smsb - a_val * smsb + a_val
  else if cmsb == 1 && clsb == 0 then
    b_val * smsb * slsb - a_val * smsb + a_val
  else
    -a_val * smsb * slsb + a_val

/-- Semantic value of a signal pair (2-bit number: msb * 2 + lsb) -/
def signalPairValF (slsb smsb : F p) : ℕ := smsb.val * 2 + slsb.val

/-- Semantic value of constant pair at position i -/
def constPairValAt (i : ℕ) (ct : ℕ) : ℕ :=
  ((ct >>> (i * 2 + 1)) &&& 1) * 2 + ((ct >>> (i * 2)) &&& 1)

/-! ### Helper lemmas for coefficients -/

omit [Fact (p < 2 ^ 254)] [Fact p.Prime] in
/-- The aCoeff value is in range for field operations -/
lemma aCoeff_lt_p (i : ℕ) (_hi : i < 127) : 2^i < p := by
  have h1 : 2^i < 2^127 := Nat.pow_lt_pow_right (by omega) _hi
  have h2 : 2^127 < 2^253 := by native_decide
  linarith [‹Fact (p > 2^253)›.elim]

omit [Fact (p < 2 ^ 254)] [Fact p.Prime] in
/-- The bCoeff value is in range for field operations -/
lemma bCoeff_lt_p (i : ℕ) : 2^128 - 2^i < p := by
  have h1 : 2^128 - 2^i < 2^128 := by
    have : 2^i ≥ 1 := Nat.one_le_two_pow
    omega
  have h2 : 2^128 < 2^253 := by native_decide
  linarith [‹Fact (p > 2^253)›.elim]

omit [Fact (p < 2 ^ 254)] in
/-- The field value of aCoeff equals its natural number value -/
lemma aCoeff_val (i : ℕ) (hi : i < 127) : (aCoeff i : F p).val = 2^i := by
  have hp_gt_1 : 1 < p := Nat.Prime.one_lt ‹Fact (Nat.Prime p)›.elim
  have h_a_bound : 2^i < p := aCoeff_lt_p i hi
  simp only [aCoeff, Int.cast_pow, Int.cast_ofNat]
  have h_pow_cast : (2 : F p)^i = ((2^i : ℕ) : F p) := by simp only [Nat.cast_pow]; rfl
  rw [h_pow_cast, ZMod.val_natCast_of_lt h_a_bound]

omit [Fact (p < 2 ^ 254)] in
/-- The field value of bCoeff equals its natural number value -/
lemma bCoeff_val (i : ℕ) (hi : i < 127) : (bCoeff i : F p).val = 2^128 - 2^i := by
  have h_b_bound : 2^128 - 2^i < p := bCoeff_lt_p i
  have h_2i_lt_128 : 2^i < 2^128 := Nat.pow_lt_pow_right (by omega) (by omega : i < 128)
  simp only [bCoeff]
  have h_eq : ((2 : ℤ)^128 - 2^i : ℤ) = ((2^128 - 2^i : ℕ) : ℤ) := by
    rw [Int.ofNat_sub (le_of_lt h_2i_lt_128)]
    simp only [Nat.cast_pow, Nat.cast_ofNat]
  rw [h_eq, Int.cast_natCast, ZMod.val_natCast_of_lt h_b_bound]

omit [Fact (p < 2 ^ 254)] [Fact (p > 2 ^ 253)] [Fact p.Prime] in
/-- Bit extraction with &&& 1 is either 0 or 1 -/
lemma bit_and_one_cases (n : ℕ) : n &&& 1 = 0 ∨ n &&& 1 = 1 := by
  have h : n &&& 1 ≤ 1 := Nat.and_le_right
  exact (Nat.le_one_iff_eq_zero_or_eq_one).mp h

/-! ### Helper lemmas for bit manipulation -/

omit [Fact (p < 2 ^ 254)] [Fact (p > 2 ^ 253)] [Fact p.Prime] in
/-- Low bit extraction from pair: n % 4 % 2 = n % 2 -/
lemma mod4_mod2_eq_mod2 (n : ℕ) : n % 4 % 2 = n % 2 := by omega

omit [Fact (p < 2 ^ 254)] [Fact (p > 2 ^ 253)] [Fact p.Prime] in
/-- High bit extraction from pair: n % 4 / 2 = n / 2 % 2 -/
lemma mod4_div2_eq_div2_mod2 (n : ℕ) : n % 4 / 2 = n / 2 % 2 := by omega

omit [Fact (p < 2 ^ 254)] [Fact (p > 2 ^ 253)] [Fact p.Prime] in
/-- Power identity for odd positions: 2^(k*2 + 1) = 2^(k*2) * 2 -/
lemma pow_double_succ (k : ℕ) : 2 ^ (k * 2 + 1) = 2 ^ (k * 2) * 2 := by ring

omit [Fact (p < 2 ^ 254)] in
/-- Key characterization: computePart encodes pair comparison. -/
lemma computePart_characterization (i : ℕ) (hi : i < 127) (slsb smsb : F p)
    (h_slsb : slsb = 0 ∨ slsb = 1) (h_smsb : smsb = 0 ∨ smsb = 1) (ct : ℕ) :
    let s_pair := signalPairValF slsb smsb
    let c_pair := constPairValAt i ct
    (computePart i slsb smsb ct).val =
      if s_pair > c_pair then 2^128 - 2^i
      else if s_pair = c_pair then 0
      else 2^i := by
  have hp_gt_1 : 1 < p := Nat.Prime.one_lt ‹Fact (Nat.Prime p)›.elim
  have h_val_0 : (0 : F p).val = 0 := ZMod.val_zero
  have h_val_1 : (1 : F p).val = 1 := @ZMod.val_one p ⟨hp_gt_1⟩
  have h_aCoeff_val : (aCoeff i : F p).val = 2^i := aCoeff_val i hi
  have h_bCoeff_val : (bCoeff i : F p).val = 2^128 - 2^i := bCoeff_val i hi
  have h_cm_cases := bit_and_one_cases (ct >>> (i * 2 + 1))
  have h_cl_cases := bit_and_one_cases (ct >>> (i * 2))

  simp only [signalPairValF, constPairValAt, computePart]
  rcases h_smsb with rfl | rfl <;> rcases h_slsb with rfl | rfl <;>
  rcases h_cm_cases with h_cm | h_cm <;> rcases h_cl_cases with h_cl | h_cl <;>
  simp only [h_val_0, h_val_1, h_cm, h_cl, mul_zero, zero_mul, add_zero, zero_add,
             mul_one, one_mul, beq_self_eq_true, Bool.and_self, Bool.and_true, Bool.true_and,
             ↓reduceIte, Nat.one_ne_zero, beq_iff_eq, sub_zero, sub_self,
             h_aCoeff_val, h_bCoeff_val, Nat.zero_ne_one] <;>
  (simp (config := {decide := true}) only [↓reduceIte]) <;>
  (simp only [show (-↑(bCoeff i) + ↑(bCoeff i) + ↑(bCoeff i) : F p) = ↑(bCoeff i) by ring,
              show (↑(bCoeff i) - ↑(aCoeff i) + ↑(aCoeff i) : F p) = ↑(bCoeff i) by ring,
              show (0 - ↑(aCoeff i) + ↑(aCoeff i) : F p) = 0 by ring,
              show (-↑(aCoeff i) + ↑(aCoeff i) : F p) = 0 by ring,
              h_aCoeff_val, h_bCoeff_val, ZMod.val_zero])

/-! ### Helper lemmas for sum_range_precise -/

lemma sum_pow_two_fin (k : ℕ) :
    (Finset.univ : Finset (Fin k)).sum (fun i => 2^i.val) = 2^k - 1 := by
  induction k with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.coe_castSucc, Fin.val_last]
    rw [ih]
    ring_nf
    omega

lemma contributions_below_k_bound (k : ℕ) (contributions : Fin k → ℕ)
    (h_bound : ∀ i, contributions i ≤ 2^128) :
    (Finset.univ : Finset (Fin k)).sum contributions < k * 2^128 + 1 := by
  calc (Finset.univ : Finset (Fin k)).sum contributions
      ≤ (Finset.univ : Finset (Fin k)).sum (fun _ => 2^128) := by
          apply Finset.sum_le_sum; intro i _; exact h_bound i
    _ = k * 2^128 := by simp [Finset.sum_const, smul_eq_mul]
    _ < k * 2^128 + 1 := by omega

/-- Signal pair value at position i (extracted from Vector) -/
def signalPairAt (i : ℕ) (hi : i < 127) (input : Vector (F p) 254) : ℕ :=
  have hi2 : i * 2 < 254 := by omega
  have hi21 : i * 2 + 1 < 254 := by omega
  input[i * 2 + 1].val * 2 + input[i * 2].val

omit [Fact (Nat.Prime p)] [Fact (p < 2 ^ 254)] [Fact (p > 2 ^ 253)] in
lemma signalPairAt_eq_signalPairValF (i : ℕ) (hi : i < 127) (input : Vector (F p) 254) :
    signalPairAt i hi input = signalPairValF input[i * 2] input[i * 2 + 1] := by
  unfold signalPairAt signalPairValF
  rfl

omit [Fact (p < 2 ^ 254)] [Fact (p > 2 ^ 253)] in
lemma signalPairAt_le_3 (i : ℕ) (hi : i < 127) (input : Vector (F p) 254)
    (h_bits : ∀ j (_ : j < 254), input[j] = 0 ∨ input[j] = 1) :
    signalPairAt i hi input ≤ 3 := by
  unfold signalPairAt
  have hi2 : i * 2 < 254 := by omega
  have hi21 : i * 2 + 1 < 254 := by omega
  have hp_gt_1 : 1 < p := Nat.Prime.one_lt ‹Fact (Nat.Prime p)›.elim
  have h_slsb := h_bits (i * 2) hi2
  have h_smsb := h_bits (i * 2 + 1) hi21
  rcases h_slsb with h0_l | h1_l <;> rcases h_smsb with h0_m | h1_m
  · simp only [h0_l, h0_m, ZMod.val_zero]; omega
  · simp only [h0_l, h1_m, ZMod.val_zero, @ZMod.val_one p ⟨hp_gt_1⟩]; omega
  · simp only [h1_l, h0_m, ZMod.val_zero, @ZMod.val_one p ⟨hp_gt_1⟩]; omega
  · simp only [h1_l, h1_m, @ZMod.val_one p ⟨hp_gt_1⟩]; omega

/-- Helper: relates (x >>> k) % 4 to bits at positions k and k+1. -/
lemma shiftRight_mod4_eq_bits (x k : ℕ) :
    (x >>> k) % 4 = (x / 2^k % 2) + 2 * (x / 2^(k+1) % 2) := by
  simp only [Nat.shiftRight_eq_div_pow]
  have h : x / 2^k % 4 = x / 2^k % 2 + 2 * (x / 2^k / 2 % 2) := by omega
  have h2 : x / 2^k / 2 = x / 2^(k+1) := by
    rw [Nat.pow_succ, Nat.div_div_eq_div_mul, mul_comm]
  omega

/-- Extract bit value from toBits_fromBits: bits[k] equals the k-th bit of fromBits bits -/
lemma fromBits_testBit_eq {n : ℕ} (bits : Vector ℕ n) (k : ℕ)
    (h_bits : ∀ (i : ℕ) (hi : i < n), bits[i] = 0 ∨ bits[i] = 1)
    (hk : k < n) :
    bits[k] = (fromBits bits) / 2^k % 2 := by
  have h_tb := toBits_fromBits bits h_bits
  have h_eq : (toBits n (fromBits bits))[k] = bits[k] := by rw [h_tb]
  simp only [toBits, Vector.getElem_mapRange] at h_eq
  simp only [Nat.testBit, Nat.shiftRight_eq_div_pow] at h_eq
  rw [Nat.and_comm, Nat.and_one_is_mod] at h_eq
  have h_mod2 : fromBits bits / 2 ^ k % 2 = 0 ∨ fromBits bits / 2 ^ k % 2 = 1 := Nat.mod_two_eq_zero_or_one _
  rcases h_bits k hk with hb | hb <;> rcases h_mod2 with hm | hm <;> simp_all

/-- Helper: for a fromBits result, the shift-mod4 equals the pair of bits. -/
lemma fromBits_shiftRight_mod4 {n : ℕ} (bits : Vector ℕ n) (k : ℕ)
    (h_bits : ∀ (i : ℕ) (hi : i < n), bits[i] = 0 ∨ bits[i] = 1)
    (hk : k + 1 < n) :
    (fromBits bits >>> k) % 4 = bits[k] + 2 * bits[k + 1] := by
  rw [shiftRight_mod4_eq_bits]
  rw [fromBits_testBit_eq bits k h_bits (Nat.lt_of_succ_lt hk)]
  rw [fromBits_testBit_eq bits (k+1) h_bits hk]

/-- Helper: 4^k = 2^(2*k) -/
lemma four_pow_eq_two_pow_double (k : ℕ) : (4:ℕ)^k = 2^(2*k) := by
  calc (4:ℕ)^k = (2^2)^k := by norm_num
    _ = 2^(2*k) := by rw [← Nat.pow_mul]

/-- Helper lemma: If x and y agree on all pairs above position k, then their high parts are equal. -/
lemma high_parts_eq_of_pairs_eq_above (x y k : ℕ)
    (h_above : ∀ j : Fin 127, j.val > k → (x >>> (j.val * 2)) % 4 = (y >>> (j.val * 2)) % 4)
    (hx : x < 2^254) (hy : y < 2^254) :
    x / 4^(k + 1) = y / 4^(k + 1) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit, Nat.shiftRight_eq_div_pow]
  rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul]
  have h4pow : (4 : ℕ)^(k+1) = 2^(2*(k+1)) := four_pow_eq_two_pow_double (k+1)
  rw [h4pow]
  rw [Nat.and_comm, Nat.and_one_is_mod, Nat.and_comm, Nat.and_one_is_mod]
  let bit_pos := 2*(k+1) + i
  by_cases hbound : bit_pos < 254
  · let h_pair_pos := bit_pos / 2
    have h_pair_bound : h_pair_pos ≥ k + 1 := by omega
    by_cases h_pair_lt_127 : h_pair_pos < 127
    · have h_pair_eq := h_above ⟨h_pair_pos, h_pair_lt_127⟩ (by omega : h_pair_pos > k)
      simp only [Nat.shiftRight_eq_div_pow] at h_pair_eq
      by_cases h_even : bit_pos % 2 = 0
      · have hpow_eq : 2^(2*(k+1)) * 2^i = 2^bit_pos := by rw [← Nat.pow_add]
        rw [hpow_eq]
        have h_bp_eq : bit_pos = h_pair_pos * 2 := by omega
        rw [h_bp_eq]
        have h_low : x / 2^(h_pair_pos * 2) % 2 = y / 2^(h_pair_pos * 2) % 2 := by
          calc x / 2^(h_pair_pos * 2) % 2 = (x / 2^(h_pair_pos * 2) % 4) % 2 := by rw [mod4_mod2_eq_mod2]
            _ = (y / 2^(h_pair_pos * 2) % 4) % 2 := by rw [h_pair_eq]
            _ = y / 2^(h_pair_pos * 2) % 2 := by rw [mod4_mod2_eq_mod2]
        simp only [h_low]
      · have hpow_eq : 2^(2*(k+1)) * 2^i = 2^bit_pos := by rw [← Nat.pow_add]
        rw [hpow_eq]
        have h_bp_eq : bit_pos = h_pair_pos * 2 + 1 := by omega
        rw [h_bp_eq]
        have hpow := pow_double_succ h_pair_pos
        have h_high : x / 2 ^ (h_pair_pos * 2 + 1) % 2 = y / 2 ^ (h_pair_pos * 2 + 1) % 2 := by
          calc x / 2 ^ (h_pair_pos * 2 + 1) % 2 = x / (2 ^ (h_pair_pos * 2) * 2) % 2 := by rw [hpow]
            _ = x / 2 ^ (h_pair_pos * 2) / 2 % 2 := by rw [Nat.div_div_eq_div_mul]
            _ = x / 2 ^ (h_pair_pos * 2) % 4 / 2 := by rw [mod4_div2_eq_div2_mod2]
            _ = y / 2 ^ (h_pair_pos * 2) % 4 / 2 := by rw [h_pair_eq]
            _ = y / 2 ^ (h_pair_pos * 2) / 2 % 2 := by rw [mod4_div2_eq_div2_mod2]
            _ = y / (2 ^ (h_pair_pos * 2) * 2) % 2 := by rw [Nat.div_div_eq_div_mul]
            _ = y / 2 ^ (h_pair_pos * 2 + 1) % 2 := by rw [hpow]
        simp only [h_high]
    · have hpow_eq : 2^(2*(k+1)) * 2^i = 2^bit_pos := by rw [← Nat.pow_add]
      rw [hpow_eq]
      have h_bp_ge_254 : bit_pos ≥ 254 := by omega
      omega
  · have hpow_eq : 2^(2*(k+1)) * 2^i = 2^bit_pos := by rw [← Nat.pow_add]
    rw [hpow_eq]
    have h_pos : 0 < 2^bit_pos := Nat.pow_pos (by omega : 0 < 2)
    have hx_div : x / 2^bit_pos = 0 := by
      apply Nat.div_eq_zero_iff.mpr
      right
      calc x < 2^254 := hx
        _ ≤ 2^bit_pos := Nat.pow_le_pow_right (by omega) (by omega)
    have hy_div : y / 2^bit_pos = 0 := by
      apply Nat.div_eq_zero_iff.mpr
      right
      calc y < 2^254 := hy
        _ ≤ 2^bit_pos := Nat.pow_le_pow_right (by omega) (by omega)
    rw [hx_div, hy_div]

/-- Helper: x % (4 * 4^k) = (x / 4^k % 4) * 4^k + x % 4^k -/
lemma mod_four_pow_succ (x k : ℕ) : x % 4^(k+1) = (x / 4^k % 4) * 4^k + x % 4^k := by
  have h41 : (4:ℕ)^(k+1) = 4 * 4^k := by ring
  rw [h41]
  have h_4k_pos : 0 < 4^k := Nat.pow_pos (by omega : 0 < 4)
  have h_rem : x % 4^k < 4^k := Nat.mod_lt x h_4k_pos
  have h_qmod : x / 4^k % 4 < 4 := Nat.mod_lt _ (by omega : 0 < 4)
  have h_sum_lt : x / 4^k % 4 * 4^k + x % 4^k < 4 * 4^k := by nlinarith
  have h1 : x / 4^k = x / 4^k / 4 * 4 + x / 4^k % 4 := by
    have := Nat.div_add_mod (x / 4^k) 4; linarith
  have h2 : x = x / 4^k / 4 * (4 * 4^k) + (x / 4^k % 4 * 4^k + x % 4^k) := by
    have h_base := Nat.div_add_mod x (4^k)
    have h_step1 : x = 4^k * (x / 4^k) + x % 4^k := by linarith
    have h_step2 : 4^k * (x / 4^k) = x / 4^k / 4 * (4 * 4^k) + x / 4^k % 4 * 4^k := by
      calc 4^k * (x / 4^k) = 4^k * (x / 4^k / 4 * 4 + x / 4^k % 4) := by
             conv_lhs => rw [h1]
        _ = x / 4^k / 4 * 4 * 4^k + x / 4^k % 4 * 4^k := by ring
        _ = x / 4^k / 4 * (4 * 4^k) + x / 4^k % 4 * 4^k := by ring
    linarith
  have h3 : x / 4^k / 4 = x / (4 * 4^k) := by
    rw [Nat.div_div_eq_div_mul]; ring_nf
  rw [h3] at h2
  have h_div_mod := Nat.div_add_mod x (4 * 4^k)
  have h_quot : x / (4 * 4^k) * (4 * 4^k) = (4 * 4^k) * (x / (4 * 4^k)) := by ring
  rw [h_quot] at h2
  omega

/-- Key comparison lemma: if high parts are equal and x's pair at k is less than y's pair,
    then x < y. -/
lemma lt_of_high_eq_and_pair_lt (x y k : ℕ)
    (h_high_eq : x / 4^(k + 1) = y / 4^(k + 1))
    (h_pair_lt : (x >>> (k * 2)) % 4 < (y >>> (k * 2)) % 4) :
    x < y := by
  simp only [Nat.shiftRight_eq_div_pow] at h_pair_lt
  have h4k : (4:ℕ)^k = 2^(k*2) := by rw [four_pow_eq_two_pow_double]; ring_nf
  have h_pair_lt' : x / 4^k % 4 < y / 4^k % 4 := by rw [h4k]; exact h_pair_lt

  have h_x_low := mod_four_pow_succ x k
  have h_y_low := mod_four_pow_succ y k

  have h_rem_x : x % 4^k < 4^k := Nat.mod_lt x (Nat.pow_pos (by omega : 0 < 4))
  have h_rem_y : y % 4^k < 4^k := Nat.mod_lt y (Nat.pow_pos (by omega : 0 < 4))
  have h_4k_pos : 0 < 4^k := Nat.pow_pos (by omega : 0 < 4)

  have h_mod_lt : x % 4^(k+1) < y % 4^(k+1) := by
    rw [h_x_low, h_y_low]
    have h_xp_lt_yp : x / 4^k % 4 + 1 ≤ y / 4^k % 4 := h_pair_lt'
    calc (x / 4^k % 4) * 4^k + x % 4^k
      < (x / 4^k % 4) * 4^k + 4^k := by omega
      _ = (x / 4^k % 4 + 1) * 4^k := by ring
      _ ≤ (y / 4^k % 4) * 4^k := Nat.mul_le_mul_right _ h_xp_lt_yp
      _ ≤ (y / 4^k % 4) * 4^k + y % 4^k := Nat.le_add_right _ _

  have h_4k1_pos : 0 < 4^(k+1) := Nat.pow_pos (by omega : 0 < 4)
  have hx_eq : x = x / 4^(k+1) * 4^(k+1) + x % 4^(k+1) := by
    have h := Nat.div_add_mod x (4^(k+1))
    linarith
  have hy_eq : y = y / 4^(k+1) * 4^(k+1) + y % 4^(k+1) := by
    have h := Nat.div_add_mod y (4^(k+1))
    linarith
  rw [hx_eq, hy_eq, h_high_eq]
  omega

/-- If all 2-bit pairs are equal, then the numbers are equal (for numbers < 2^254). -/
lemma eq_of_all_pairs_eq (x y : ℕ) (hx : x < 2^254) (hy : y < 2^254)
    (h_all_eq : ∀ i : Fin 127, (x >>> (i.val * 2)) % 4 = (y >>> (i.val * 2)) % 4) :
    x = y := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi_bound : i < 254
  · let k : Fin 127 := ⟨i / 2, by omega⟩
    have h_pair_eq := h_all_eq k
    simp only [Nat.testBit, Nat.shiftRight_eq_div_pow]
    rw [Nat.and_comm, Nat.and_one_is_mod, Nat.and_comm, Nat.and_one_is_mod]
    by_cases h_even : i % 2 = 0
    · have h_i_eq : i = k.val * 2 := by
        have hk_def : k.val = i / 2 := rfl
        omega
      rw [h_i_eq]
      simp only [Nat.shiftRight_eq_div_pow] at h_pair_eq
      have h_low : x / 2 ^ (k.val * 2) % 2 = y / 2 ^ (k.val * 2) % 2 := by
        calc x / 2 ^ (k.val * 2) % 2 = x / 2 ^ (k.val * 2) % 4 % 2 := by rw [mod4_mod2_eq_mod2]
          _ = y / 2 ^ (k.val * 2) % 4 % 2 := by rw [h_pair_eq]
          _ = y / 2 ^ (k.val * 2) % 2 := by rw [mod4_mod2_eq_mod2]
      simp only [h_low]
    · have h_i_eq : i = k.val * 2 + 1 := by
        have hk_def : k.val = i / 2 := rfl
        omega
      rw [h_i_eq]
      simp only [Nat.shiftRight_eq_div_pow] at h_pair_eq
      have hpow := pow_double_succ k.val
      have h_high : x / 2 ^ (k.val * 2 + 1) % 2 = y / 2 ^ (k.val * 2 + 1) % 2 := by
        calc x / 2 ^ (k.val * 2 + 1) % 2 = x / (2 ^ (k.val * 2) * 2) % 2 := by rw [hpow]
          _ = x / 2 ^ (k.val * 2) / 2 % 2 := by rw [Nat.div_div_eq_div_mul]
          _ = x / 2 ^ (k.val * 2) % 4 / 2 := by rw [mod4_div2_eq_div2_mod2]
          _ = y / 2 ^ (k.val * 2) % 4 / 2 := by rw [h_pair_eq]
          _ = y / 2 ^ (k.val * 2) / 2 % 2 := by rw [mod4_div2_eq_div2_mod2]
          _ = y / (2 ^ (k.val * 2) * 2) % 2 := by rw [Nat.div_div_eq_div_mul]
          _ = y / 2 ^ (k.val * 2 + 1) % 2 := by rw [hpow]
      simp only [h_high]
  · have hx_high : x.testBit i = false := by
      apply Nat.testBit_eq_false_of_lt
      calc x < 2^254 := hx
        _ ≤ 2^i := Nat.pow_le_pow_right (by omega) (by omega)
    have hy_high : y.testBit i = false := by
      apply Nat.testBit_eq_false_of_lt
      calc y < 2^254 := hy
        _ ≤ 2^i := Nat.pow_le_pow_right (by omega) (by omega)
    rw [hx_high, hy_high]

/-- Key lemma: fromBits comparison implies existence of differing pair. -/
lemma exists_msb_win_from_gt (x y : ℕ) (hx : x < 2^254) (hy : y < 2^254) (h_gt : x > y) :
    ∃ k : Fin 127,
      (x >>> (k.val * 2)) % 4 > (y >>> (k.val * 2)) % 4 ∧
      ∀ j : Fin 127, j > k → (x >>> (j.val * 2)) % 4 = (y >>> (j.val * 2)) % 4 := by
  let diff_positions := { i : Fin 127 | (x >>> (i.val * 2)) % 4 ≠ (y >>> (i.val * 2)) % 4 }
  let diff_finset := diff_positions.toFinset

  have h_nonempty : diff_finset.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h_empty
    have h_all_eq : ∀ i : Fin 127, (x >>> (i.val * 2)) % 4 = (y >>> (i.val * 2)) % 4 := by
      intro i
      by_contra h_ne
      have : i ∈ diff_finset := by simp [diff_finset, diff_positions, h_ne]
      rw [h_empty] at this
      exact Finset.notMem_empty _ this
    have h_x_eq_y : x = y := eq_of_all_pairs_eq x y hx hy h_all_eq
    omega

  let k := diff_finset.max' h_nonempty

  have hk_mem : (x >>> (k.val * 2)) % 4 ≠ (y >>> (k.val * 2)) % 4 := by
    have : k ∈ diff_finset := Finset.max'_mem diff_finset h_nonempty
    simp only [diff_finset, diff_positions, Set.mem_toFinset, Set.mem_setOf_eq] at this
    exact this

  have h_above_eq : ∀ j : Fin 127, j > k → (x >>> (j.val * 2)) % 4 = (y >>> (j.val * 2)) % 4 := by
    intro j hj
    by_contra h_ne
    have hj_mem : j ∈ diff_finset := by
      simp only [diff_finset, diff_positions, Set.mem_toFinset, Set.mem_setOf_eq]
      exact h_ne
    have h_le := Finset.le_max' diff_finset j hj_mem
    have h_lt := lt_of_lt_of_le hj h_le
    exact (lt_irrefl _ h_lt)

  by_cases h_pair_gt : (x >>> (k.val * 2)) % 4 > (y >>> (k.val * 2)) % 4
  · exact ⟨k, h_pair_gt, h_above_eq⟩
  · have h_pair_lt : (x >>> (k.val * 2)) % 4 < (y >>> (k.val * 2)) % 4 := by
      have h_ne := hk_mem
      omega
    have h_high_eq := high_parts_eq_of_pairs_eq_above x y k.val h_above_eq hx hy
    have h_lt := lt_of_high_eq_and_pair_lt x y k.val h_high_eq h_pair_lt
    omega

/-- Helper: x % 4 gives pair value at position 0. -/
lemma shift_mod4_eq_pair (x : ℕ) : x % 4 = (x >>> 0) % 4 := by
  simp

/-- Helper: const pair value equals shift/mod4. -/
lemma constPairAt_eq_shift_mod4 (ct i : ℕ) :
    constPairValAt i ct = (ct >>> (i * 2)) % 4 := by
  unfold constPairValAt
  have h1 : (ct >>> (i * 2)) % 4 = (ct / 2^(i*2)) % 4 := by simp [Nat.shiftRight_eq_div_pow]
  have h2 : (ct >>> (i * 2 + 1)) &&& 1 = (ct / 2^(i*2+1)) % 2 := by
    simp [Nat.shiftRight_eq_div_pow, Nat.and_comm]
  have h3 : (ct >>> (i * 2)) &&& 1 = (ct / 2^(i*2)) % 2 := by
    simp [Nat.shiftRight_eq_div_pow, Nat.and_comm]
  have h4 : (ct / 2^(i*2)) % 4 = (ct / 2^(i*2)) % 2 + 2 * (ct / 2^(i*2+1) % 2) := by
    have := shiftRight_mod4_eq_bits ct (i*2)
    simp [Nat.shiftRight_eq_div_pow] at this
    exact this
  omega

omit [Fact (p < 2 ^ 254)] [Fact (p > 2 ^ 253)] in
/-- Helper: signal pair value equals fromBits shift/mod4. -/
lemma signalPairAt_eq_fromBits_pair (i : ℕ) (input : Vector (F p) 254)
    (h_bits : ∀ j (_ : j < 254), input[j] = 0 ∨ input[j] = 1)
    (hi : i < 127) :
    signalPairAt i hi input = (fromBits (input.map ZMod.val) >>> (i * 2)) % 4 := by
  have hk : i * 2 + 1 < 254 := by omega
  have hk' : i * 2 < 254 := by omega
  have h_bits' : ∀ (j : ℕ) (hj : j < 254), (input.map ZMod.val)[j] = 0 ∨ (input.map ZMod.val)[j] = 1 := by
    intro j hj
    have h := h_bits j hj
    rcases h with h0 | h1
    · left; simpa [Vector.getElem_map, ZMod.val_zero] using congrArg ZMod.val h0
    · right
      have hp_gt_1 : 1 < p := Nat.Prime.one_lt ‹Fact (Nat.Prime p)›.elim
      have h1' := congrArg ZMod.val h1
      simpa [Vector.getElem_map, @ZMod.val_one p ⟨hp_gt_1⟩] using h1'
  have h_mod4 := fromBits_shiftRight_mod4 (bits := input.map ZMod.val) (k := i*2) h_bits' (by omega)
  simp only [Vector.getElem_map] at h_mod4
  unfold signalPairAt
  simpa [Nat.mul_comm, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h_mod4.symm

omit [Fact (p < 2 ^ 254)] [Fact (p > 2 ^ 253)] in
lemma exists_msb_win_position (ct : ℕ) (h_ct : ct < 2^254)
    (input : Vector (F p) 254)
    (h_bits : ∀ i (_ : i < 254), input[i] = 0 ∨ input[i] = 1)
    (h_gt : fromBits (input.map ZMod.val) > ct) :
    ∃ k : Fin 127,
      signalPairValF input[k.val * 2] input[k.val * 2 + 1] > constPairValAt k.val ct ∧
      ∀ j : Fin 127, j > k →
        signalPairValF input[j.val * 2] input[j.val * 2 + 1] = constPairValAt j.val ct := by
  have hx : fromBits (input.map ZMod.val) < 2^254 := by
    exact (toBits_fromBits_aux (input.map ZMod.val) (by
      intro i hi
      have h := h_bits i hi
      rcases h with h0 | h1
      · left; simpa [Vector.getElem_map, ZMod.val_zero] using congrArg ZMod.val h0
      · right
        have hp_gt_1 : 1 < p := Nat.Prime.one_lt ‹Fact (Nat.Prime p)›.elim
        have h1' := congrArg ZMod.val h1
        simpa [Vector.getElem_map, @ZMod.val_one p ⟨hp_gt_1⟩] using h1')).1
  have hy : ct < 2^254 := h_ct
  obtain ⟨k, h_win, h_above⟩ := exists_msb_win_from_gt (fromBits (input.map ZMod.val)) ct hx hy h_gt
  refine ⟨k, ?_, ?_⟩
  · have h_sig : signalPairValF input[k.val * 2] input[k.val * 2 + 1] =
      (fromBits (input.map ZMod.val) >>> (k.val * 2)) % 4 := by
      have h1 := (signalPairAt_eq_signalPairValF k.val k.isLt input).symm
      have h2 := signalPairAt_eq_fromBits_pair k.val input h_bits k.isLt
      simpa [h1] using h2
    have h_const : constPairValAt k.val ct = (ct >>> (k.val * 2)) % 4 :=
      constPairAt_eq_shift_mod4 ct k.val
    simpa [h_sig, h_const] using h_win
  · intro j hj
    have h_sig : signalPairValF input[j.val * 2] input[j.val * 2 + 1] =
      (fromBits (input.map ZMod.val) >>> (j.val * 2)) % 4 := by
      have h1 := (signalPairAt_eq_signalPairValF j.val j.isLt input).symm
      have h2 := signalPairAt_eq_fromBits_pair j.val input h_bits j.isLt
      simpa [h1] using h2
    have h_const : constPairValAt j.val ct = (ct >>> (j.val * 2)) % 4 :=
      constPairAt_eq_shift_mod4 ct j.val
    have h_ab := h_above j hj
    simpa [h_sig, h_const] using h_ab

omit [Fact (p < 2 ^ 254)] [Fact (p > 2 ^ 253)] in
/-- When input ≤ ct, either all pairs are ties, or the MSB differing position is a loss. -/
lemma msb_determines_le (ct : ℕ) (h_ct : ct < 2^254)
    (input : Vector (F p) 254)
    (h_bits : ∀ i (_ : i < 254), input[i] = 0 ∨ input[i] = 1)
    (h_le : fromBits (input.map ZMod.val) ≤ ct) :
    (∀ i : Fin 127, signalPairValF input[i.val * 2] input[i.val * 2 + 1] = constPairValAt i.val ct) ∨
    (∃ k : Fin 127,
      signalPairValF input[k.val * 2] input[k.val * 2 + 1] < constPairValAt k.val ct ∧
      ∀ j : Fin 127, j > k →
        signalPairValF input[j.val * 2] input[j.val * 2 + 1] = constPairValAt j.val ct) := by
  let x := fromBits (input.map ZMod.val)
  have hx_lt : x < 2^254 := by
    apply fromBits_lt
    intro i hi
    simp only [Vector.getElem_map]
    have hp_gt_1 : 1 < p := Nat.Prime.one_lt ‹Fact (Nat.Prime p)›.elim
    rcases h_bits i hi with h0 | h1
    · left; simp only [ZMod.val_eq_zero]; exact h0
    · right
      apply_fun ZMod.val at h1
      simp only [@ZMod.val_one p ⟨hp_gt_1⟩] at h1
      exact h1

  have h_signal_pair : ∀ i : Fin 127,
      signalPairValF input[i.val * 2] input[i.val * 2 + 1] = (x >>> (i.val * 2)) % 4 := by
    intro i
    unfold signalPairValF
    let bits := input.map ZMod.val
    have h_bits_01 : ∀ (j : ℕ) (hj : j < 254), bits[j] = 0 ∨ bits[j] = 1 := by
      intro j hj
      simp only [Vector.getElem_map, bits]
      have hp_gt_1 : 1 < p := Nat.Prime.one_lt ‹Fact (Nat.Prime p)›.elim
      rcases h_bits j hj with h0 | h1
      · left; simp only [ZMod.val_eq_zero]; exact h0
      · right
        apply_fun ZMod.val at h1
        simp only [@ZMod.val_one p ⟨hp_gt_1⟩] at h1
        exact h1
    have hi_bound : i.val * 2 + 1 < 254 := by omega
    have h_fb := fromBits_shiftRight_mod4 bits (i.val * 2) h_bits_01 hi_bound
    simp only [Vector.getElem_map, bits] at h_fb
    have h_idx : i.val * 2 + 1 = 1 + i.val * 2 := by omega
    simp only [h_idx] at h_fb ⊢
    rw [h_fb]
    ac_rfl

  have h_const_pair : ∀ i : Fin 127, constPairValAt i.val ct = (ct >>> (i.val * 2)) % 4 := by
    intro i
    unfold constPairValAt
    have h1 : (ct >>> (i.val * 2 + 1)) &&& 1 = (ct >>> (i.val * 2)) / 2 % 2 := by
      simp only [Nat.shiftRight_add, Nat.shiftRight_one, Nat.and_one_is_mod]
    have h2 : (ct >>> (i.val * 2)) &&& 1 = (ct >>> (i.val * 2)) % 2 := by
      simp only [Nat.and_one_is_mod]
    rw [h1, h2]
    omega

  rcases Nat.lt_or_eq_of_le h_le with h_lt | h_eq
  · right
    obtain ⟨k, hk_gt, hk_eq⟩ := exists_msb_win_from_gt ct x h_ct hx_lt h_lt
    use k
    constructor
    · rw [h_signal_pair k, h_const_pair k]
      exact hk_gt
    · intro j hj
      rw [h_signal_pair j, h_const_pair j]
      exact (hk_eq j hj).symm
  · left
    intro i
    rw [h_signal_pair i, h_const_pair i]
    have hx_eq_ct : x = ct := h_eq
    rw [hx_eq_ct]

omit [Fact (p < 2 ^ 254)] in
lemma computePart_val_bound' (i : ℕ) (hi : i < 127) (slsb smsb : F p)
    (h_slsb : slsb = 0 ∨ slsb = 1) (h_smsb : smsb = 0 ∨ smsb = 1) (ct : ℕ) :
    (computePart i slsb smsb ct).val ≤ 2^128 := by
  have h_char := computePart_characterization i hi slsb smsb h_slsb h_smsb ct
  by_cases h_gt : signalPairValF slsb smsb > constPairValAt i ct
  · have h_val : (computePart i slsb smsb ct).val = 2^128 - 2^i := by
      simpa [h_gt] using h_char
    exact h_val ▸ Nat.sub_le _ _
  · by_cases h_eq : signalPairValF slsb smsb = constPairValAt i ct
    · have h_val : (computePart i slsb smsb ct).val = 0 := by
        simpa [h_gt, h_eq] using h_char
      exact h_val ▸ (by omega : 0 ≤ 2^128)
    · have h_val : (computePart i slsb smsb ct).val = 2^i := by
        simpa [h_gt, h_eq] using h_char
      have h2 : 2^i ≤ 2^128 := by
        have h' : i < 128 := by omega
        exact Nat.pow_le_pow_right (by omega) (le_of_lt h')
      exact h_val ▸ h2

omit [Fact (p < 2 ^ 254)] in
lemma computePart_val_bound (i : ℕ) (hi : i < 127) (slsb smsb : F p)
    (h_slsb : slsb = 0 ∨ slsb = 1) (h_smsb : smsb = 0 ∨ smsb = 1) (ct : ℕ) :
    (computePart i slsb smsb ct).val ≤ 2^128 :=
  computePart_val_bound' i hi slsb smsb h_slsb h_smsb ct

omit [Fact (Nat.Prime p)] [Fact (p < 2 ^ 254)] [Fact (p > 2 ^ 253)] in
lemma list_sum_val_bound {l : List (F p)} {bound : ℕ}
    (h : ∀ x ∈ l, x.val ≤ bound) :
    (l.map ZMod.val).sum ≤ l.length * bound := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have h_x : x.val ≤ bound := h x (List.Mem.head xs)
    have h_xs : ∀ y ∈ xs, y.val ≤ bound := fun y hy => h y (List.Mem.tail x hy)
    have := ih h_xs
    linarith

lemma vector_sum_eq_list_sum' {α} [AddCommMonoid α] {n : ℕ} (v : Vector α n) :
    v.sum = v.toList.sum := by
  rw [Vector.sum_mk, ← Array.sum_eq_sum_toList]
  rfl

omit [Fact (p < 2 ^ 254)] [Fact (p > 2 ^ 253)] in
/-- Helper: Expression.eval distributes over List.sum. -/
lemma list_sum_map_eval (env : Environment (F p)) (l : List (Expression (F p))) :
    (l.map (Expression.eval env)).sum = Expression.eval env l.sum := by
  induction l with
  | nil => simp only [List.map_nil, List.sum_nil, circuit_norm]
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [ih]
    simp only [circuit_norm]

omit [Fact (p < 2 ^ 254)] [Fact (p > 2 ^ 253)] in
/-- Helper: Expression.eval distributes over Vector.sum. -/
lemma vector_sum_map_eval (env : Environment (F p)) (n : ℕ) (i₀ : ℕ) :
    (Vector.map (Expression.eval env) (Vector.mapRange n fun i => var { index := i₀ + i })).sum =
    Expression.eval env (Vector.mapRange n fun i => var { index := i₀ + i }).sum := by
  simp only [Vector.sum, Vector.toArray_map]
  conv_lhs => rw [← Array.sum_eq_sum_toList, Array.toList_map]
  conv_rhs => rw [← Array.sum_eq_sum_toList]
  exact list_sum_map_eval env _

omit [Fact (p < 2 ^ 254)] [Fact (p > 2 ^ 253)] in
lemma list_sum_val_eq {l : List (F p)} (h : (l.map ZMod.val).sum < p) :
    l.sum.val = (l.map ZMod.val).sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons] at h ⊢
    have h_xs : (xs.map ZMod.val).sum < p := by
      have : x.val < p := ZMod.val_lt x
      linarith
    have ih' := ih h_xs
    rw [ZMod.val_add, ih']
    rw [Nat.mod_eq_of_lt h]

omit [Fact (p < 2 ^ 254)] [Fact (p > 2 ^ 253)] in
lemma list_sum_val_eq' {l : List (F p)} (h : (l.map ZMod.val).sum < p) :
    l.sum.val = (l.map ZMod.val).sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons] at h ⊢
    have h_xs : (xs.map ZMod.val).sum < p := by
      have : x.val < p := ZMod.val_lt x
      linarith
    have ih' := ih h_xs
    rw [ZMod.val_add, ih']
    rw [Nat.mod_eq_of_lt h]

omit [Fact (Nat.Prime p)] [Fact (p < 2 ^ 254)] [Fact (p > 2 ^ 253)] in
lemma list_sum_val_bound' {l : List (F p)} {bound : ℕ}
    (h : ∀ x ∈ l, x.val ≤ bound) :
    (l.map ZMod.val).sum ≤ l.length * bound := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have h_x : x.val ≤ bound := h x (List.Mem.head xs)
    have h_xs : ∀ y ∈ xs, y.val ≤ bound := fun y hy => h y (List.Mem.tail x hy)
    have := ih h_xs
    linarith

omit [Fact (p < 2 ^ 254)] in
/-- Helper: All parts are bounded by 2^128 -/
lemma parts_val_bounded (input : Vector (F p) 254)
    (h_bits : ∀ i (_ : i < 254), input[i] = 0 ∨ input[i] = 1)
    (parts : Vector (F p) 127) (ct : ℕ)
    (h_parts : ∀ i : Fin 127, parts[i] = computePart i.val input[i.val * 2] input[i.val * 2 + 1] ct) :
    ∀ i : Fin 127, parts[i].val ≤ 2^128 := by
  intro i
  rw [h_parts i]
  exact computePart_val_bound' i.val i.isLt _ _
    (h_bits (i.val * 2) (by omega)) (h_bits (i.val * 2 + 1) (by omega)) ct

omit [Fact (p < 2 ^ 254)] [Fact p.Prime] in
/-- Helper: Sum of parts is less than p -/
lemma parts_sum_lt_p (parts : Vector (F p) 127)
    (h_parts_bounded : ∀ i : Fin 127, parts[i].val ≤ 2^128) :
    (parts.toList.map ZMod.val).sum < p := by
  have hp : p > 2^253 := ‹Fact (p > 2^253)›.elim
  calc (parts.toList.map ZMod.val).sum
      ≤ parts.toList.length * 2^128 := list_sum_val_bound' (by
          intro x hx
          rw [List.mem_iff_getElem] at hx
          obtain ⟨i, hi, rfl⟩ := hx
          simp only [Vector.getElem_toList]
          rw [Vector.length_toList] at hi
          exact h_parts_bounded ⟨i, hi⟩)
    _ = 127 * 2^128 := by simp [Vector.length_toList]
    _ < p := by linarith

omit [Fact (p < 2 ^ 254)] in
/-- Helper: computePart value when signal pair wins -/
lemma computePart_val_when_win (i : Fin 127) (input : Vector (F p) 254) (ct : ℕ)
    (h_bits : ∀ j (_ : j < 254), input[j] = 0 ∨ input[j] = 1)
    (h_win : signalPairValF input[i.val * 2] input[i.val * 2 + 1] > constPairValAt i.val ct) :
    (computePart i.val input[i.val * 2] input[i.val * 2 + 1] ct).val = 2^128 - 2^i.val := by
  have := computePart_characterization i.val i.isLt input[i.val * 2] input[i.val * 2 + 1]
    (h_bits (i.val * 2) (by omega)) (h_bits (i.val * 2 + 1) (by omega)) ct
  simp only [signalPairValF] at this h_win
  simp only [this, h_win, ↓reduceIte]

omit [Fact (p < 2 ^ 254)] in
/-- Helper: computePart value when signal pair ties -/
lemma computePart_val_when_tie (i : Fin 127) (input : Vector (F p) 254) (ct : ℕ)
    (h_bits : ∀ j (_ : j < 254), input[j] = 0 ∨ input[j] = 1)
    (h_tie : signalPairValF input[i.val * 2] input[i.val * 2 + 1] = constPairValAt i.val ct) :
    (computePart i.val input[i.val * 2] input[i.val * 2 + 1] ct).val = 0 := by
  have := computePart_characterization i.val i.isLt input[i.val * 2] input[i.val * 2 + 1]
    (h_bits (i.val * 2) (by omega)) (h_bits (i.val * 2 + 1) (by omega)) ct
  simp only [signalPairValF] at this h_tie
  simp only [this, h_tie, lt_irrefl, ↓reduceIte]

omit [Fact (p < 2 ^ 254)] in
/-- Helper: computePart value when signal pair loses -/
lemma computePart_val_when_lose (i : Fin 127) (input : Vector (F p) 254) (ct : ℕ)
    (h_bits : ∀ j (_ : j < 254), input[j] = 0 ∨ input[j] = 1)
    (h_lose : signalPairValF input[i.val * 2] input[i.val * 2 + 1] < constPairValAt i.val ct) :
    (computePart i.val input[i.val * 2] input[i.val * 2 + 1] ct).val = 2^i.val := by
  have := computePart_characterization i.val i.isLt input[i.val * 2] input[i.val * 2 + 1]
    (h_bits (i.val * 2) (by omega)) (h_bits (i.val * 2 + 1) (by omega)) ct
  simp only [signalPairValF] at this h_lose
  have h_not_gt : ¬(input[i.val * 2 + 1].val * 2 + input[i.val * 2].val > constPairValAt i.val ct) := by omega
  have h_not_eq : ¬(input[i.val * 2 + 1].val * 2 + input[i.val * 2].val = constPairValAt i.val ct) := by omega
  simp only [this, h_not_gt, h_not_eq, ↓reduceIte]

set_option maxHeartbeats 400000 in
omit [Fact (p < 2 ^ 254)] in
lemma sum_range_precise (ct : ℕ) (h_ct : ct < 2^254)
    (input : Vector (F p) 254)
    (h_bits : ∀ i (_ : i < 254), input[i] = 0 ∨ input[i] = 1)
    (parts : Vector (F p) 127)
    (h_parts : ∀ i : Fin 127,
      parts[i] = computePart i.val input[i.val * 2] input[i.val * 2 + 1] ct) :
    let sum := parts.sum
    let input_val := fromBits (input.map ZMod.val)
    (input_val > ct → sum.val / 2^127 % 2 = 1) ∧
    (input_val ≤ ct → sum.val / 2^127 % 2 = 0) := by
  constructor

  -- Case 1: input > ct → sum.val / 2^127 is odd
  · intro h_gt
    obtain ⟨k, h_win_k, h_tie_above⟩ := exists_msb_win_position ct h_ct input h_bits h_gt
    have h_parts_bounded := parts_val_bounded input h_bits parts ct h_parts
    have h_sum_lt_p := parts_sum_lt_p parts h_parts_bounded

    let wins := Finset.filter (fun i : Fin 127 =>
      signalPairValF input[i.val * 2] input[i.val * 2 + 1] > constPairValAt i.val ct) Finset.univ
    let losses := Finset.filter (fun i : Fin 127 =>
      signalPairValF input[i.val * 2] input[i.val * 2 + 1] < constPairValAt i.val ct) Finset.univ

    have hk_in_wins : k ∈ wins := by
      simp only [wins, Finset.mem_filter, Finset.mem_univ, true_and, signalPairValF]
      exact h_win_k

    have h_losses_lt_k : ∀ j ∈ losses, j < k := by
      intro j hj
      by_contra h_ge_k
      push_neg at h_ge_k
      rcases h_ge_k.lt_or_eq with h_gt_k | h_eq_k
      · have h_tie := h_tie_above j h_gt_k
        simp only [losses, Finset.mem_filter, Finset.mem_univ, true_and, signalPairValF] at hj
        simp only [signalPairValF] at h_tie
        omega
      · subst h_eq_k
        simp only [losses, Finset.mem_filter, Finset.mem_univ, true_and, signalPairValF] at hj h_win_k
        omega

    let W := wins.sum (fun i => 2^i.val)
    let Λ := losses.sum (fun i => 2^i.val)

    have hW_ge : W ≥ 2^k.val := by
      show 2^k.val ≤ W
      exact Finset.single_le_sum (f := fun i : Fin 127 => 2^i.val)
        (fun _ _ => Nat.zero_le _) hk_in_wins
    have hΛ_lt : Λ < 2^k.val := by
      have h_losses_subset : losses ⊆ Finset.filter (fun i : Fin 127 => i.val < k.val) Finset.univ := by
        intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact h_losses_lt_k j hj
      have h1 : Λ ≤ (Finset.filter (fun i : Fin 127 => i.val < k.val) Finset.univ).sum (fun i => 2^i.val) :=
        Finset.sum_le_sum_of_subset h_losses_subset
      have h2 : (Finset.filter (fun i : Fin 127 => i.val < k.val) Finset.univ).sum (fun i : Fin 127 => 2^i.val)
              ≤ 2^k.val - 1 := by
        have h_sum_eq : (Finset.filter (fun i : Fin 127 => i.val < k.val) Finset.univ).sum (fun i : Fin 127 => 2^i.val)
            = (Finset.univ : Finset (Fin k.val)).sum (fun i => 2^i.val) := by
          symm
          apply Finset.sum_bij (fun (i : Fin k.val) _ => (⟨i.val, Nat.lt_trans i.isLt k.isLt⟩ : Fin 127))
          · intro i _; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact i.isLt
          · intro _ _ _ _ h; simp only [Fin.mk.injEq] at h; exact Fin.ext h
          · intro j hj
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
            exact ⟨⟨j.val, hj⟩, Finset.mem_univ _, rfl⟩
          · intro _ _; rfl
        rw [h_sum_eq, sum_pow_two_fin]
      have h3 : 2^k.val - 1 < 2^k.val := Nat.sub_one_lt (Nat.two_pow_pos k.val).ne'
      exact Nat.lt_of_le_of_lt (Nat.le_trans h1 h2) h3
    have hW_gt_Λ : W > Λ := Nat.lt_of_lt_of_le hΛ_lt hW_ge
    have hW_bound : W ≤ 2^127 - 1 := by
      show W ≤ 2^127 - 1
      calc W ≤ (Finset.univ : Finset (Fin 127)).sum (fun i => 2^i.val) :=
              Finset.sum_le_sum_of_subset (fun _ _ => Finset.mem_univ _)
        _ = 2^127 - 1 := sum_pow_two_fin 127
    have hW_sub_Λ_bound : W - Λ < 2^127 := Nat.lt_of_le_of_lt (Nat.sub_le W Λ) (Nat.lt_of_le_of_lt hW_bound (by native_decide))
    have hW_sub_Λ_pos : W - Λ > 0 := Nat.sub_pos_of_lt hW_gt_Λ

    have h_wins_nonempty : wins.Nonempty := ⟨k, hk_in_wins⟩
    have h_wins_card_pos : 0 < wins.card := Finset.card_pos.mpr h_wins_nonempty

    have h_sum_partition : (parts.toList.map ZMod.val).sum =
        wins.card * 2^128 - W + Λ := by
      have h_sum_eq : (parts.toList.map ZMod.val).sum =
          (Finset.univ : Finset (Fin 127)).sum (fun i => parts[i].val) := by
        trans (List.ofFn (fun i : Fin 127 => parts[i].val)).sum
        · congr 1
          apply List.ext_getElem
          · rw [List.length_map, Vector.length_toList, List.length_ofFn]
          · intro i h1 h2
            rw [List.length_map, Vector.length_toList] at h1
            simp only [List.getElem_map, Vector.getElem_toList, List.getElem_ofFn]
            rfl
        · simp only [List.sum_ofFn]
      rw [h_sum_eq]

      let ties := Finset.filter (fun i : Fin 127 =>
        signalPairValF input[i.val * 2] input[i.val * 2 + 1] = constPairValAt i.val ct) Finset.univ

      have h_disjoint_wl : Disjoint wins losses := by
        simp only [wins, losses, Finset.disjoint_filter]; intro i _ h1 h2; omega
      have h_disjoint_wt : Disjoint wins ties := by
        simp only [wins, ties, Finset.disjoint_filter]; intro i _ h1 h2; omega
      have h_disjoint_lt : Disjoint losses ties := by
        simp only [losses, ties, Finset.disjoint_filter]; intro i _ h1 h2; omega

      have h_union : wins ∪ losses ∪ ties = Finset.univ := by
        ext i; simp only [Finset.mem_union, wins, losses, ties, Finset.mem_filter,
                          Finset.mem_univ, true_and, iff_true]; omega

      have h_ties_zero : ties.sum (fun i => parts[i].val) = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        simp only [ties, Finset.mem_filter, Finset.mem_univ, true_and] at hi
        rw [h_parts i]
        exact computePart_val_when_tie i input ct h_bits hi

      have h_wins_val : wins.sum (fun i => parts[i].val) = wins.card * 2^128 - W := by
        have h_eq : wins.sum (fun i => parts[i].val) = wins.sum (fun i => 2^128 - 2^i.val) := by
          apply Finset.sum_congr rfl
          intro i hi
          simp only [wins, Finset.mem_filter, Finset.mem_univ, true_and] at hi
          rw [h_parts i]
          exact computePart_val_when_win i input ct h_bits hi
        rw [h_eq]
        have h_sum_sub : ∀ (t : Finset (Fin 127)),
            t.sum (fun i => 2^128 - 2^i.val) = t.card * 2^128 - t.sum (fun i => 2^i.val) := by
          intro t
          induction t using Finset.induction with
          | empty => simp
          | @insert a s ha ih =>
            have h_a_ge : 2^a.val ≤ 2^128 :=
              Nat.pow_le_pow_right (by omega) (Nat.le_of_lt (Nat.lt_trans a.isLt (by omega : 127 < 128)))
            have h_s_ge : ∀ i ∈ s, 2^i.val ≤ 2^128 := fun i _ =>
              Nat.pow_le_pow_right (by omega) (Nat.le_of_lt (Nat.lt_trans i.isLt (by omega : 127 < 128)))
            simp only [Finset.sum_insert ha, Finset.card_insert_of_notMem ha]
            rw [ih]
            have h_sum_le : s.sum (fun i => 2^i.val) ≤ s.card * 2^128 := by
              calc s.sum (fun i => 2^i.val)
                  ≤ s.sum (fun _ => 2^128) := Finset.sum_le_sum (fun i hi => h_s_ge i hi)
                _ = s.card * 2^128 := by simp [Finset.sum_const, smul_eq_mul]
            omega
        rw [h_sum_sub wins]

      have h_losses_val : losses.sum (fun i => parts[i].val) = Λ := by
        simp only [Λ]
        apply Finset.sum_congr rfl
        intro i hi
        simp only [losses, Finset.mem_filter, Finset.mem_univ, true_and] at hi
        rw [h_parts i]
        exact computePart_val_when_lose i input ct h_bits hi

      calc (Finset.univ : Finset (Fin 127)).sum (fun i => parts[i].val)
          = (wins ∪ losses ∪ ties).sum (fun i => parts[i].val) := by rw [h_union]
        _ = (wins ∪ losses).sum (fun i => parts[i].val) + ties.sum (fun i => parts[i].val) := by
            have h_wl_t_disj : Disjoint (wins ∪ losses) ties := by
              rw [Finset.disjoint_union_left]; exact ⟨h_disjoint_wt, h_disjoint_lt⟩
            exact Finset.sum_union h_wl_t_disj
        _ = wins.sum (fun i => parts[i].val) + losses.sum (fun i => parts[i].val) +
            ties.sum (fun i => parts[i].val) := by
            rw [Finset.sum_union h_disjoint_wl]
        _ = wins.sum (fun i => parts[i].val) + losses.sum (fun i => parts[i].val) := by
            rw [h_ties_zero]; ring
        _ = wins.card * 2^128 - W + Λ := by rw [h_wins_val, h_losses_val]

    rw [vector_sum_eq_list_sum', list_sum_val_eq' h_sum_lt_p, h_sum_partition]

    have h_n_pos : wins.card ≥ 1 := h_wins_card_pos
    have h_key : (wins.card * 2^128 - W + Λ) / 2^127 = 2 * wins.card - 1 := by
      have h_W_ge_Λ : W ≥ Λ := Nat.le_of_lt hW_gt_Λ
      have h_rearrange : wins.card * 2^128 - W + Λ = wins.card * 2^128 - (W - Λ) := by
        have : W - Λ + Λ = W := Nat.sub_add_cancel h_W_ge_Λ
        have h_W_le : W ≤ wins.card * 2^128 := by
          have h_W_lt : W < 2^127 := Nat.lt_of_le_of_lt hW_bound (Nat.sub_one_lt (Nat.two_pow_pos 127).ne')
          have h1 : (2 : ℕ)^127 ≤ 1 * 2^128 := by
            calc (2 : ℕ)^127 ≤ 2^128 := Nat.pow_le_pow_right (by omega) (by omega)
              _ = 1 * 2^128 := by ring
          have h2 : 1 * 2^128 ≤ wins.card * 2^128 := Nat.mul_le_mul_right _ h_n_pos
          have h3 : W < wins.card * 2^128 := calc W < 2^127 := h_W_lt
            _ ≤ 1 * 2^128 := h1
            _ ≤ wins.card * 2^128 := h2
          exact Nat.le_of_lt h3
        omega
      rw [h_rearrange]
      have h_WΛ_pos : W - Λ > 0 := hW_sub_Λ_pos
      have h_WΛ_bound : W - Λ < 2^127 := hW_sub_Λ_bound
      have h_expand : wins.card * 2^128 - (W - Λ) = (2 * wins.card - 1) * 2^127 + (2^127 - (W - Λ)) := by
        have h1 : wins.card * 2^128 = 2 * wins.card * 2^127 := by ring
        have h2 : 2 * wins.card * 2^127 = (2 * wins.card - 1) * 2^127 + 2^127 := by
          have : 2 * wins.card - 1 + 1 = 2 * wins.card := Nat.sub_add_cancel (by omega : 2 * wins.card ≥ 1)
          calc 2 * wins.card * 2^127 = (2 * wins.card - 1 + 1) * 2^127 := by rw [this]
            _ = (2 * wins.card - 1) * 2^127 + 1 * 2^127 := by ring
            _ = (2 * wins.card - 1) * 2^127 + 2^127 := by ring
        calc wins.card * 2^128 - (W - Λ) = 2 * wins.card * 2^127 - (W - Λ) := by rw [h1]
          _ = (2 * wins.card - 1) * 2^127 + 2^127 - (W - Λ) := by rw [h2]
          _ = (2 * wins.card - 1) * 2^127 + (2^127 - (W - Λ)) := by omega
      rw [h_expand]
      have h_remainder_lt : 2^127 - (W - Λ) < 2^127 := Nat.sub_lt (Nat.two_pow_pos 127) h_WΛ_pos
      have h_div : ((2 * wins.card - 1) * 2^127 + (2^127 - (W - Λ))) / 2^127 = 2 * wins.card - 1 := by
        rw [Nat.add_comm]
        rw [Nat.add_mul_div_right _ _ (Nat.two_pow_pos 127)]
        rw [Nat.div_eq_of_lt h_remainder_lt]
        simp
      exact h_div

    rw [h_key]
    have : 2 * wins.card - 1 = 2 * (wins.card - 1) + 1 := by omega
    rw [this]
    simp only [Nat.add_mod, Nat.mul_mod_right, Nat.zero_add, Nat.one_mod]

  -- Case 2: input ≤ ct → sum.val / 2^127 is even
  · intro h_le
    obtain h_all_tie | ⟨k, h_lose_k, h_tie_above⟩ := msb_determines_le ct h_ct input h_bits h_le

    · have h_all_zero : ∀ i : Fin 127, parts[i].val = 0 := by
        intro i
        rw [h_parts i]
        have := computePart_characterization i.val i.isLt input[i.val * 2] input[i.val * 2 + 1]
          (h_bits (i.val * 2) (by omega)) (h_bits (i.val * 2 + 1) (by omega)) ct
        simp only [signalPairValF] at this
        have h_tie := h_all_tie i
        simp only [signalPairValF] at h_tie
        simp only [this, h_tie, lt_irrefl, ↓reduceIte]
      have h_sum_zero : parts.sum = 0 := by
        rw [vector_sum_eq_list_sum']
        apply List.sum_eq_zero
        intro x hx
        rw [List.mem_iff_getElem] at hx
        obtain ⟨i, hi, rfl⟩ := hx
        simp only [Vector.getElem_toList]
        rw [Vector.length_toList] at hi
        have := h_all_zero ⟨i, hi⟩
        simp only [ZMod.val_eq_zero] at this
        exact this
      simp only [h_sum_zero, ZMod.val_zero, Nat.zero_div, Nat.zero_mod]

    · have h_parts_bounded := parts_val_bounded input h_bits parts ct h_parts
      have h_sum_lt_p := parts_sum_lt_p parts h_parts_bounded

      let wins := Finset.filter (fun i : Fin 127 =>
        signalPairValF input[i.val * 2] input[i.val * 2 + 1] > constPairValAt i.val ct) Finset.univ
      let losses := Finset.filter (fun i : Fin 127 =>
        signalPairValF input[i.val * 2] input[i.val * 2 + 1] < constPairValAt i.val ct) Finset.univ

      have hk_in_losses : k ∈ losses := by
        simp only [losses, Finset.mem_filter, Finset.mem_univ, true_and, signalPairValF]
        exact h_lose_k

      have h_wins_lt_k : ∀ j ∈ wins, j < k := by
        intro j hj
        by_contra h_ge_k
        push_neg at h_ge_k
        rcases h_ge_k.lt_or_eq with h_gt_k | h_eq_k
        · have h_tie := h_tie_above j h_gt_k
          simp only [wins, Finset.mem_filter, Finset.mem_univ, true_and, signalPairValF] at hj
          simp only [signalPairValF] at h_tie
          omega
        · subst h_eq_k
          simp only [wins, Finset.mem_filter, Finset.mem_univ, true_and, signalPairValF] at hj h_lose_k
          omega

      let W := wins.sum (fun i => 2^i.val)
      let Λ := losses.sum (fun i => 2^i.val)

      have hW_lt : W < 2^k.val := by
        have h_wins_subset : wins ⊆ Finset.filter (fun i : Fin 127 => i.val < k.val) Finset.univ := by
          intro j hj
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact h_wins_lt_k j hj
        have h1 : W ≤ (Finset.filter (fun i : Fin 127 => i.val < k.val) Finset.univ).sum (fun i => 2^i.val) :=
          Finset.sum_le_sum_of_subset h_wins_subset
        have h_sum_eq : (Finset.filter (fun i : Fin 127 => i.val < k.val) Finset.univ).sum (fun i : Fin 127 => 2^i.val)
            = (Finset.univ : Finset (Fin k.val)).sum (fun i => 2^i.val) := by
          symm
          apply Finset.sum_bij (fun (i : Fin k.val) _ => (⟨i.val, Nat.lt_trans i.isLt k.isLt⟩ : Fin 127))
          · intro i _; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact i.isLt
          · intro _ _ _ _ h; simp only [Fin.mk.injEq] at h; exact Fin.ext h
          · intro j hj
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
            exact ⟨⟨j.val, hj⟩, Finset.mem_univ _, rfl⟩
          · intro _ _; rfl
        have h2 : (Finset.filter (fun i : Fin 127 => i.val < k.val) Finset.univ).sum (fun i => 2^i.val)
                ≤ 2^k.val - 1 := by rw [h_sum_eq, sum_pow_two_fin]
        have h3 : 2^k.val - 1 < 2^k.val := Nat.sub_one_lt (Nat.two_pow_pos k.val).ne'
        exact Nat.lt_of_le_of_lt (Nat.le_trans h1 h2) h3

      have hΛ_ge : Λ ≥ 2^k.val := by
        show 2^k.val ≤ Λ
        exact Finset.single_le_sum (f := fun i : Fin 127 => 2^i.val)
          (fun _ _ => Nat.zero_le _) hk_in_losses

      have hW_lt_Λ : W < Λ := by omega

      have hΛ_bound : Λ ≤ 2^127 - 1 := by
        calc Λ ≤ (Finset.univ : Finset (Fin 127)).sum (fun i => 2^i.val) :=
                Finset.sum_le_sum_of_subset (by intro _ _; exact Finset.mem_univ _)
          _ = 2^127 - 1 := sum_pow_two_fin 127

      have h_sum_partition : (parts.toList.map ZMod.val).sum =
          wins.card * 2^128 - W + Λ := by
        have h_sum_eq : (parts.toList.map ZMod.val).sum =
            (Finset.univ : Finset (Fin 127)).sum (fun i => parts[i].val) := by
          trans (List.ofFn (fun i : Fin 127 => parts[i].val)).sum
          · congr 1
            apply List.ext_getElem
            · rw [List.length_map, Vector.length_toList, List.length_ofFn]
            · intro i h1 h2
              rw [List.length_map, Vector.length_toList] at h1
              simp only [List.getElem_map, Vector.getElem_toList, List.getElem_ofFn]
              rfl
          · simp only [List.sum_ofFn]
        rw [h_sum_eq]

        let ties := Finset.filter (fun i : Fin 127 =>
          signalPairValF input[i.val * 2] input[i.val * 2 + 1] = constPairValAt i.val ct) Finset.univ

        have h_disjoint_wl : Disjoint wins losses := by
          simp only [wins, losses, Finset.disjoint_filter]; intro i _ h1 h2; omega
        have h_disjoint_wt : Disjoint wins ties := by
          simp only [wins, ties, Finset.disjoint_filter]; intro i _ h1 h2; omega
        have h_disjoint_lt : Disjoint losses ties := by
          simp only [losses, ties, Finset.disjoint_filter]; intro i _ h1 h2; omega

        have h_union : wins ∪ losses ∪ ties = Finset.univ := by
          ext i; simp only [Finset.mem_union, wins, losses, ties, Finset.mem_filter,
                            Finset.mem_univ, true_and, iff_true]; omega

        have h_ties_zero : ties.sum (fun i => parts[i].val) = 0 := by
          apply Finset.sum_eq_zero
          intro i hi
          simp only [ties, Finset.mem_filter, Finset.mem_univ, true_and] at hi
          rw [h_parts i]
          have := computePart_characterization i.val i.isLt input[i.val * 2] input[i.val * 2 + 1]
            (h_bits (i.val * 2) (by omega)) (h_bits (i.val * 2 + 1) (by omega)) ct
          simp only [signalPairValF] at this hi
          simp only [this, hi, lt_irrefl, ↓reduceIte]

        have h_wins_val : wins.sum (fun i => parts[i].val) = wins.card * 2^128 - W := by
          have h_eq : wins.sum (fun i => parts[i].val) = wins.sum (fun i => 2^128 - 2^i.val) := by
            apply Finset.sum_congr rfl
            intro i hi
            simp only [wins, Finset.mem_filter, Finset.mem_univ, true_and] at hi
            rw [h_parts i]
            have := computePart_characterization i.val i.isLt input[i.val * 2] input[i.val * 2 + 1]
              (h_bits (i.val * 2) (by omega)) (h_bits (i.val * 2 + 1) (by omega)) ct
            simp only [signalPairValF] at this hi
            simp only [this, hi, ↓reduceIte]
          rw [h_eq]
          have h_sum_sub : ∀ (t : Finset (Fin 127)),
              t.sum (fun i => 2^128 - 2^i.val) = t.card * 2^128 - t.sum (fun i => 2^i.val) := by
            intro t
            induction t using Finset.induction with
            | empty => simp
            | @insert a s ha ih =>
              have h_a_ge : 2^a.val ≤ 2^128 :=
                Nat.pow_le_pow_right (by omega) (Nat.le_of_lt (Nat.lt_trans a.isLt (by omega : 127 < 128)))
              have h_s_ge : ∀ i ∈ s, 2^i.val ≤ 2^128 := fun i _ =>
                Nat.pow_le_pow_right (by omega) (Nat.le_of_lt (Nat.lt_trans i.isLt (by omega : 127 < 128)))
              simp only [Finset.sum_insert ha, Finset.card_insert_of_notMem ha]
              rw [ih]
              have h_sum_le : s.sum (fun i => 2^i.val) ≤ s.card * 2^128 := by
                calc s.sum (fun i => 2^i.val)
                    ≤ s.sum (fun _ => 2^128) := Finset.sum_le_sum (fun i hi => h_s_ge i hi)
                  _ = s.card * 2^128 := by simp [Finset.sum_const, smul_eq_mul]
              omega
          rw [h_sum_sub wins]

        have h_losses_val : losses.sum (fun i => parts[i].val) = Λ := by
          simp only [Λ]
          apply Finset.sum_congr rfl
          intro i hi
          simp only [losses, Finset.mem_filter, Finset.mem_univ, true_and] at hi
          rw [h_parts i]
          have := computePart_characterization i.val i.isLt input[i.val * 2] input[i.val * 2 + 1]
            (h_bits (i.val * 2) (by omega)) (h_bits (i.val * 2 + 1) (by omega)) ct
          simp only [signalPairValF] at this hi
          have h_not_gt : ¬(input[i.val * 2 + 1].val * 2 + input[i.val * 2].val >
                            constPairValAt i.val ct) := by omega
          have h_not_eq : ¬(input[i.val * 2 + 1].val * 2 + input[i.val * 2].val =
                            constPairValAt i.val ct) := by omega
          simp only [this, h_not_gt, h_not_eq, ↓reduceIte]

        calc (Finset.univ : Finset (Fin 127)).sum (fun i => parts[i].val)
            = (wins ∪ losses ∪ ties).sum (fun i => parts[i].val) := by rw [h_union]
          _ = (wins ∪ losses).sum (fun i => parts[i].val) + ties.sum (fun i => parts[i].val) := by
              have h_wl_t_disj : Disjoint (wins ∪ losses) ties := by
                rw [Finset.disjoint_union_left]; exact ⟨h_disjoint_wt, h_disjoint_lt⟩
              exact Finset.sum_union h_wl_t_disj
          _ = wins.sum (fun i => parts[i].val) + losses.sum (fun i => parts[i].val) +
              ties.sum (fun i => parts[i].val) := by
              rw [Finset.sum_union h_disjoint_wl]
          _ = wins.sum (fun i => parts[i].val) + losses.sum (fun i => parts[i].val) := by
              rw [h_ties_zero]; ring
          _ = wins.card * 2^128 - W + Λ := by rw [h_wins_val, h_losses_val]

      rw [vector_sum_eq_list_sum', list_sum_val_eq' h_sum_lt_p, h_sum_partition]

      have h_Λ_W_bound : Λ - W < 2^127 := by omega

      have hW_bound : W ≤ 2^127 - 1 := by
        calc W ≤ (Finset.univ : Finset (Fin 127)).sum (fun i => 2^i.val) :=
              Finset.sum_le_sum_of_subset (by intro _ _; exact Finset.mem_univ _)
          _ = 2^127 - 1 := sum_pow_two_fin 127

      have h_key : (wins.card * 2^128 - W + Λ) / 2^127 = 2 * wins.card := by
        by_cases h_wins_zero : wins.card = 0
        · have h_wins_empty : wins = ∅ := Finset.card_eq_zero.mp h_wins_zero
          have hW_zero : W = 0 := by simp only [W, h_wins_empty, Finset.sum_empty]
          simp only [h_wins_zero, hW_zero, Nat.zero_mul, Nat.zero_sub, Nat.zero_add]
          have hΛ_lt : Λ < 2^127 := by omega
          rw [Nat.div_eq_of_lt hΛ_lt]
        · have h_wins_pos : wins.card ≥ 1 := Nat.one_le_iff_ne_zero.mpr h_wins_zero
          have h_W_le : W ≤ wins.card * 2^128 := by
            have h1 : W ≤ 2^127 - 1 := hW_bound
            have h2 : (2 : ℕ)^127 - 1 < 2^128 := by
              calc (2 : ℕ)^127 - 1 < 2^127 := Nat.sub_one_lt (Nat.two_pow_pos 127).ne'
                _ ≤ 2^128 := Nat.pow_le_pow_right (by omega) (by omega)
            have h3 : (1 : ℕ) * 2^128 ≤ wins.card * 2^128 := Nat.mul_le_mul_right _ h_wins_pos
            omega
          have h_rearrange : wins.card * 2^128 - W + Λ = wins.card * 2^128 + (Λ - W) := by
            omega
          rw [h_rearrange]
          have h_expand : wins.card * 2^128 + (Λ - W) = 2 * wins.card * 2^127 + (Λ - W) := by ring
          rw [h_expand]
          apply Nat.div_eq_of_lt_le
          · omega
          · calc 2 * wins.card * 2^127 + (Λ - W) < 2 * wins.card * 2^127 + 2^127 := by omega
              _ = (2 * wins.card + 1) * 2^127 := by ring

      rw [h_key]
      omega

omit [Fact (p < 2 ^ 254)] in
lemma sum_bit127_encodes_gt (ct : ℕ) (h_ct : ct < 2^254)
    (input : Vector (F p) 254)
    (h_bits : ∀ i (_ : i < 254), input[i] = 0 ∨ input[i] = 1)
    (parts : Vector (F p) 127)
    (h_parts : ∀ i : Fin 127,
      parts[i] = computePart i.val input[i.val * 2] input[i.val * 2 + 1] ct) :
    let sum := parts.sum
    let input_val := fromBits (input.map ZMod.val)
    sum.val.testBit 127 = (input_val > ct) := by
  have h_range := sum_range_precise ct h_ct input h_bits parts h_parts
  by_cases h_cmp : fromBits (input.map ZMod.val) > ct
  · have h_odd := h_range.1 h_cmp
    simp only [h_cmp, Nat.testBit, Nat.shiftRight_eq_div_pow]
    rw [Nat.one_and_eq_mod_two, h_odd]
    decide
  · have h_le : fromBits (input.map ZMod.val) ≤ ct := by omega
    have h_even := h_range.2 h_le
    simp only [h_cmp, Nat.testBit, Nat.shiftRight_eq_div_pow]
    rw [Nat.one_and_eq_mod_two, h_even]
    decide

omit [Fact (p < 2 ^ 254)] [Fact (p > 2 ^ 253)] in
lemma fieldToBits_testBit_127 (x : F p) (n : ℕ) (hn : 127 < n) :
    (fieldToBits n x)[127] = if x.val.testBit 127 then 1 else 0 := by
  simp only [fieldToBits, toBits, Vector.getElem_map, Vector.getElem_mapRange]
  split_ifs <;> simp_all

end CompConstant

end Circomlib
