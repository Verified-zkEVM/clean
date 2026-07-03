import Clean.Circuit
import Clean.Gadgets.Boolean
import Clean.Orchard.Ecc
import Clean.Orchard.Specs.Bitrange
import Clean.Utils.Tactics

/-!
# NoteCommit canonicity theorems

Foundational bit-decomposition / Pallas-base-modulus canonicity facts shared by the
note-commitment gates.  Stated over `Orchard.Specs.bitrange` and the modulus, with no
reference to any particular circuit cell.
-/

namespace Orchard.Action.NoteCommit

variable {F : Type} [FiniteField F]

theorem mul_eq_zero_of_or {a b : F} (h : a = 0 ∨ b = 0) : a * b = 0 := by
  rcases h with h | h <;> rw [h] <;> simp

/-! ### Foundational bit-decomposition / canonicity facts

These are stated over `Orchard.Specs.bitrange` and the Pallas base modulus, with no
reference to any particular circuit cell (`y`, `j`, …). The canonicity gates build on
them. -/

open CompElliptic.Fields.Pasta (PALLAS_BASE_CARD)
open Orchard.Specs (bitrange bitrange_lt bitrange_add bitrange_mod)

/-- `t_P`, the Pallas base modulus minus `2^254`, as a natural number. -/
def tPNat : ℕ := 45560315531419706090280762371685220353

/-- The defining split of the Pallas base modulus: `p = 2^254 + t_P`. -/
theorem pallasBaseCard_eq : PALLAS_BASE_CARD = 2 ^ 254 + tPNat := by
  norm_num [PALLAS_BASE_CARD, tPNat]

/-- A `< 2^255` value is the sum of its low 250 bits, next 4 bits, and top bit. -/
theorem bit_decomp_255 {n : ℕ} (hn : n < 2 ^ 255) :
    n = bitrange n 0 250 + 2 ^ 250 * bitrange n 250 4 + 2 ^ 254 * bitrange n 254 1 := by
  simp only [bitrange, pow_zero, Nat.div_one]
  omega

/-- Canonicity with the top bit set: for `n < p` with bit 254 set, bits 250–253 vanish
and the low 250 bits lie below `t_P` (hence the `+2^130-t_P` shift stays below `2^130`). -/
theorem high_bit_canonical {n : ℕ} (hn : n < PALLAS_BASE_CARD) (hhigh : bitrange n 254 1 = 1) :
    bitrange n 250 4 = 0 ∧ bitrange n 0 250 < tPNat ∧
      bitrange n 0 250 + 2 ^ 130 - tPNat < 2 ^ 130 := by
  have hdec := bit_decomp_255 (lt_trans hn (by norm_num [PALLAS_BASE_CARD]))
  have hlo := bitrange_lt n 0 250
  have hk2 := bitrange_lt n 250 4
  rw [hhigh] at hdec
  rw [pallasBaseCard_eq] at hn
  norm_num [tPNat] at hlo hk2 hn hdec ⊢
  omega

/-- `lsb` is the low (sign) bit of the field element `y`. -/
def IsLowBit (y lsb : Fp) : Prop :=
  lsb.val = y.val % 2

theorem nat_mod_two_isBool (n : ℕ) : IsBool (((n % 2 : ℕ) : Fp)) := by
  have hlt : n % 2 < 2 := Nat.mod_lt _ (by norm_num)
  interval_cases n % 2 <;> simp [IsBool]

theorem isLowBit_iff_mod_two {y lsb : Fp} :
    IsLowBit y lsb ↔ lsb = ((y.val % 2 : ℕ) : Fp) := by
  have hlt : y.val % 2 < PALLAS_BASE_CARD :=
    lt_trans (Nat.mod_lt _ (by norm_num)) (by norm_num [PALLAS_BASE_CARD])
  unfold IsLowBit
  constructor
  · intro h
    rw [← ZMod.natCast_rightInverse lsb, h]
  · intro h
    rw [h, ZMod.val_natCast_of_lt hlt]

/-- The low bit is Boolean. -/
theorem isBool_of_isLowBit {y lsb : Fp} (h : IsLowBit y lsb) : IsBool lsb := by
  rw [isLowBit_iff_mod_two] at h
  rw [h]; exact nat_mod_two_isBool _

/-- `tP` as the cast of the natural number `tPNat`. -/
theorem tP_eq : tP = ((tPNat : ℕ) : Fp) := by
  rw [tP, tPNat]; norm_num

/-- A 1-bit field slice is Boolean. -/
theorem bitrange_one_isBool (n start : ℕ) :
    IsBool ((bitrange n start 1 : ℕ) : Fp) := by
  have h : bitrange n start 1 < 2 := by simpa using bitrange_lt n start 1
  interval_cases (bitrange n start 1) <;> simp [IsBool]

/-- The low 250-bit field splits into the sign bit, the next 9 bits, and the rest. -/
theorem low_250_decomp (n : ℕ) :
    bitrange n 0 250 = bitrange n 0 1 + 2 * bitrange n 1 9 + 1024 * bitrange n 10 240 := by
  have h1 := bitrange_add n 0 1 249
  have h2 := bitrange_add n 1 9 240
  norm_num at h1 h2
  rw [h1, h2]; ring

/-- With the top bit set, the bits 130–249 of a canonical value vanish. -/
theorem high_bit_z13_zero {n : ℕ} (hn : n < PALLAS_BASE_CARD)
    (hhigh : bitrange n 254 1 = 1) : bitrange n 130 120 = 0 := by
  obtain ⟨_, hlo, _⟩ := high_bit_canonical hn hhigh
  have hsplit := bitrange_add n 0 130 120
  have htp : tPNat < 2 ^ 130 := by norm_num [tPNat]
  have key : bitrange n 0 (130 + 120) < 2 ^ 130 := by
    rw [show (130 : ℕ) + 120 = 250 by norm_num]; omega
  rw [hsplit] at key
  rcases Nat.eq_zero_or_pos (bitrange n (0 + 130) 120) with h | h
  · simpa using h
  · exfalso
    have hge : 2 ^ 130 ≤ 2 ^ 130 * bitrange n (0 + 130) 120 := Nat.le_mul_of_pos_right _ h
    omega

/-- The canonical top-bit decomposition shared by the `x`/`rho`/`psi` canonicity gates: a
field element written `x = lo + top·2^254`, with `lo` a `< 2^254` value, `top` a bit, and the
canonicity side-condition `top = 1 → lo < t_P`, equals `lo + top·2^254` over `ℕ` (no
wraparound) and so `lo`/`top` are its canonical low-254-bit field and top bit. -/
theorem canonical_top_decomp {x lo top : Fp}
    (hrec : x = lo + top * ((2 ^ 254 : ℕ) : Fp))
    (hlo : lo.val < 2 ^ 254) (htop : IsBool top)
    (hcanon : top = 1 → lo.val < tPNat) :
    x.val = lo.val + top.val * 2 ^ 254 ∧
      lo.val = bitrange x.val 0 254 ∧ top.val = bitrange x.val 254 1 := by
  haveI : Fact (1 < PALLAS_BASE_CARD) := ⟨by norm_num [PALLAS_BASE_CARD]⟩
  have hp := pallasBaseCard_eq
  have htv : top.val < 2 := by rcases htop with h | h <;> subst h <;> simp [ZMod.val_one]
  have hwrap : lo.val + top.val * 2 ^ 254 < PALLAS_BASE_CARD := by
    rcases htop with h | h
    · have h0 : top.val = 0 := by rw [h]; simp
      omega
    · have hc := hcanon h
      omega
  have hcast : x = ((lo.val + top.val * 2 ^ 254 : ℕ) : Fp) := by
    rw [hrec]; push_cast
    rw [ZMod.natCast_rightInverse lo, ZMod.natCast_rightInverse top]
  have hxnat : x.val = lo.val + top.val * 2 ^ 254 := by
    rw [hcast, ZMod.val_natCast_of_lt hwrap]
  refine ⟨hxnat, ?_, ?_⟩
  · simp only [bitrange, hxnat]; omega
  · simp only [bitrange, hxnat]; omega

/-- `.val` of a non-overflowing two-limb sum `lo + hi·2^k`. -/
theorem val_limb2 {lo hi : Fp} (k : ℕ)
    (hsum : lo.val + hi.val * 2 ^ k < PALLAS_BASE_CARD) :
    (lo + hi * ((2 ^ k : ℕ) : Fp)).val = lo.val + hi.val * 2 ^ k := by
  have hcast : lo + hi * ((2 ^ k : ℕ) : Fp) = ((lo.val + hi.val * 2 ^ k : ℕ) : Fp) := by
    push_cast
    rw [ZMod.natCast_rightInverse lo, ZMod.natCast_rightInverse hi]
  rw [hcast, ZMod.val_natCast_of_lt hsum]

/-- `.val` of the canonicity-shifted cell `a + 2^k - t_P` (no underflow / overflow). -/
theorem val_shift {a : Fp} (k : ℕ) (htp : tPNat ≤ a.val + 2 ^ k)
    (hlt : a.val + 2 ^ k - tPNat < PALLAS_BASE_CARD) :
    (a + ((2 ^ k : ℕ) : Fp) - tP).val = a.val + 2 ^ k - tPNat := by
  have hcast : a + ((2 ^ k : ℕ) : Fp) - tP = ((a.val + 2 ^ k - tPNat : ℕ) : Fp) := by
    rw [tP_eq, Nat.cast_sub htp]
    push_cast
    rw [ZMod.natCast_rightInverse a]
  rw [hcast, ZMod.val_natCast_of_lt hlt]

/-- A canonicity-shifted cell `lo + 2^k - t_P` with `lo < t_P` (and `130 ≤ k ≤ 254`) is
`< 2^k`, so its `k`-bit running-sum tail vanishes. Shared by the `NoteCommit`/`CommitIvk`
canonicity gates (and their completeness, via `Telescoped.zLast_eq_zero`). -/
theorem shifted_high_zero {lo : Fp} {k : ℕ} (hk : 130 ≤ k) (hk254 : k ≤ 254)
    (hlo : lo.val < tPNat) :
    (lo + ((2 ^ k : ℕ) : Fp) - tP).val / 2 ^ k = 0 := by
  have htp : tPNat < 2 ^ k :=
    lt_of_lt_of_le (by norm_num [tPNat] : tPNat < 2 ^ 130) (Nat.pow_le_pow_right (by norm_num) hk)
  have hp := pallasBaseCard_eq
  have hPk : (2 : ℕ) ^ k ≤ 2 ^ 254 := Nat.pow_le_pow_right (by norm_num) hk254
  have hval : (lo + ((2 ^ k : ℕ) : Fp) - tP).val = lo.val + 2 ^ k - tPNat :=
    val_shift k (by omega) (by omega)
  rw [hval, Nat.div_eq_of_lt (by omega)]

/-- A one-bit slice cast to `Fp` that equals `1` is the bit value `1`. (Turns a canonicity
gate's `b = ((bitrange n s 1 : ℕ) : Fp)` plus `b = 1` into `bitrange n s 1 = 1`.) -/
theorem bit_one_of_eq {b : Fp} {n s : ℕ} (heq : b = ((bitrange n s 1 : ℕ) : Fp))
    (h1 : b = 1) : bitrange n s 1 = 1 := by
  rcases (show bitrange n s 1 = 0 ∨ bitrange n s 1 = 1 from by
    have := bitrange_lt n s 1; omega) with h | h
  · rw [heq, h] at h1; norm_num at h1
  · exact h

/-- `.val`-form sibling of `bit_one_of_eq`: a one-bit slice whose cell equals `1` has
`bitrange = 1`. (Lets canonicity consumers stay in the `.val = bitrange` spelling.) -/
theorem bit_one_of_val_eq {b : Fp} {n s : ℕ} (heq : b.val = bitrange n s 1)
    (h1 : b = 1) : bitrange n s 1 = 1 :=
  bit_one_of_eq (by rw [← heq]; exact (ZMod.natCast_rightInverse b).symm) h1

/-- Canonicity with the top bit set, in the form needed when the canonicity element spans
the full low 254 bits (the `pk_d`/`rho` gates): `n < p` with bit 254 set forces the low 254
bits below `t_P`. -/
theorem high_bit_canonical_254 {n : ℕ} (hn : n < PALLAS_BASE_CARD)
    (hhigh : bitrange n 254 1 = 1) : bitrange n 0 254 < tPNat := by
  have hsplit := bitrange_add n 0 254 1
  have hfull : bitrange n 0 255 = n := by
    simp only [bitrange, pow_zero, Nat.div_one]
    exact Nat.mod_eq_of_lt (lt_trans hn (by norm_num [PALLAS_BASE_CARD]))
  rw [show (254 : ℕ) + 1 = 255 from rfl, hfull, hhigh, mul_one] at hsplit
  rw [pallasBaseCard_eq] at hn
  omega

/-- Top bit set ⇒ every low-bit prefix of width `≤ 254` lies below `t_P`. Generalises
`high_bit_canonical` over the prefix width, covering all four `x`/`rho`/`psi` canonicity
gates (whose canonicity bases are the low `250`/`254`/`254`/`249` bits). -/
theorem high_bit_low_lt_tP {n : ℕ} (hn : n < PALLAS_BASE_CARD)
    (hhigh : bitrange n 254 1 = 1) {s : ℕ} (hs : s ≤ 254) :
    bitrange n 0 s < tPNat := by
  have h254 := high_bit_canonical_254 hn hhigh
  have hle : bitrange n 0 s ≤ bitrange n 0 254 := by
    simp only [bitrange, pow_zero, Nat.div_one]
    conv_lhs => rw [← Nat.mod_mod_of_dvd n (pow_dvd_pow 2 hs)]
    exact Nat.mod_le _ _
  omega

/-- The two-limb canonicity base `lo + 2^a·hi` (where `lo`/`hi` are the canonical low-`a`
and next-`b` slices of `n`) equals the low `(a+b)` bits as a field element; with the top
bit set it lies below `t_P`. Feeds `shifted_high_zero` for the `pk_d`/`rho`/`psi` gates. -/
theorem base_val_lt_tP {loF hiF : Fp} {n a b : ℕ}
    (hlo : loF = ((bitrange n 0 a : ℕ) : Fp))
    (hhi : hiF = ((bitrange n a b : ℕ) : Fp))
    (hn : n < PALLAS_BASE_CARD) (hhigh : bitrange n 254 1 = 1) (hab : a + b ≤ 254) :
    (loF + ((2 ^ a : ℕ) : Fp) * hiF).val < tPNat := by
  have hbr := bitrange_add n 0 a b
  simp only [Nat.zero_add] at hbr
  have hbase : loF + ((2 ^ a : ℕ) : Fp) * hiF = ((bitrange n 0 (a + b) : ℕ) : Fp) := by
    rw [hlo, hhi, hbr]; push_cast; ring
  have hlt : bitrange n 0 (a + b) < PALLAS_BASE_CARD :=
    lt_trans (bitrange_lt n 0 (a + b))
      (lt_of_le_of_lt (Nat.pow_le_pow_right (by norm_num) hab)
        (by norm_num [PALLAS_BASE_CARD]))
  rw [hbase, ZMod.val_natCast_of_lt hlt]
  exact high_bit_low_lt_tP hn hhigh hab

/-- `.val`-form sibling of `base_val_lt_tP`: the canonical low/next slices are given by
their `.val = bitrange` cells (as produced by the converted canonicity gate specs). -/
theorem base_val_lt_tP_val {loF hiF : Fp} {n a b : ℕ}
    (hlo : loF.val = bitrange n 0 a)
    (hhi : hiF.val = bitrange n a b)
    (hn : n < PALLAS_BASE_CARD) (hhigh : bitrange n 254 1 = 1) (hab : a + b ≤ 254) :
    (loF + ((2 ^ a : ℕ) : Fp) * hiF).val < tPNat :=
  base_val_lt_tP (by rw [← hlo]; exact (ZMod.natCast_rightInverse loF).symm)
    (by rw [← hhi]; exact (ZMod.natCast_rightInverse hiF).symm) hn hhigh hab

/-- Dividing a `bitrange` of width `a+b` by `2^a` exposes the next `b` bits. -/
theorem bitrange_div_pow (n s a b : ℕ) :
    bitrange n s (a + b) / 2 ^ a = bitrange n (s + a) b := by
  simp only [bitrange]
  rw [pow_add, Nat.mod_mul_right_div_self, Nat.div_div_eq_div_mul, ← pow_add]

/-- Dividing the low `a+b` bits by `2^a` exposes the next `b` bits (the honest running
sum's `z_a` cell is the corresponding higher `bitrange`). -/
theorem bitrange_low_div (n a b : ℕ) :
    bitrange n 0 (a + b) / 2 ^ a = bitrange n a b := by
  simpa using bitrange_div_pow n 0 a b

/-- With the top bit set, every bit field of a canonical value at offset `≥ 130` (and
within the low 254 bits) vanishes. -/
theorem high_bit_high_zero {n : ℕ} (hn : n < PALLAS_BASE_CARD) (hh : bitrange n 254 1 = 1)
    {s len : ℕ} (hs : 130 ≤ s) (hsl : s + len ≤ 254) : bitrange n s len = 0 := by
  obtain ⟨hk2, hlo, _⟩ := high_bit_canonical hn hh
  have htps : tPNat < 2 ^ 130 := by norm_num [tPNat]
  have h254 : bitrange n 0 254 < 2 ^ 130 := by
    have hsplit := bitrange_add n 0 250 4
    norm_num at hsplit
    rw [hk2] at hsplit
    omega
  rw [← bitrange_mod (n := n) (s := s) (len := len) hsl]
  have hlt : n % 2 ^ 254 < 2 ^ 130 := by
    have : n % 2 ^ 254 = bitrange n 0 254 := by simp [bitrange]
    rw [this]; exact h254
  simp only [bitrange]
  rw [Nat.div_eq_of_lt (lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by norm_num) hs))]
  simp

/-- A sub-`p` natural that casts to `0` in `Fp` is `0` (used to read the canonicity guards:
`z = ↑(…) = 0` forces the running-sum tail to vanish). -/
theorem natCast_eq_zero {n : ℕ} (hlt : n < PALLAS_BASE_CARD) (h : ((n : ℕ) : Fp) = 0) :
    n = 0 := by
  have hv := congrArg ZMod.val h
  rwa [ZMod.val_natCast_of_lt hlt, ZMod.val_zero] at hv

end Orchard.Action.NoteCommit
