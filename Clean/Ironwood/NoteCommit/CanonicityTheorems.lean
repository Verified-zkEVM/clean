import Clean.Circuit
import Clean.Gadgets.Boolean
import Clean.Ironwood.Ecc.Defs
import Clean.Ironwood.Ecc.DoubleAndAdd
import Clean.Ironwood.Ecc.AddTheorems
import Clean.Ironwood.Ecc.AddIncompleteTheorems
import Clean.Ironwood.Ecc.MulAssignTheorems
import Clean.Ironwood.Ecc.MulFixed.Theorems
import Clean.Ironwood.Ecc.MulFixed.BaseFieldElemTheorems
import Clean.Ironwood.Ecc.MulFixed.ShortTheorems
import Clean.Ironwood.Specs.Bitrange
import Clean.Utils.Tactics
import Clean.Utils.Tactics.ProvableStructDeriving

/-!
# NoteCommit canonicity theorems

Foundational bit-decomposition / Pallas-base-modulus canonicity facts shared by the
note-commitment gates.  Stated over `Specs.bitrange` and the modulus, with no
reference to any particular circuit cell.
-/

namespace Zcash.Circuits.NoteCommit

open Clean

variable {F : Type} [FiniteField F]

theorem mul_eq_zero_of_or {a b : F} (h : a = 0 ∨ b = 0) : a * b = 0 := by
  rcases h with h | h <;> rw [h] <;> simp

/-! ### Foundational bit-decomposition / canonicity facts

These are stated over `Specs.bitrange` and the Pallas base modulus, with no
reference to any particular circuit cell (`y`, `j`, …). The canonicity gates build on
them. -/

open CompElliptic.Fields.Pasta (PALLAS_BASE_CARD)
open Specs (bitrange bitrange_lt bitrange_add bitrange_mod)

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

end Zcash.Circuits.NoteCommit

/-! ### Canonicity custom-gate specs (`note_commit.rs` `*Canonicity` gates) -/

namespace Zcash.Circuits.NoteCommit

open Specs (bitrange bitrange_lt bitrange_add bitrange_mod)
open CompElliptic.Fields.Pasta (PALLAS_BASE_CARD)

namespace GdCanonicity.Gate

structure Row (F : Type) where
  gdX : F
  b0 : F
  b1 : F
  a : F
  a' : F
  z13A : F
  z13A' : F
deriving ProvableStruct

/-- Rely-conditions from the surrounding lookups: `a`/`b0` are range-checked, `b1` is
Boolean, `a'` is the canonicity shift of `a`, and `z13A`/`z13A'` are the 13-word
running-sum tails of `a`/`a'`. -/
def Assumptions (row : Row Fp) : Prop :=
  IsBool row.b1 ∧
    row.a.val < 2 ^ 250 ∧
    row.b0.val < 2 ^ 4 ∧
    row.a' = row.a + ((2 ^ 130 : ℕ) : Fp) - tP ∧
    row.z13A = ((row.a.val / 2 ^ 130 : ℕ) : Fp) ∧
    -- `z13A'` is the *partial* (13-word) CopyCheck running sum of `a'`, which overflows
    -- `2^130`, so only the telescoped decomposition is soundly available.
    ∃ lo : ℕ, lo < 2 ^ 130 ∧ row.a' = ((lo : ℕ) : Fp) + ((2 ^ 130 : ℕ) : Fp) * row.z13A'

/-- The gate's payoff: `a`/`b0`/`b1` are the canonical bit slices of `x(g_d)`. -/
def Spec (row : Row Fp) : Prop :=
  row.a.val = bitrange row.gdX.val 0 250 ∧
    row.b0.val = bitrange row.gdX.val 250 4 ∧
    row.b1.val = bitrange row.gdX.val 254 1 ∧
    (row.b1 = 1 → row.z13A' = 0)

/-- Row-level payoff (extracted from `soundness` for the halo2-native port): the gate
equations plus the rely-conditions pin the canonical slices of `x(g_d)`. -/
theorem spec_of_eqs (row : Row Fp) (hAss : Assumptions row)
    (heq1 : row.a + row.b0 * ((2 ^ 250 : ℕ) : Fp) + row.b1 * ((2 ^ 254 : ℕ) : Fp)
      - row.gdX = 0)
    (heq3 : row.b1 * row.b0 = 0) (heq4 : row.b1 * row.z13A = 0)
    (heq5 : row.b1 * row.z13A' = 0) : Spec row := by
  obtain ⟨hb1, ha_lt, hb0_lt, haPrime, hz13A, hzaDec⟩ := hAss
  have hp := pallasBaseCard_eq
  have htpsmall : tPNat < 2 ^ 130 := by norm_num [tPNat]
  -- low 254-bit limb `lo = a + b0·2^250`
  have hlo_sum : row.a.val + row.b0.val * 2 ^ 250 < PALLAS_BASE_CARD := by omega
  have hlo_val : (row.a + row.b0 * ((2 ^ 250 : ℕ) : Fp)).val
      = row.a.val + row.b0.val * 2 ^ 250 := val_limb2 250 hlo_sum
  have hlo_lt : (row.a + row.b0 * ((2 ^ 250 : ℕ) : Fp)).val < 2 ^ 254 := by
    rw [hlo_val]; omega
  -- canonicity: when the top bit is set, the low limb is below `t_P`
  have hcanon : row.b1 = 1 →
      (row.a + row.b0 * ((2 ^ 250 : ℕ) : Fp)).val < tPNat := by
    intro h1
    have hb0z : row.b0 = 0 := by
      rcases mul_eq_zero.mp heq3 with h | h
      · exact absurd (h1 ▸ h) one_ne_zero
      · exact h
    have ha130 : row.a.val < 2 ^ 130 := by
      have hz : row.z13A = 0 := by
        rcases mul_eq_zero.mp heq4 with h | h
        · exact absurd (h1 ▸ h) one_ne_zero
        · exact h
      rw [hz13A] at hz
      have := natCast_eq_zero
        (lt_of_le_of_lt (Nat.div_le_self _ _) (lt_trans ha_lt (by norm_num [PALLAS_BASE_CARD]))) hz
      omega
    have haPrime_val : row.a'.val = row.a.val + 2 ^ 130 - tPNat := by
      rw [haPrime]; exact val_shift 130 (by omega) (by omega)
    have haPrime_lt : row.a'.val < 2 ^ 130 := by
      have hz : row.z13A' = 0 := by
        rcases mul_eq_zero.mp heq5 with h | h
        · exact absurd (h1 ▸ h) one_ne_zero
        · exact h
      obtain ⟨lo, hlo, hdec⟩ := hzaDec
      rw [hz, mul_zero, _root_.add_zero] at hdec
      rw [hdec, ZMod.val_natCast_of_lt (lt_trans hlo (by norm_num [PALLAS_BASE_CARD]))]
      exact hlo
    -- `simp` first: `omega` exceeds the recursion limit on the raw `0 * 2 ^ 250` goal
    rw [hlo_val, hb0z, ZMod.val_zero]; simp only [zero_mul, add_zero]; omega
  -- top-bit decomposition of `gdX`
  have hrecL : row.gdX = (row.a + row.b0 * ((2 ^ 250 : ℕ) : Fp))
      + row.b1 * ((2 ^ 254 : ℕ) : Fp) := by linear_combination -heq1
  obtain ⟨_, hlo_eq, hb1_eq⟩ := canonical_top_decomp hrecL hlo_lt hb1 hcanon
  have hmod : bitrange row.gdX.val 0 254 = row.gdX.val % 2 ^ 254 := by simp [bitrange]
  -- read the sub-pieces off the low 254-bit field
  have ha_eq : row.a.val = bitrange row.gdX.val 0 250 := by
    have h1 : row.a.val = bitrange (row.a + row.b0 * ((2 ^ 250 : ℕ) : Fp)).val 0 250 := by
      simp only [bitrange, pow_zero, Nat.div_one, hlo_val]; omega
    rw [h1, hlo_eq, hmod, bitrange_mod (by norm_num : 0 + 250 ≤ 254)]
  have hb0_eq : row.b0.val = bitrange row.gdX.val 250 4 := by
    have h1 : row.b0.val = bitrange (row.a + row.b0 * ((2 ^ 250 : ℕ) : Fp)).val 250 4 := by
      simp only [bitrange, hlo_val]; omega
    rw [h1, hlo_eq, hmod, bitrange_mod (by norm_num : 250 + 4 ≤ 254)]
  exact ⟨ha_eq, hb0_eq, hb1_eq, fun h1 => by
    rcases mul_eq_zero.mp heq5 with h | h
    · exact absurd (h1 ▸ h) one_ne_zero
    · exact h⟩

/-- Row-level completeness direction: the rely-conditions plus the spec discharge the
gate equations. -/
theorem eqs_of_spec (row : Row Fp) (hAss : Assumptions row) (hSpec : Spec row) :
    (row.a + row.b0 * ((2 ^ 250 : ℕ) : Fp) + row.b1 * ((2 ^ 254 : ℕ) : Fp)
      - row.gdX = 0) ∧
    (row.a + ((2 ^ 130 : ℕ) : Fp) - tP - row.a' = 0) ∧
    row.b1 * row.b0 = 0 ∧ row.b1 * row.z13A = 0 ∧ row.b1 * row.z13A' = 0 := by
  obtain ⟨_, ha_lt, _, haPrime, hz13A, _⟩ := hAss
  obtain ⟨ha_val, hb0_val, hb1_val, hzaZero⟩ := hSpec
  have hp := pallasBaseCard_eq
  have htpsmall : tPNat < 2 ^ 130 := by norm_num [tPNat]
  have hgdX : row.gdX.val < 2 ^ 255 :=
    lt_trans (ZMod.val_lt row.gdX) (by norm_num [PALLAS_BASE_CARD])
  have ha_eq : row.a = ((bitrange row.gdX.val 0 250 : ℕ) : Fp) := by
    rw [← ha_val]; exact (ZMod.natCast_rightInverse row.a).symm
  have hb0_eq : row.b0 = ((bitrange row.gdX.val 250 4 : ℕ) : Fp) := by
    rw [← hb0_val]; exact (ZMod.natCast_rightInverse row.b0).symm
  have hb1_eq : row.b1 = ((bitrange row.gdX.val 254 1 : ℕ) : Fp) := by
    rw [← hb1_val]; exact (ZMod.natCast_rightInverse row.b1).symm
  have hb1cases := show bitrange row.gdX.val 254 1 = 0 ∨ bitrange row.gdX.val 254 1 = 1 from by
    have := bitrange_lt row.gdX.val 254 1; omega
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- reconstruction
    have hgd_eq : row.gdX = ((bitrange row.gdX.val 0 250 : ℕ) : Fp)
        + ((bitrange row.gdX.val 250 4 : ℕ) : Fp) * ((2 ^ 250 : ℕ) : Fp)
        + ((bitrange row.gdX.val 254 1 : ℕ) : Fp) * ((2 ^ 254 : ℕ) : Fp) := by
      conv_lhs => rw [← ZMod.natCast_rightInverse row.gdX, bit_decomp_255 hgdX]
      push_cast; ring
    rw [ha_eq, hb0_eq, hb1_eq]; linear_combination -hgd_eq
  · -- prime
    rw [haPrime]; ring
  · -- b1·b0 = 0
    rcases hb1cases with h | h
    · rw [hb1_eq, h]; simp
    · rw [hb0_eq, (high_bit_canonical (ZMod.val_lt row.gdX) h).1]; simp
  · -- b1·z13A = 0
    rcases hb1cases with h | h
    · rw [hb1_eq, h]; simp
    · rw [hz13A, ha_val,
        show bitrange row.gdX.val 0 250 / 2 ^ 130 = bitrange row.gdX.val 130 120 from
          bitrange_low_div row.gdX.val 130 120,
        high_bit_z13_zero (ZMod.val_lt row.gdX) h]
      simp
  · -- b1·z13A' = 0  (the canonicity-shifted running sum vanishes when the top bit is set)
    rcases hb1cases with h | h
    · rw [hb1_eq, h]; simp
    · rw [hzaZero (by rw [hb1_eq, h]; norm_num)]; simp

end GdCanonicity.Gate

namespace PkdCanonicity.Gate

structure Row (F : Type) where
  pkdX : F
  b3 : F
  d0 : F
  c : F
  b3C' : F
  z13C : F
  z14B3C' : F
deriving ProvableStruct

/-- Rely-conditions from the surrounding lookups: `b3`/`c` are range-checked, `d0` is
Boolean, `b3C'` is the canonicity shift of the low limb, and `z13C`/`z14B3C'` are
the running-sum tails of `c`/`b3C'`. -/
def Assumptions (row : Row Fp) : Prop :=
  IsBool row.d0 ∧
    row.c.val < 2 ^ 250 ∧
    row.b3.val < 2 ^ 4 ∧
    row.b3C' = row.b3 + row.c * ((2 ^ 4 : ℕ) : Fp) + ((2 ^ 140 : ℕ) : Fp) - tP ∧
    row.z13C = ((row.c.val / 2 ^ 130 : ℕ) : Fp) ∧
    ∃ lo : ℕ, lo < 2 ^ 140 ∧ row.b3C' = ((lo : ℕ) : Fp) + ((2 ^ 140 : ℕ) : Fp) * row.z14B3C'

/-- The gate's payoff: `b3`/`c`/`d0` are the canonical bit slices of `x(pk_d)`. -/
def Spec (row : Row Fp) : Prop :=
  row.b3.val = bitrange row.pkdX.val 0 4 ∧
    row.c.val = bitrange row.pkdX.val 4 250 ∧
    row.d0.val = bitrange row.pkdX.val 254 1 ∧
    (row.d0 = 1 → row.z14B3C' = 0)

/-- Row-level payoff (extracted from `soundness` for the halo2-native port). -/
theorem spec_of_eqs (row : Row Fp) (hAss : Assumptions row)
    (heq1 : row.b3 + row.c * ((2 ^ 4 : ℕ) : Fp) + row.d0 * ((2 ^ 254 : ℕ) : Fp)
      - row.pkdX = 0)
    (heq3 : row.d0 * row.z13C = 0) (heq4 : row.d0 * row.z14B3C' = 0) : Spec row := by
  obtain ⟨hd0, hc_lt, hb3_lt, hb3cP, hz13C, hzbDec⟩ := hAss
  have hp := pallasBaseCard_eq
  have htpsmall : tPNat < 2 ^ 130 := by norm_num [tPNat]
  have hlo_sum : row.b3.val + row.c.val * 2 ^ 4 < PALLAS_BASE_CARD := by omega
  have hlo_val : (row.b3 + row.c * ((2 ^ 4 : ℕ) : Fp)).val
      = row.b3.val + row.c.val * 2 ^ 4 := val_limb2 4 hlo_sum
  have hlo_lt : (row.b3 + row.c * ((2 ^ 4 : ℕ) : Fp)).val < 2 ^ 254 := by rw [hlo_val]; omega
  have hcanon : row.d0 = 1 → (row.b3 + row.c * ((2 ^ 4 : ℕ) : Fp)).val < tPNat := by
    intro h1
    have hc130 : row.c.val < 2 ^ 130 := by
      have hz : row.z13C = 0 := by
        rcases mul_eq_zero.mp heq3 with h | h
        · exact absurd (h1 ▸ h) one_ne_zero
        · exact h
      rw [hz13C] at hz
      have := natCast_eq_zero
        (lt_of_le_of_lt (Nat.div_le_self _ _) (lt_trans hc_lt (by norm_num [PALLAS_BASE_CARD]))) hz
      omega
    have hb3cP_val : row.b3C'.val
        = (row.b3 + row.c * ((2 ^ 4 : ℕ) : Fp)).val + 2 ^ 140 - tPNat := by
      rw [hb3cP]; exact val_shift 140 (by rw [hlo_val]; omega) (by rw [hlo_val]; omega)
    have hb3cP_lt : row.b3C'.val < 2 ^ 140 := by
      have hz : row.z14B3C' = 0 := by
        rcases mul_eq_zero.mp heq4 with h | h
        · exact absurd (h1 ▸ h) one_ne_zero
        · exact h
      obtain ⟨lo, hlo, hdec⟩ := hzbDec
      rw [hz, mul_zero, _root_.add_zero] at hdec
      rw [hdec, ZMod.val_natCast_of_lt (lt_trans hlo (by norm_num [PALLAS_BASE_CARD]))]
      exact hlo
    omega
  have hrecL : row.pkdX = (row.b3 + row.c * ((2 ^ 4 : ℕ) : Fp))
      + row.d0 * ((2 ^ 254 : ℕ) : Fp) := by linear_combination -heq1
  obtain ⟨_, hlo_eq, hd0_eq⟩ := canonical_top_decomp hrecL hlo_lt hd0 hcanon
  have hmod : bitrange row.pkdX.val 0 254 = row.pkdX.val % 2 ^ 254 := by simp [bitrange]
  have hb3_eq : row.b3.val = bitrange row.pkdX.val 0 4 := by
    have h1 : row.b3.val = bitrange (row.b3 + row.c * ((2 ^ 4 : ℕ) : Fp)).val 0 4 := by
      simp only [bitrange, pow_zero, Nat.div_one, hlo_val]; omega
    rw [h1, hlo_eq, hmod, bitrange_mod (by norm_num : 0 + 4 ≤ 254)]
  have hc_eq : row.c.val = bitrange row.pkdX.val 4 250 := by
    have h1 : row.c.val = bitrange (row.b3 + row.c * ((2 ^ 4 : ℕ) : Fp)).val 4 250 := by
      simp only [bitrange, hlo_val]; omega
    rw [h1, hlo_eq, hmod, bitrange_mod (by norm_num : 4 + 250 ≤ 254)]
  exact ⟨hb3_eq, hc_eq, hd0_eq, fun h1 => by
    rcases mul_eq_zero.mp heq4 with h | h
    · exact absurd (h1 ▸ h) one_ne_zero
    · exact h⟩

/-- Row-level completeness direction. -/
theorem eqs_of_spec (row : Row Fp) (hAss : Assumptions row) (hSpec : Spec row) :
    (row.b3 + row.c * ((2 ^ 4 : ℕ) : Fp) + row.d0 * ((2 ^ 254 : ℕ) : Fp)
      - row.pkdX = 0) ∧
    (row.b3 + row.c * ((2 ^ 4 : ℕ) : Fp) + ((2 ^ 140 : ℕ) : Fp) - tP - row.b3C' = 0) ∧
    row.d0 * row.z13C = 0 ∧ row.d0 * row.z14B3C' = 0 := by
  obtain ⟨_, hc_lt, hb3_lt, hb3cP, hz13C, _⟩ := hAss
  obtain ⟨hb3_val, hc_val, hd0_val, hzbZero⟩ := hSpec
  have hp := pallasBaseCard_eq
  have htpsmall : tPNat < 2 ^ 130 := by norm_num [tPNat]
  have hpkdX : row.pkdX.val < 2 ^ 255 :=
    lt_trans (ZMod.val_lt row.pkdX) (by norm_num [PALLAS_BASE_CARD])
  have hb3_eq : row.b3 = ((bitrange row.pkdX.val 0 4 : ℕ) : Fp) := by
    rw [← hb3_val]; exact (ZMod.natCast_rightInverse row.b3).symm
  have hc_eq : row.c = ((bitrange row.pkdX.val 4 250 : ℕ) : Fp) := by
    rw [← hc_val]; exact (ZMod.natCast_rightInverse row.c).symm
  have hd0_eq : row.d0 = ((bitrange row.pkdX.val 254 1 : ℕ) : Fp) := by
    rw [← hd0_val]; exact (ZMod.natCast_rightInverse row.d0).symm
  have hd0cases := show bitrange row.pkdX.val 254 1 = 0 ∨ bitrange row.pkdX.val 254 1 = 1 from by
    have := bitrange_lt row.pkdX.val 254 1; omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- reconstruction
    have hdec : row.pkdX.val = bitrange row.pkdX.val 0 4
        + 2 ^ 4 * bitrange row.pkdX.val 4 250 + 2 ^ 254 * bitrange row.pkdX.val 254 1 := by
      simp only [bitrange, pow_zero, Nat.div_one]; omega
    have hpkd_eq : row.pkdX = ((bitrange row.pkdX.val 0 4 : ℕ) : Fp)
        + ((bitrange row.pkdX.val 4 250 : ℕ) : Fp) * ((2 ^ 4 : ℕ) : Fp)
        + ((bitrange row.pkdX.val 254 1 : ℕ) : Fp) * ((2 ^ 254 : ℕ) : Fp) := by
      conv_lhs => rw [← ZMod.natCast_rightInverse row.pkdX, hdec]
      push_cast; ring
    rw [hb3_eq, hc_eq, hd0_eq]; linear_combination -hpkd_eq
  · -- prime
    rw [hb3cP]; ring
  · -- d0·z13C = 0
    rcases hd0cases with h | h
    · rw [hd0_eq, h]; simp
    · rw [hz13C, hc_val,
        show bitrange row.pkdX.val 4 250 / 2 ^ 130 = bitrange row.pkdX.val 134 120 from
          bitrange_div_pow row.pkdX.val 4 130 120,
        high_bit_high_zero (ZMod.val_lt row.pkdX) h (by norm_num) (by norm_num)]
      simp
  · -- d0·z14B3C' = 0
    rcases hd0cases with h | h
    · rw [hd0_eq, h]; simp
    · rw [hzbZero (by rw [hd0_eq, h]; norm_num)]; simp

end PkdCanonicity.Gate

namespace ValueCanonicity.Gate

structure Row (F : Type) where
  value : F
  d2 : F
  d3 : F
  e0 : F
deriving ProvableStruct

/-- Rely-conditions: the three sub-pieces are range-checked. -/
def Assumptions (row : Row Fp) : Prop :=
  row.d2.val < 2 ^ 8 ∧ row.d3.val < 2 ^ 50 ∧ row.e0.val < 2 ^ 6

/-- The gate's payoff: `value` is a canonical 64-bit value with `d2`/`d3`/`e0` its slices. -/
def Spec (row : Row Fp) : Prop :=
  row.value.val < 2 ^ 64 ∧
    row.d2.val = bitrange row.value.val 0 8 ∧
    row.d3.val = bitrange row.value.val 8 50 ∧
    row.e0.val = bitrange row.value.val 58 6

/-- Row-level payoff (extracted from `soundness` for reuse by the halo2-native port):
the gate equation plus the rely-conditions pin the canonical decomposition. -/
theorem spec_of_eq (row : Row Fp) (hAss : Assumptions row)
    (heq : row.d2 + row.d3 * ((2 ^ 8 : ℕ) : Fp) + row.e0 * ((2 ^ 58 : ℕ) : Fp)
      - row.value = 0) : Spec row := by
  obtain ⟨hd2_lt, hd3_lt, he0_lt⟩ := hAss
  have hp := pallasBaseCard_eq
  have hbnd : row.d2.val + row.d3.val * 2 ^ 8 + row.e0.val * 2 ^ 58
      < PALLAS_BASE_CARD := by omega
  have hval : row.value.val
      = row.d2.val + row.d3.val * 2 ^ 8 + row.e0.val * 2 ^ 58 := by
    have hcast : row.value
        = ((row.d2.val + row.d3.val * 2 ^ 8 + row.e0.val * 2 ^ 58 : ℕ) : Fp) := by
      have hrec : row.value = row.d2 + row.d3 * ((2 ^ 8 : ℕ) : Fp)
          + row.e0 * ((2 ^ 58 : ℕ) : Fp) := by linear_combination -heq
      rw [hrec]; push_cast
      rw [ZMod.natCast_rightInverse row.d2, ZMod.natCast_rightInverse row.d3,
        ZMod.natCast_rightInverse row.e0]
    rw [hcast, ZMod.val_natCast_of_lt hbnd]
  refine ⟨by rw [hval]; omega, ?_, ?_, ?_⟩
  · simp only [bitrange, pow_zero, Nat.div_one, hval]; omega
  · simp only [bitrange, hval]; omega
  · simp only [bitrange, hval]; omega

end ValueCanonicity.Gate

namespace RhoCanonicity.Gate

structure Row (F : Type) where
  rho : F
  e1 : F
  g0 : F
  f : F
  e1F' : F
  z13F : F
  z14E1F' : F
deriving ProvableStruct

/-- Rely-conditions from the surrounding lookups (same shape as `pk_d`). -/
def Assumptions (row : Row Fp) : Prop :=
  IsBool row.g0 ∧
    row.f.val < 2 ^ 250 ∧
    row.e1.val < 2 ^ 4 ∧
    row.e1F' = row.e1 + row.f * ((2 ^ 4 : ℕ) : Fp) + ((2 ^ 140 : ℕ) : Fp) - tP ∧
    row.z13F = ((row.f.val / 2 ^ 130 : ℕ) : Fp) ∧
    ∃ lo : ℕ, lo < 2 ^ 140 ∧ row.e1F' = ((lo : ℕ) : Fp) + ((2 ^ 140 : ℕ) : Fp) * row.z14E1F'

/-- The gate's payoff: `e1`/`f`/`g0` are the canonical bit slices of `rho`. -/
def Spec (row : Row Fp) : Prop :=
  row.e1.val = bitrange row.rho.val 0 4 ∧
    row.f.val = bitrange row.rho.val 4 250 ∧
    row.g0.val = bitrange row.rho.val 254 1 ∧
    (row.g0 = 1 → row.z14E1F' = 0)

/-- Row-level payoff (extracted from `soundness` for the halo2-native port). -/
theorem spec_of_eqs (row : Row Fp) (hAss : Assumptions row)
    (heq1 : row.e1 + row.f * ((2 ^ 4 : ℕ) : Fp) + row.g0 * ((2 ^ 254 : ℕ) : Fp)
      - row.rho = 0)
    (heq3 : row.g0 * row.z13F = 0) (heq4 : row.g0 * row.z14E1F' = 0) : Spec row := by
  obtain ⟨hg0, hf_lt, he1_lt, he1fP, hz13F, hzeDec⟩ := hAss
  have hp := pallasBaseCard_eq
  have htpsmall : tPNat < 2 ^ 130 := by norm_num [tPNat]
  have hlo_sum : row.e1.val + row.f.val * 2 ^ 4 < PALLAS_BASE_CARD := by omega
  have hlo_val : (row.e1 + row.f * ((2 ^ 4 : ℕ) : Fp)).val
      = row.e1.val + row.f.val * 2 ^ 4 := val_limb2 4 hlo_sum
  have hlo_lt : (row.e1 + row.f * ((2 ^ 4 : ℕ) : Fp)).val < 2 ^ 254 := by rw [hlo_val]; omega
  have hcanon : row.g0 = 1 → (row.e1 + row.f * ((2 ^ 4 : ℕ) : Fp)).val < tPNat := by
    intro h1
    have hf130 : row.f.val < 2 ^ 130 := by
      have hz : row.z13F = 0 := by
        rcases mul_eq_zero.mp heq3 with h | h
        · exact absurd (h1 ▸ h) one_ne_zero
        · exact h
      rw [hz13F] at hz
      have := natCast_eq_zero
        (lt_of_le_of_lt (Nat.div_le_self _ _) (lt_trans hf_lt (by norm_num [PALLAS_BASE_CARD]))) hz
      omega
    have he1fP_val : row.e1F'.val
        = (row.e1 + row.f * ((2 ^ 4 : ℕ) : Fp)).val + 2 ^ 140 - tPNat := by
      rw [he1fP]; exact val_shift 140 (by rw [hlo_val]; omega) (by rw [hlo_val]; omega)
    have he1fP_lt : row.e1F'.val < 2 ^ 140 := by
      have hz : row.z14E1F' = 0 := by
        rcases mul_eq_zero.mp heq4 with h | h
        · exact absurd (h1 ▸ h) one_ne_zero
        · exact h
      obtain ⟨lo, hlo, hdec⟩ := hzeDec
      rw [hz, mul_zero, _root_.add_zero] at hdec
      rw [hdec, ZMod.val_natCast_of_lt (lt_trans hlo (by norm_num [PALLAS_BASE_CARD]))]
      exact hlo
    omega
  have hrecL : row.rho = (row.e1 + row.f * ((2 ^ 4 : ℕ) : Fp))
      + row.g0 * ((2 ^ 254 : ℕ) : Fp) := by linear_combination -heq1
  obtain ⟨_, hlo_eq, hg0_eq⟩ := canonical_top_decomp hrecL hlo_lt hg0 hcanon
  have hmod : bitrange row.rho.val 0 254 = row.rho.val % 2 ^ 254 := by simp [bitrange]
  have he1_eq : row.e1.val = bitrange row.rho.val 0 4 := by
    have h1 : row.e1.val = bitrange (row.e1 + row.f * ((2 ^ 4 : ℕ) : Fp)).val 0 4 := by
      simp only [bitrange, pow_zero, Nat.div_one, hlo_val]; omega
    rw [h1, hlo_eq, hmod, bitrange_mod (by norm_num : 0 + 4 ≤ 254)]
  have hf_eq : row.f.val = bitrange row.rho.val 4 250 := by
    have h1 : row.f.val = bitrange (row.e1 + row.f * ((2 ^ 4 : ℕ) : Fp)).val 4 250 := by
      simp only [bitrange, hlo_val]; omega
    rw [h1, hlo_eq, hmod, bitrange_mod (by norm_num : 4 + 250 ≤ 254)]
  exact ⟨he1_eq, hf_eq, hg0_eq, fun h1 => by
    rcases mul_eq_zero.mp heq4 with h | h
    · exact absurd (h1 ▸ h) one_ne_zero
    · exact h⟩

/-- Row-level completeness direction. -/
theorem eqs_of_spec (row : Row Fp) (hAss : Assumptions row) (hSpec : Spec row) :
    (row.e1 + row.f * ((2 ^ 4 : ℕ) : Fp) + row.g0 * ((2 ^ 254 : ℕ) : Fp)
      - row.rho = 0) ∧
    (row.e1 + row.f * ((2 ^ 4 : ℕ) : Fp) + ((2 ^ 140 : ℕ) : Fp) - tP - row.e1F' = 0) ∧
    row.g0 * row.z13F = 0 ∧ row.g0 * row.z14E1F' = 0 := by
  obtain ⟨_, hf_lt, he1_lt, he1fP, hz13F, _⟩ := hAss
  obtain ⟨he1_val, hf_val, hg0_val, hzeZero⟩ := hSpec
  have hp := pallasBaseCard_eq
  have htpsmall : tPNat < 2 ^ 130 := by norm_num [tPNat]
  have hrhoX : row.rho.val < 2 ^ 255 :=
    lt_trans (ZMod.val_lt row.rho) (by norm_num [PALLAS_BASE_CARD])
  have he1_eq : row.e1 = ((bitrange row.rho.val 0 4 : ℕ) : Fp) := by
    rw [← he1_val]; exact (ZMod.natCast_rightInverse row.e1).symm
  have hf_eq : row.f = ((bitrange row.rho.val 4 250 : ℕ) : Fp) := by
    rw [← hf_val]; exact (ZMod.natCast_rightInverse row.f).symm
  have hg0_eq : row.g0 = ((bitrange row.rho.val 254 1 : ℕ) : Fp) := by
    rw [← hg0_val]; exact (ZMod.natCast_rightInverse row.g0).symm
  have hg0cases := show bitrange row.rho.val 254 1 = 0 ∨ bitrange row.rho.val 254 1 = 1 from by
    have := bitrange_lt row.rho.val 254 1; omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hdec : row.rho.val = bitrange row.rho.val 0 4
        + 2 ^ 4 * bitrange row.rho.val 4 250 + 2 ^ 254 * bitrange row.rho.val 254 1 := by
      simp only [bitrange, pow_zero, Nat.div_one]; omega
    have hrho_eq : row.rho = ((bitrange row.rho.val 0 4 : ℕ) : Fp)
        + ((bitrange row.rho.val 4 250 : ℕ) : Fp) * ((2 ^ 4 : ℕ) : Fp)
        + ((bitrange row.rho.val 254 1 : ℕ) : Fp) * ((2 ^ 254 : ℕ) : Fp) := by
      conv_lhs => rw [← ZMod.natCast_rightInverse row.rho, hdec]
      push_cast; ring
    rw [he1_eq, hf_eq, hg0_eq]; linear_combination -hrho_eq
  · rw [he1fP]; ring
  · rcases hg0cases with h | h
    · rw [hg0_eq, h]; simp
    · rw [hz13F, hf_val,
        show bitrange row.rho.val 4 250 / 2 ^ 130 = bitrange row.rho.val 134 120 from
          bitrange_div_pow row.rho.val 4 130 120,
        high_bit_high_zero (ZMod.val_lt row.rho) h (by norm_num) (by norm_num)]
      simp
  · rcases hg0cases with h | h
    · rw [hg0_eq, h]; simp
    · rw [hzeZero (by rw [hg0_eq, h]; norm_num)]; simp

end RhoCanonicity.Gate

namespace PsiCanonicity.Gate

structure Row (F : Type) where
  psi : F
  h0 : F
  g1 : F
  h1 : F
  g2 : F
  g1G2' : F
  z13G : F
  z13G1G2' : F
deriving ProvableStruct

/-- Rely-conditions from the surrounding lookups: the inner limb is `g1 + g2·2^9`, `h0` is
the 5-bit field above it, `h1` is Boolean, `g1G2'` is the canonicity shift of the inner
limb, and `z13G`/`z13G1G2'` are the running-sum tails of the inner limb / its shift. -/
def Assumptions (row : Row Fp) : Prop :=
  IsBool row.h1 ∧
    row.g1.val < 2 ^ 9 ∧
    row.g2.val < 2 ^ 240 ∧
    row.h0.val < 2 ^ 5 ∧
    row.g1G2' = row.g1 + row.g2 * ((2 ^ 9 : ℕ) : Fp) + ((2 ^ 130 : ℕ) : Fp) - tP ∧
    row.z13G = ((row.g1.val + row.g2.val * 2 ^ 9) / 2 ^ 129 : ℕ) ∧
    ∃ lo : ℕ, lo < 2 ^ 130 ∧ row.g1G2' = ((lo : ℕ) : Fp) + ((2 ^ 130 : ℕ) : Fp) * row.z13G1G2'

/-- The gate's payoff: `g1`/`g2`/`h0`/`h1` are the canonical bit slices of `psi`. -/
def Spec (row : Row Fp) : Prop :=
  row.g1.val = bitrange row.psi.val 0 9 ∧
    row.g2.val = bitrange row.psi.val 9 240 ∧
    row.h0.val = bitrange row.psi.val 249 5 ∧
    row.h1.val = bitrange row.psi.val 254 1 ∧
    (row.h1 = 1 → row.z13G1G2' = 0)

/-- Row-level payoff (extracted from `soundness` for the halo2-native port). -/
theorem spec_of_eqs (row : Row Fp) (hAss : Assumptions row)
    (heq1 : row.g1 + row.g2 * ((2 ^ 9 : ℕ) : Fp) + row.h0 * ((2 ^ 249 : ℕ) : Fp)
      + row.h1 * ((2 ^ 254 : ℕ) : Fp) - row.psi = 0)
    (heq3 : row.h1 * row.h0 = 0) (heq4 : row.h1 * row.z13G = 0)
    (heq5 : row.h1 * row.z13G1G2' = 0) : Spec row := by
  obtain ⟨hh1, hg1_lt, hg2_lt, hh0_lt, hg1g2P, hz13G, hzgDec⟩ := hAss
  have hp := pallasBaseCard_eq
  have htpsmall : tPNat < 2 ^ 130 := by norm_num [tPNat]
  -- inner limb `g1 + g2·2^9`
  have hin_sum : row.g1.val + row.g2.val * 2 ^ 9 < PALLAS_BASE_CARD := by omega
  have hin_val : (row.g1 + row.g2 * ((2 ^ 9 : ℕ) : Fp)).val
      = row.g1.val + row.g2.val * 2 ^ 9 := val_limb2 9 hin_sum
  have hin_lt : row.g1.val + row.g2.val * 2 ^ 9 < 2 ^ 249 := by omega
  -- low 254-bit limb `inner + h0·2^249`
  have hlo_sum : (row.g1 + row.g2 * ((2 ^ 9 : ℕ) : Fp)).val + row.h0.val * 2 ^ 249
      < PALLAS_BASE_CARD := by rw [hin_val]; omega
  have hlo_val : ((row.g1 + row.g2 * ((2 ^ 9 : ℕ) : Fp)) + row.h0 * ((2 ^ 249 : ℕ) : Fp)).val
      = (row.g1.val + row.g2.val * 2 ^ 9) + row.h0.val * 2 ^ 249 := by
    rw [val_limb2 249 hlo_sum, hin_val]
  have hlo_lt : ((row.g1 + row.g2 * ((2 ^ 9 : ℕ) : Fp)) + row.h0 * ((2 ^ 249 : ℕ) : Fp)).val
      < 2 ^ 254 := by rw [hlo_val]; omega
  have hcanon : row.h1 = 1 →
      ((row.g1 + row.g2 * ((2 ^ 9 : ℕ) : Fp)) + row.h0 * ((2 ^ 249 : ℕ) : Fp)).val
        < tPNat := by
    intro h1
    have hh0z : row.h0 = 0 := by
      rcases mul_eq_zero.mp heq3 with h | h
      · exact absurd (h1 ▸ h) one_ne_zero
      · exact h
    have hin130 : row.g1.val + row.g2.val * 2 ^ 9 < 2 ^ 130 := by
      have hz : row.z13G = 0 := by
        rcases mul_eq_zero.mp heq4 with h | h
        · exact absurd (h1 ▸ h) one_ne_zero
        · exact h
      rw [hz13G] at hz
      have := natCast_eq_zero
        (lt_of_le_of_lt (Nat.div_le_self _ _) (lt_trans hin_lt (by norm_num [PALLAS_BASE_CARD]))) hz
      omega
    have hgP_val : row.g1G2'.val
        = (row.g1 + row.g2 * ((2 ^ 9 : ℕ) : Fp)).val + 2 ^ 130 - tPNat := by
      rw [hg1g2P]; exact val_shift 130 (by rw [hin_val]; omega) (by rw [hin_val]; omega)
    have hgP_lt : row.g1G2'.val < 2 ^ 130 := by
      have hz : row.z13G1G2' = 0 := by
        rcases mul_eq_zero.mp heq5 with h | h
        · exact absurd (h1 ▸ h) one_ne_zero
        · exact h
      obtain ⟨lo, hlo, hdec⟩ := hzgDec
      rw [hz, mul_zero, _root_.add_zero] at hdec
      rw [hdec, ZMod.val_natCast_of_lt (lt_trans hlo (by norm_num [PALLAS_BASE_CARD]))]
      exact hlo
    rw [hlo_val, hh0z, ZMod.val_zero]; rw [hin_val] at hgP_val; omega
  have hrecL : row.psi
      = ((row.g1 + row.g2 * ((2 ^ 9 : ℕ) : Fp)) + row.h0 * ((2 ^ 249 : ℕ) : Fp))
        + row.h1 * ((2 ^ 254 : ℕ) : Fp) := by linear_combination -heq1
  obtain ⟨_, hlo_eq, hh1_eq⟩ := canonical_top_decomp hrecL hlo_lt hh1 hcanon
  have hmod : bitrange row.psi.val 0 254 = row.psi.val % 2 ^ 254 := by simp [bitrange]
  -- inner limb is the low 249 bits
  have hin_eq : row.g1.val + row.g2.val * 2 ^ 9 = bitrange row.psi.val 0 249 := by
    have h1 : (row.g1.val + row.g2.val * 2 ^ 9)
        = bitrange ((row.g1 + row.g2 * ((2 ^ 9 : ℕ) : Fp))
            + row.h0 * ((2 ^ 249 : ℕ) : Fp)).val 0 249 := by
      simp only [bitrange, pow_zero, Nat.div_one, hlo_val]; omega
    rw [h1, hlo_eq, hmod, bitrange_mod (by norm_num : 0 + 249 ≤ 254)]
  have hh0_eq : row.h0.val = bitrange row.psi.val 249 5 := by
    have h1 : row.h0.val = bitrange ((row.g1 + row.g2 * ((2 ^ 9 : ℕ) : Fp))
        + row.h0 * ((2 ^ 249 : ℕ) : Fp)).val 249 5 := by
      simp only [bitrange, hlo_val]; omega
    rw [h1, hlo_eq, hmod, bitrange_mod (by norm_num : 249 + 5 ≤ 254)]
  have hg1_eq : row.g1.val = bitrange row.psi.val 0 9 := by
    have h1 : row.g1.val = bitrange (row.g1.val + row.g2.val * 2 ^ 9) 0 9 := by
      simp only [bitrange, pow_zero, Nat.div_one]; omega
    rw [h1, hin_eq]
    have : bitrange row.psi.val 0 249 = row.psi.val % 2 ^ 249 := by simp [bitrange]
    rw [this, bitrange_mod (by norm_num : 0 + 9 ≤ 249)]
  have hg2_eq : row.g2.val = bitrange row.psi.val 9 240 := by
    have h1 : row.g2.val = bitrange (row.g1.val + row.g2.val * 2 ^ 9) 9 240 := by
      simp only [bitrange]; omega
    rw [h1, hin_eq]
    have : bitrange row.psi.val 0 249 = row.psi.val % 2 ^ 249 := by simp [bitrange]
    rw [this, bitrange_mod (by norm_num : 9 + 240 ≤ 249)]
  exact ⟨hg1_eq, hg2_eq, hh0_eq, hh1_eq, fun h1 => by
    rcases mul_eq_zero.mp heq5 with h | h
    · exact absurd (h1 ▸ h) one_ne_zero
    · exact h⟩

/-- Row-level completeness direction. -/
theorem eqs_of_spec (row : Row Fp) (hAss : Assumptions row) (hSpec : Spec row) :
    (row.g1 + row.g2 * ((2 ^ 9 : ℕ) : Fp) + row.h0 * ((2 ^ 249 : ℕ) : Fp)
      + row.h1 * ((2 ^ 254 : ℕ) : Fp) - row.psi = 0) ∧
    (row.g1 + row.g2 * ((2 ^ 9 : ℕ) : Fp) + ((2 ^ 130 : ℕ) : Fp) - tP
      - row.g1G2' = 0) ∧
    row.h1 * row.h0 = 0 ∧ row.h1 * row.z13G = 0 ∧ row.h1 * row.z13G1G2' = 0 := by
  obtain ⟨_, hg1_lt, hg2_lt, hh0_lt, hg1g2P, hz13G, _⟩ := hAss
  obtain ⟨hg1_val, hg2_val, hh0_val, hh1_val, hzgZero⟩ := hSpec
  have hp := pallasBaseCard_eq
  have htpsmall : tPNat < 2 ^ 130 := by norm_num [tPNat]
  have hpsiX : row.psi.val < 2 ^ 255 :=
    lt_trans (ZMod.val_lt row.psi) (by norm_num [PALLAS_BASE_CARD])
  have hg1_eq : row.g1 = ((bitrange row.psi.val 0 9 : ℕ) : Fp) := by
    rw [← hg1_val]; exact (ZMod.natCast_rightInverse row.g1).symm
  have hg2_eq : row.g2 = ((bitrange row.psi.val 9 240 : ℕ) : Fp) := by
    rw [← hg2_val]; exact (ZMod.natCast_rightInverse row.g2).symm
  have hh0_eq : row.h0 = ((bitrange row.psi.val 249 5 : ℕ) : Fp) := by
    rw [← hh0_val]; exact (ZMod.natCast_rightInverse row.h0).symm
  have hh1_eq : row.h1 = ((bitrange row.psi.val 254 1 : ℕ) : Fp) := by
    rw [← hh1_val]; exact (ZMod.natCast_rightInverse row.h1).symm
  -- inner limb is the low 249 bits
  have hin_eq : row.g1.val + row.g2.val * 2 ^ 9 = bitrange row.psi.val 0 249 := by
    rw [hg1_val, hg2_val]; have := bitrange_add row.psi.val 0 9 240; norm_num at this; omega
  have hh1cases := show bitrange row.psi.val 254 1 = 0 ∨ bitrange row.psi.val 254 1 = 1 from by
    have := bitrange_lt row.psi.val 254 1; omega
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have hdec : row.psi.val = bitrange row.psi.val 0 9
        + 2 ^ 9 * bitrange row.psi.val 9 240 + 2 ^ 249 * bitrange row.psi.val 249 5
        + 2 ^ 254 * bitrange row.psi.val 254 1 := by
      simp only [bitrange, pow_zero, Nat.div_one]; omega
    have hpsi_eq : row.psi = ((bitrange row.psi.val 0 9 : ℕ) : Fp)
        + ((bitrange row.psi.val 9 240 : ℕ) : Fp) * ((2 ^ 9 : ℕ) : Fp)
        + ((bitrange row.psi.val 249 5 : ℕ) : Fp) * ((2 ^ 249 : ℕ) : Fp)
        + ((bitrange row.psi.val 254 1 : ℕ) : Fp) * ((2 ^ 254 : ℕ) : Fp) := by
      conv_lhs => rw [← ZMod.natCast_rightInverse row.psi, hdec]
      push_cast; ring
    rw [hg1_eq, hg2_eq, hh0_eq, hh1_eq]; linear_combination -hpsi_eq
  · rw [hg1g2P]; ring
  · -- h1·h0 = 0
    rcases hh1cases with h | h
    · rw [hh1_eq, h]; simp
    · rw [hh0_eq, high_bit_high_zero (ZMod.val_lt row.psi) h (by norm_num) (by norm_num)]; simp
  · -- h1·z13G = 0
    rcases hh1cases with h | h
    · rw [hh1_eq, h]; simp
    · rw [hz13G, hin_eq,
        show bitrange row.psi.val 0 249 / 2 ^ 129 = bitrange row.psi.val 129 120 from
          bitrange_div_pow row.psi.val 0 129 120]
      have hlow : bitrange row.psi.val 0 254 < tPNat :=
        high_bit_low_lt_tP (ZMod.val_lt row.psi) h (by norm_num)
      have hzero : bitrange row.psi.val 129 120 = 0 := by
        rw [← bitrange_mod (n := row.psi.val) (s := 129) (len := 120) (m := 254)
          (by norm_num)]
        simp only [bitrange]
        have hlt : row.psi.val % 2 ^ 254 < 2 ^ 129 := by
          have hlow' := hlow
          simp only [bitrange, pow_zero, Nat.div_one] at hlow'
          exact lt_trans hlow' (by norm_num [tPNat])
        rw [Nat.div_eq_of_lt hlt]
        simp
      rw [hzero]
      simp
  · -- h1·z13G1G2' = 0
    rcases hh1cases with h | h
    · rw [hh1_eq, h]; simp
    · rw [hzgZero (by rw [hh1_eq, h]; norm_num)]; simp

end PsiCanonicity.Gate

namespace YCanonicity.Gate

structure Row (F : Type) where
  y : F
  lsb : F
  k0 : F
  k2 : F
  k3 : F
  j : F
  z1J : F
  z13J : F
  j' : F
  z13J' : F
deriving ProvableStruct

/-- Rely-conditions from the surrounding lookups, mirroring `GdCanonicity.Gate` with the
extra sign-bit split of the low limb: `lsb` is Boolean (the 1-bit sign cell), `k0`/`k2` are
range-checked, `j` is the `< 2^250` low limb, `j'` is its canonicity shift, `z1J`/`z13J` are
the exact 1- and 13-word running-sum tails of `j` (supplied by the surrounding running sum), and
`z13J'` is the *partial* 13-word telescoped tail of `j'`. The bit slices and `lsb` itself are
**derived**, not assumed — that is the `Spec`. -/
def Assumptions (row : Row Fp) : Prop :=
  IsBool row.lsb ∧
    row.j.val < 2 ^ 250 ∧
    row.k0.val < 2 ^ 9 ∧
    row.k2.val < 2 ^ 4 ∧
    row.j' = row.j + ((2 ^ 130 : ℕ) : Fp) - tP ∧
    row.z1J.val = row.j.val / 2 ^ 10 ∧
    row.z13J.val = row.j.val / 2 ^ 130 ∧
    ∃ lo : ℕ, lo < 2 ^ 130 ∧ row.j' = ((lo : ℕ) : Fp) + ((2 ^ 130 : ℕ) : Fp) * row.z13J'

/-- The gate's payoff: `lsb` is the low (sign) bit of `y`, and the support cells are the
canonical bit slices of `y` (`j`/`k0`/`k2`/`k3`). -/
def Spec (row : Row Fp) : Prop :=
  IsLowBit row.y row.lsb ∧
    row.j.val = bitrange row.y.val 0 250 ∧
    row.k0.val = bitrange row.y.val 1 9 ∧
    row.k2.val = bitrange row.y.val 250 4 ∧
    row.k3.val = bitrange row.y.val 254 1 ∧
    (row.k3 = 1 → row.z13J' = 0)

/-- Row-level payoff (extracted from `soundness` for the halo2-native port). -/
theorem spec_of_eqs (row : Row Fp) (hAss : Assumptions row)
    (hk3b : IsBool row.k3)
    (heq2 : row.j - (row.lsb + row.k0 * 2 + row.z1J * 1024) = 0)
    (heq3 : row.y - (row.j + row.k2 * ((2 ^ 250 : ℕ) : Fp)
      + row.k3 * ((2 ^ 254 : ℕ) : Fp)) = 0)
    (heq5 : row.k3 * row.k2 = 0) (heq7 : row.k3 * row.z13J' = 0) : Spec row := by
  obtain ⟨hlsb_bool, hj_lt, hk0_lt, hk2_lt, hj', hz1J, hz13J, hzjDec⟩ := hAss
  have hp := pallasBaseCard_eq
  have htpsmall : tPNat < 2 ^ 130 := by norm_num [tPNat]
  -- canonical top-bit decomposition of `y` (mirrors `GdCanonicity.Gate`, with `j`/`k2`/`k3`
  -- for `a`/`b0`/`b1`)
  have hlo_sum : row.j.val + row.k2.val * 2 ^ 250 < PALLAS_BASE_CARD := by omega
  have hlo_val : (row.j + row.k2 * ((2 ^ 250 : ℕ) : Fp)).val
      = row.j.val + row.k2.val * 2 ^ 250 := val_limb2 250 hlo_sum
  have hlo_lt : (row.j + row.k2 * ((2 ^ 250 : ℕ) : Fp)).val < 2 ^ 254 := by
    rw [hlo_val]; omega
  have hcanon : row.k3 = 1 →
      (row.j + row.k2 * ((2 ^ 250 : ℕ) : Fp)).val < tPNat := by
    intro h1
    have hk2z : row.k2 = 0 := by
      rcases mul_eq_zero.mp heq5 with h | h
      · exact absurd (h1 ▸ h) one_ne_zero
      · exact h
    have hj'_val : row.j'.val = row.j.val + 2 ^ 130 - tPNat := by
      rw [hj']; exact val_shift 130 (by omega) (by omega)
    have hj'_lt : row.j'.val < 2 ^ 130 := by
      have hz : row.z13J' = 0 := by
        rcases mul_eq_zero.mp heq7 with h | h
        · exact absurd (h1 ▸ h) one_ne_zero
        · exact h
      obtain ⟨lo, hlo, hdec⟩ := hzjDec
      rw [hz, mul_zero, _root_.add_zero] at hdec
      rw [hdec, ZMod.val_natCast_of_lt (lt_trans hlo (by norm_num [PALLAS_BASE_CARD]))]
      exact hlo
    -- `simp` first: `omega` exceeds the recursion limit on the raw `0 * 2 ^ 250` goal
    rw [hlo_val, hk2z, ZMod.val_zero]; simp only [zero_mul, add_zero]; omega
  have hrecL : row.y = (row.j + row.k2 * ((2 ^ 250 : ℕ) : Fp))
      + row.k3 * ((2 ^ 254 : ℕ) : Fp) := by linear_combination heq3
  obtain ⟨_, hlo_eq, hk3_eq⟩ := canonical_top_decomp hrecL hlo_lt hk3b hcanon
  have hmod : bitrange row.y.val 0 254 = row.y.val % 2 ^ 254 := by simp [bitrange]
  have hj_val : row.j.val = bitrange row.y.val 0 250 := by
    have h1 : row.j.val
        = bitrange (row.j + row.k2 * ((2 ^ 250 : ℕ) : Fp)).val 0 250 := by
      simp only [bitrange, pow_zero, Nat.div_one, hlo_val]; omega
    rw [h1, hlo_eq, hmod, bitrange_mod (by norm_num : 0 + 250 ≤ 254)]
  have hk2_val : row.k2.val = bitrange row.y.val 250 4 := by
    have h1 : row.k2.val
        = bitrange (row.j + row.k2 * ((2 ^ 250 : ℕ) : Fp)).val 250 4 := by
      simp only [bitrange, hlo_val]; omega
    rw [h1, hlo_eq, hmod, bitrange_mod (by norm_num : 250 + 4 ≤ 254)]
  -- sign-bit extraction off `j = lsb + 2·k0 + 1024·z1J`, entirely in ℕ
  have hjsum : row.j
      = (((row.lsb.val + row.k0.val * 2 + row.z1J.val * 1024 : ℕ)) : Fp) := by
    have hcast : row.lsb + row.k0 * 2 + row.z1J * 1024
        = (((row.lsb.val + row.k0.val * 2 + row.z1J.val * 1024 : ℕ)) : Fp) := by
      push_cast
      rw [ZMod.natCast_rightInverse row.lsb, ZMod.natCast_rightInverse row.k0,
        ZMod.natCast_rightInverse row.z1J]
    linear_combination heq2 + hcast
  have hz1J_le : row.z1J.val * 2 ^ 10 ≤ row.j.val := by
    rw [hz1J]; exact Nat.div_mul_le_self _ _
  have hlsb_lt : row.lsb.val < 2 := IsBool.val_lt_two hlsb_bool
  have hjval2 : row.j.val
      = row.lsb.val + row.k0.val * 2 + row.z1J.val * 1024 := by
    rw [hjsum]
    refine ZMod.val_natCast_of_lt ?_
    norm_num [PALLAS_BASE_CARD] at hj_lt ⊢
    omega
  have hlsb_val : row.lsb.val = row.j.val % 2 := by omega
  have hk0_val : row.k0.val = bitrange row.y.val 1 9 := by
    have hj250 : row.j.val = row.y.val % 2 ^ 250 := by rw [hj_val]; simp [bitrange]
    have hbr : bitrange row.y.val 1 9 = row.j.val / 2 % 2 ^ 9 := by
      rw [hj250, ← bitrange_mod (show (1 : ℕ) + 9 ≤ 250 from by norm_num)]; simp [bitrange]
    rw [hbr]; omega
  refine ⟨?_, hj_val, hk0_val, hk2_val, hk3_eq, fun h1 => by
    rcases mul_eq_zero.mp heq7 with h | h
    · exact absurd (h1 ▸ h) one_ne_zero
    · exact h⟩
  -- `lsb` is the low bit of `y`
  show row.lsb.val = row.y.val % 2
  rw [hlsb_val, hj_val,
    show bitrange row.y.val 0 250 = row.y.val % 2 ^ 250 from by simp [bitrange]]
  exact Nat.mod_mod_of_dvd _ (by norm_num)

/-- Row-level completeness direction. -/
theorem eqs_of_spec (row : Row Fp) (hAss : Assumptions row) (hSpec : Spec row) :
    IsBool row.k3 ∧
    (row.j - (row.lsb + row.k0 * 2 + row.z1J * 1024) = 0) ∧
    (row.y - (row.j + row.k2 * ((2 ^ 250 : ℕ) : Fp)
      + row.k3 * ((2 ^ 254 : ℕ) : Fp)) = 0) ∧
    (row.j + ((2 ^ 130 : ℕ) : Fp) - tP - row.j' = 0) ∧
    row.k3 * row.k2 = 0 ∧ row.k3 * row.z13J = 0 ∧ row.k3 * row.z13J' = 0 := by
  obtain ⟨hlsb_bool, hj_lt, hk0_lt, hk2_lt, hj', hz1J, hz13J, hzjDec⟩ := hAss
  obtain ⟨hlowbit, hj_val, hk0_val, hk2_val, hk3_val, hzjZero⟩ := hSpec
  have hyval : row.y.val < PALLAS_BASE_CARD := ZMod.val_lt row.y
  have hyval255 : row.y.val < 2 ^ 255 := lt_trans hyval (by norm_num [PALLAS_BASE_CARD])
  have hj_eq : row.j = ((bitrange row.y.val 0 250 : ℕ) : Fp) := by
    rw [← hj_val]; exact (ZMod.natCast_rightInverse row.j).symm
  have hk0_eq : row.k0 = ((bitrange row.y.val 1 9 : ℕ) : Fp) := by
    rw [← hk0_val]; exact (ZMod.natCast_rightInverse row.k0).symm
  have hk2_eq : row.k2 = ((bitrange row.y.val 250 4 : ℕ) : Fp) := by
    rw [← hk2_val]; exact (ZMod.natCast_rightInverse row.k2).symm
  have hk3_eq : row.k3 = ((bitrange row.y.val 254 1 : ℕ) : Fp) := by
    rw [← hk3_val]; exact (ZMod.natCast_rightInverse row.k3).symm
  have hjval : row.j.val = bitrange row.y.val 0 250 := hj_val
  have hlsb : row.lsb = ((bitrange row.y.val 0 1 : ℕ) : Fp) := by
    rw [isLowBit_iff_mod_two] at hlowbit
    rw [hlowbit, show row.y.val % 2 = bitrange row.y.val 0 1 from by simp [bitrange]]
  have hz1J_f : row.z1J = ((bitrange row.y.val 10 240 : ℕ) : Fp) := by
    rw [← ZMod.natCast_rightInverse row.z1J, hz1J, hjval,
      show bitrange row.y.val 0 250 / 2 ^ 10 = bitrange row.y.val 10 240 from
        bitrange_low_div row.y.val 10 240]
  have hb1cases := show bitrange row.y.val 254 1 = 0 ∨ bitrange row.y.val 254 1 = 1 from by
    have := bitrange_lt row.y.val 254 1; omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- k3 Boolean
    rw [hk3_eq]; exact bitrange_one_isBool _ _
  · -- j = lsb + k0·2 + z1J·1024
    rw [hj_eq, hlsb, hk0_eq, hz1J_f, low_250_decomp row.y.val]; push_cast; ring
  · -- y = j + k2·2^250 + k3·2^254
    have hyv : row.y = ((row.y.val : ℕ) : Fp) :=
      (ZMod.natCast_rightInverse row.y).symm
    have hdcast : ((row.y.val : ℕ) : Fp)
        = ((bitrange row.y.val 0 250 : ℕ) : Fp)
          + ((bitrange row.y.val 250 4 : ℕ) : Fp) * ((2 ^ 250 : ℕ) : Fp)
          + ((bitrange row.y.val 254 1 : ℕ) : Fp) * ((2 ^ 254 : ℕ) : Fp) := by
      conv_lhs => rw [bit_decomp_255 hyval255]
      push_cast; ring
    linear_combination hyv + hdcast - hj_eq - ((2 ^ 250 : ℕ) : Fp) * hk2_eq
      - ((2 ^ 254 : ℕ) : Fp) * hk3_eq
  · -- j' = j + 2^130 - t_P
    linear_combination -hj'
  · -- k3·k2 = 0
    rcases hb1cases with h | h
    · rw [hk3_eq, h]; simp
    · rw [hk2_eq, (high_bit_canonical hyval h).1]; simp
  · -- k3·z13J = 0
    rcases hb1cases with h | h
    · rw [hk3_eq, h]; simp
    · have hz : row.z13J = 0 := by
        rw [← ZMod.val_eq_zero, hz13J, hjval,
          show bitrange row.y.val 0 250 / 2 ^ 130 = bitrange row.y.val 130 120 from
            bitrange_low_div row.y.val 130 120, high_bit_z13_zero hyval h]
      rw [hz]; simp
  · -- k3·z13J' = 0
    rcases hb1cases with h | h
    · rw [hk3_eq, h]; simp
    · rw [hzjZero (by rw [hk3_eq, h]; norm_num)]; simp

end YCanonicity.Gate

end Zcash.Circuits.NoteCommit
