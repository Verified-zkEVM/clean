import Clean.Circuit
import Clean.Gadgets.Boolean
import Clean.Orchard.Ecc
import Clean.Orchard.Action.CanonicityTheorems
import Clean.Utils.Tactics
import Clean.Utils.Tactics.ProvableStructDeriving

/-!
# Orchard incoming viewing key commitment gate

Clean port of the Orchard `CommitIvk` custom gate.

Reference:
`orchard@0.14.0/src/circuit/commit_ivk.rs`
- `CommitIvk canonicity check`
- `gadgets::commit_ivk`

The top-level `circuit` models the arithmetic constraints enabled by the Halo2
`q_commit_ivk` selector, not the selector, row layout, Sinsemilla hash, lookup range
checks, or assignment machinery around the gate.

Like the `NoteCommit` canonicity gates, the gate `Spec` is the *canonical-decomposition
payoff*: under the surrounding lookup rely-conditions (`Assumptions`), the witnessed
sub-pieces are exactly the canonical little-endian bit slices of `ak`/`nk`. The proofs reuse
the shared canonicity facts in `Orchard.Action.NoteCommit` (`CanonicityTheorems`).
-/

namespace Orchard.Action.CommitIvk.Gate

open Orchard.Specs (bitrange bitrange_lt bitrange_add bitrange_mod)
open CompElliptic.Fields.Pasta (PALLAS_BASE_CARD)
open Orchard.Action.NoteCommit (pallasBaseCard_eq tPNat tP_eq val_limb2 val_shift
  canonical_top_decomp natCast_eq_zero high_bit_canonical high_bit_z13_zero
  high_bit_high_zero bitrange_low_div bitrange_div_pow bit_decomp_255 bitrange_one_isBool)

structure Input (F : Type) where
  ak : F
  nk : F
  a : F
  bWhole : F
  c : F
  dWhole : F
  b0 : F
  b1 : F
  b2 : F
  d0 : F
  d1 : F
  z13A : F
  z13C : F
  aPrime : F
  b2CPrime : F
  z13APrime : F
  z14B2CPrime : F
deriving ProvableStruct

/-- Rely-conditions from the surrounding lookups and witness assignments: the short pieces
`a`/`b0`/`b2`/`c`/`d0` are range-checked, `aPrime`/`b2CPrime` are the canonicity shifts, and
`z13A`/`z13C`/`z13APrime`/`z14B2CPrime` are the running-sum tails. -/
def Assumptions (row : Input Fp) : Prop :=
  row.a.val < 2 ^ 250 ∧
    row.b0.val < 2 ^ 4 ∧
    row.b2.val < 2 ^ 5 ∧
    row.c.val < 2 ^ 240 ∧
    row.d0.val < 2 ^ 9 ∧
    row.aPrime = row.a + ((2 ^ 130 : ℕ) : Fp) - tP ∧
    -- `z13A` is the Sinsemilla running sum of `a` (a full, range-checked `K`-bit
    -- decomposition), so the exact running-sum value is soundly available.
    row.z13A = ((row.a.val / 2 ^ 130 : ℕ) : Fp) ∧
    -- `z13APrime` is the `CopyCheck` (partial, 13-word) running sum of `aPrime`. The sound
    -- fact is the decomposition `aPrime = lo + 2^130·z13APrime` with `lo < 2^130`, which
    -- gives `z13APrime = 0 → aPrime < 2^130`. The `b1 = 1 → z13APrime = 0` implication is
    -- supplied for the completeness direction (and is the gate's own canonicity constraint).
    (∃ lo : ℕ, lo < 2 ^ 130 ∧
      row.aPrime = ((lo : ℕ) : Fp) + ((2 ^ 130 : ℕ) : Fp) * row.z13APrime) ∧
    (row.b1 = 1 → row.z13APrime = 0) ∧
    row.b2CPrime = row.b2 + row.c * ((2 ^ 5 : ℕ) : Fp) + ((2 ^ 140 : ℕ) : Fp) - tP ∧
    row.z13C = ((row.c.val / 2 ^ 130 : ℕ) : Fp) ∧
    (∃ lo : ℕ, lo < 2 ^ 140 ∧
      row.b2CPrime = ((lo : ℕ) : Fp) + ((2 ^ 140 : ℕ) : Fp) * row.z14B2CPrime) ∧
    (row.d1 = 1 → row.z14B2CPrime = 0)

/-- The gate's payoff: `a`/`b0`/`b1` are the canonical bit slices of `ak`, `b2`/`c`/`d0`/`d1`
are the canonical bit slices of `nk`, and the pieces `b`/`d` are the witnessed sub-piece
recombinations. -/
def Spec (row : Input Fp) : Prop :=
  row.a.val = bitrange row.ak.val 0 250 ∧
    row.b0.val = bitrange row.ak.val 250 4 ∧
    row.b1.val = bitrange row.ak.val 254 1 ∧
    row.b2.val = bitrange row.nk.val 0 5 ∧
    row.c.val = bitrange row.nk.val 5 240 ∧
    row.d0.val = bitrange row.nk.val 245 9 ∧
    row.d1.val = bitrange row.nk.val 254 1 ∧
    row.bWhole = row.b0 + row.b1 * 16 + row.b2 * 32 ∧
    row.dWhole = row.d0 + row.d1 * 512

def main (row : Var Input Fp) : Circuit Fp Unit := do
  assertBool row.b1
  assertBool row.d1
  assertZero (row.bWhole - (row.b0 + row.b1 * 16 + row.b2 * 32))
  assertZero (row.dWhole - (row.d0 + row.d1 * 512))
  assertZero (row.a + row.b0 * Expression.const ((2 ^ 250 : ℕ) : Fp) +
    row.b1 * Expression.const ((2 ^ 254 : ℕ) : Fp) - row.ak)
  assertZero (row.b2 + row.c * Expression.const ((2 ^ 5 : ℕ) : Fp) +
    row.d0 * Expression.const ((2 ^ 245 : ℕ) : Fp) +
    row.d1 * Expression.const ((2 ^ 254 : ℕ) : Fp) - row.nk)
  assertZero (row.b1 * row.b0)
  assertZero (row.b1 * row.z13A)
  assertZero (row.a + Expression.const ((2 ^ 130 : ℕ) : Fp) -
    Expression.const tP - row.aPrime)
  assertZero (row.b1 * row.z13APrime)
  assertZero (row.d1 * row.d0)
  assertZero (row.d1 * row.z13C)
  assertZero (row.b2 + row.c * Expression.const ((2 ^ 5 : ℕ) : Fp) +
    Expression.const ((2 ^ 140 : ℕ) : Fp) - Expression.const tP - row.b2CPrime)
  assertZero (row.d1 * row.z14B2CPrime)

instance elaborated : ElaboratedCircuit Fp Input unit main := by
  elaborate_circuit

/-- The `ak` side of the gate's soundness argument (mirrors `GdCanonicity`): `a`/`b0`/`b1`
are the canonical bit slices of `ak`. Split out of `soundness` so that no single
declaration's kernel check explodes (4.30 bump). -/
private theorem soundness_ak {ak a b0 b1 z13A aPrime z13APrime : Fp}
    (ha_lt : a.val < 2 ^ 250) (hb0_lt : b0.val < 2 ^ 4) (hb1 : IsBool b1)
    (haPrime : aPrime = a + ((2 ^ 130 : ℕ) : Fp) - tP)
    (hz13A : z13A = ((a.val / 2 ^ 130 : ℕ) : Fp))
    (hz13APrimeDec : ∃ lo : ℕ, lo < 2 ^ 130 ∧
      aPrime = ((lo : ℕ) : Fp) + ((2 ^ 130 : ℕ) : Fp) * z13APrime)
    (hak : a + b0 * ((2 ^ 250 : ℕ) : Fp) + b1 * ((2 ^ 254 : ℕ) : Fp) - ak = 0)
    (hb1b0 : b1 * b0 = 0) (hb1z13A : b1 * z13A = 0) (hb1z13APrime : b1 * z13APrime = 0) :
    a.val = bitrange ak.val 0 250 ∧ b0.val = bitrange ak.val 250 4 ∧
      b1.val = bitrange ak.val 254 1 := by
  have hp := pallasBaseCard_eq
  have htpsmall : tPNat < 2 ^ 130 := by norm_num [tPNat]
  have hloA_val : (a + b0 * ((2 ^ 250 : ℕ) : Fp)).val
      = a.val + b0.val * 2 ^ 250 :=
    val_limb2 250 (by omega)
  have hloA_lt : (a + b0 * ((2 ^ 250 : ℕ) : Fp)).val < 2 ^ 254 := by
    rw [hloA_val]; omega
  have hcanonA : b1 = 1 →
      (a + b0 * ((2 ^ 250 : ℕ) : Fp)).val < tPNat := by
    intro h1
    have hb0z : b0 = 0 := by
      rcases mul_eq_zero.mp hb1b0 with h | h
      · exact absurd (h1 ▸ h) one_ne_zero
      · exact h
    have ha130 : a.val < 2 ^ 130 := by
      have hz : z13A = 0 := by
        rcases mul_eq_zero.mp hb1z13A with h | h
        · exact absurd (h1 ▸ h) one_ne_zero
        · exact h
      rw [hz13A] at hz
      have := natCast_eq_zero
        (lt_of_le_of_lt (Nat.div_le_self _ _) (lt_trans ha_lt (by norm_num [PALLAS_BASE_CARD]))) hz
      omega
    have haPrime_lt : aPrime.val < 2 ^ 130 := by
      have hz : z13APrime = 0 := by
        rcases mul_eq_zero.mp hb1z13APrime with h | h
        · exact absurd (h1 ▸ h) one_ne_zero
        · exact h
      obtain ⟨lo, hlo, hdec⟩ := hz13APrimeDec
      rw [hz, mul_zero, _root_.add_zero] at hdec
      rw [hdec, ZMod.val_natCast_of_lt (lt_trans hlo (by norm_num [PALLAS_BASE_CARD]))]
      exact hlo
    have haPrime_val : aPrime.val = a.val + 2 ^ 130 - tPNat := by
      rw [haPrime]; exact val_shift 130 (by omega) (by omega)
    rw [hloA_val, hb0z, ZMod.val_zero]; simp only [zero_mul, add_zero]; omega
  have hrecA : ak = (a + b0 * ((2 ^ 250 : ℕ) : Fp))
      + b1 * ((2 ^ 254 : ℕ) : Fp) := by linear_combination -hak
  obtain ⟨_, hloA_eq, hb1_eq⟩ := canonical_top_decomp hrecA hloA_lt hb1 hcanonA
  have hmodA : bitrange ak.val 0 254 = ak.val % 2 ^ 254 := by simp [bitrange]
  refine ⟨?_, ?_, hb1_eq⟩
  · have h1 : a.val = bitrange (a + b0 * ((2 ^ 250 : ℕ) : Fp)).val 0 250 := by
      simp only [bitrange, pow_zero, Nat.div_one, hloA_val]; omega
    rw [h1, hloA_eq, hmodA, bitrange_mod (by norm_num : 0 + 250 ≤ 254)]
  · have h1 : b0.val = bitrange (a + b0 * ((2 ^ 250 : ℕ) : Fp)).val 250 4 := by
      simp only [bitrange, hloA_val]; omega
    rw [h1, hloA_eq, hmodA, bitrange_mod (by norm_num : 250 + 4 ≤ 254)]

/-- The `nk` side of the gate's soundness argument (3-limb low part `b2 + c·2^5 + d0·2^245`,
top bit `d1`): `b2`/`c`/`d0`/`d1` are the canonical bit slices of `nk`. Split out of
`soundness` so that no single declaration's kernel check explodes (4.30 bump). -/
private theorem soundness_nk {nk b2 c d0 d1 b2CPrime z14B2CPrime : Fp}
    (hb2_lt : b2.val < 2 ^ 5) (hc_lt : c.val < 2 ^ 240) (hd0_lt : d0.val < 2 ^ 9)
    (hd1 : IsBool d1)
    (hb2cP : b2CPrime = b2 + c * ((2 ^ 5 : ℕ) : Fp) + ((2 ^ 140 : ℕ) : Fp) - tP)
    (hz14Dec : ∃ lo : ℕ, lo < 2 ^ 140 ∧
      b2CPrime = ((lo : ℕ) : Fp) + ((2 ^ 140 : ℕ) : Fp) * z14B2CPrime)
    (hnk : b2 + c * ((2 ^ 5 : ℕ) : Fp) + d0 * ((2 ^ 245 : ℕ) : Fp)
      + d1 * ((2 ^ 254 : ℕ) : Fp) - nk = 0)
    (hd1d0 : d1 * d0 = 0) (hd1z14 : d1 * z14B2CPrime = 0) :
    b2.val = bitrange nk.val 0 5 ∧ c.val = bitrange nk.val 5 240 ∧
      d0.val = bitrange nk.val 245 9 ∧ d1.val = bitrange nk.val 254 1 := by
  have hp := pallasBaseCard_eq
  have htpsmall : tPNat < 2 ^ 130 := by norm_num [tPNat]
  have hloC_inner_val : (b2 + c * ((2 ^ 5 : ℕ) : Fp)).val
      = b2.val + c.val * 2 ^ 5 :=
    val_limb2 5 (by omega)
  have hloN_val : ((b2 + c * ((2 ^ 5 : ℕ) : Fp))
        + d0 * ((2 ^ 245 : ℕ) : Fp)).val
      = b2.val + c.val * 2 ^ 5 + d0.val * 2 ^ 245 := by
    rw [val_limb2 245 (by rw [hloC_inner_val]; omega), hloC_inner_val]
  have hloN_lt : ((b2 + c * ((2 ^ 5 : ℕ) : Fp))
        + d0 * ((2 ^ 245 : ℕ) : Fp)).val < 2 ^ 254 := by
    rw [hloN_val]; omega
  have hcanonN : d1 = 1 →
      ((b2 + c * ((2 ^ 5 : ℕ) : Fp))
        + d0 * ((2 ^ 245 : ℕ) : Fp)).val < tPNat := by
    intro h1
    have hd0z : d0 = 0 := by
      rcases mul_eq_zero.mp hd1d0 with h | h
      · exact absurd (h1 ▸ h) one_ne_zero
      · exact h
    have hinner_lt : (b2 + c * ((2 ^ 5 : ℕ) : Fp)).val < tPNat := by
      have hb2cP_val : b2CPrime.val
          = (b2 + c * ((2 ^ 5 : ℕ) : Fp)).val + 2 ^ 140 - tPNat := by
        rw [hb2cP]; exact val_shift 140 (by rw [hloC_inner_val]; omega) (by rw [hloC_inner_val]; omega)
      have hb2cP_lt : b2CPrime.val < 2 ^ 140 := by
        have hz : z14B2CPrime = 0 := by
          rcases mul_eq_zero.mp hd1z14 with h | h
          · exact absurd (h1 ▸ h) one_ne_zero
          · exact h
        obtain ⟨lo, hlo, hdec⟩ := hz14Dec
        rw [hz, mul_zero, _root_.add_zero] at hdec
        rw [hdec, ZMod.val_natCast_of_lt (lt_trans hlo (by norm_num [PALLAS_BASE_CARD]))]
        exact hlo
      omega
    rw [hloN_val, hd0z, ZMod.val_zero]
    rw [hloC_inner_val] at hinner_lt
    simp only [zero_mul, add_zero]; omega
  have hrecN : nk = ((b2 + c * ((2 ^ 5 : ℕ) : Fp))
        + d0 * ((2 ^ 245 : ℕ) : Fp)) + d1 * ((2 ^ 254 : ℕ) : Fp) := by
    linear_combination -hnk
  obtain ⟨_, hloN_eq, hd1_eq⟩ := canonical_top_decomp hrecN hloN_lt hd1 hcanonN
  have hmodN : bitrange nk.val 0 254 = nk.val % 2 ^ 254 := by simp [bitrange]
  refine ⟨?_, ?_, ?_, hd1_eq⟩
  · have h1 : b2.val = bitrange ((b2 + c * ((2 ^ 5 : ℕ) : Fp))
        + d0 * ((2 ^ 245 : ℕ) : Fp)).val 0 5 := by
      simp only [bitrange, pow_zero, Nat.div_one, hloN_val]; omega
    rw [h1, hloN_eq, hmodN, bitrange_mod (by norm_num : 0 + 5 ≤ 254)]
  · have h1 : c.val = bitrange ((b2 + c * ((2 ^ 5 : ℕ) : Fp))
        + d0 * ((2 ^ 245 : ℕ) : Fp)).val 5 240 := by
      simp only [bitrange, hloN_val]; omega
    rw [h1, hloN_eq, hmodN, bitrange_mod (by norm_num : 5 + 240 ≤ 254)]
  · have h1 : d0.val = bitrange ((b2 + c * ((2 ^ 5 : ℕ) : Fp))
        + d0 * ((2 ^ 245 : ℕ) : Fp)).val 245 9 := by
      simp only [bitrange, hloN_val]; omega
    rw [h1, hloN_eq, hmodN, bitrange_mod (by norm_num : 245 + 9 ≤ 254)]

theorem soundness : FormalAssertion.Soundness Fp main Assumptions Spec := by
  circuit_proof_start [tP]
  obtain ⟨ha_lt, hb0_lt, hb2_lt, hc_lt, hd0_lt, haPrime, hz13A, hz13APrimeDec,
    _hb1z13APrimeA, hb2cP, _hz13C, hz14Dec, _hd1z14A⟩ := h_assumptions
  obtain ⟨hb1, hd1, hbW, hdW, hak, hnk, hb1b0, hb1z13A, _haPrimeC, hb1z13APrime,
    hd1d0, _hd1z13C, _hb2cPC, hd1z14⟩ := h_holds
  obtain ⟨ha_eq, hb0_eq, hb1_eq⟩ := soundness_ak ha_lt hb0_lt hb1 haPrime hz13A
    hz13APrimeDec hak hb1b0 hb1z13A hb1z13APrime
  obtain ⟨hb2_eq, hc_eq, hd0_eq, hd1_eq⟩ := soundness_nk hb2_lt hc_lt hd0_lt hd1 hb2cP
    hz14Dec hnk hd1d0 hd1z14
  exact ⟨ha_eq, hb0_eq, hb1_eq, hb2_eq, hc_eq, hd0_eq, hd1_eq,
    by linear_combination hbW, by linear_combination hdW⟩

theorem completeness : FormalAssertion.Completeness Fp main Assumptions Spec := by
  circuit_proof_start
  obtain ⟨ha_lt, hb0_lt, hb2_lt, hc_lt, hd0_lt, haPrime, hz13A, _hz13APrimeDec,
    hb1z13APrimeImpl, hb2cP, hz13C, _hz14Dec, hd1z14Impl⟩ := h_assumptions
  obtain ⟨ha_val, hb0_val, hb1_val, hb2_val, hc_val, hd0_val, hd1_val, hbW, hdW⟩ := h_spec
  have hp := pallasBaseCard_eq
  have htpsmall : tPNat < 2 ^ 130 := by norm_num [tPNat]
  have hak : input_ak.val < 2 ^ 255 :=
    lt_trans (ZMod.val_lt input_ak) (by norm_num [PALLAS_BASE_CARD])
  have hnk : input_nk.val < 2 ^ 255 :=
    lt_trans (ZMod.val_lt input_nk) (by norm_num [PALLAS_BASE_CARD])
  have ha_eq : input_a = ((bitrange input_ak.val 0 250 : ℕ) : Fp) := by
    rw [← ha_val]; exact (ZMod.natCast_rightInverse input_a).symm
  have hb0_eq : input_b0 = ((bitrange input_ak.val 250 4 : ℕ) : Fp) := by
    rw [← hb0_val]; exact (ZMod.natCast_rightInverse input_b0).symm
  have hb1_eq : input_b1 = ((bitrange input_ak.val 254 1 : ℕ) : Fp) := by
    rw [← hb1_val]; exact (ZMod.natCast_rightInverse input_b1).symm
  have hb2_eq : input_b2 = ((bitrange input_nk.val 0 5 : ℕ) : Fp) := by
    rw [← hb2_val]; exact (ZMod.natCast_rightInverse input_b2).symm
  have hc_eq : input_c = ((bitrange input_nk.val 5 240 : ℕ) : Fp) := by
    rw [← hc_val]; exact (ZMod.natCast_rightInverse input_c).symm
  have hd0_eq : input_d0 = ((bitrange input_nk.val 245 9 : ℕ) : Fp) := by
    rw [← hd0_val]; exact (ZMod.natCast_rightInverse input_d0).symm
  have hd1_eq : input_d1 = ((bitrange input_nk.val 254 1 : ℕ) : Fp) := by
    rw [← hd1_val]; exact (ZMod.natCast_rightInverse input_d1).symm
  have hb1cases := show bitrange input_ak.val 254 1 = 0 ∨ bitrange input_ak.val 254 1 = 1 from by
    have := bitrange_lt input_ak.val 254 1; omega
  have hd1cases := show bitrange input_nk.val 254 1 = 0 ∨ bitrange input_nk.val 254 1 = 1 from by
    have := bitrange_lt input_nk.val 254 1; omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- IsBool b1
    rw [hb1_eq]; exact bitrange_one_isBool _ _
  · -- IsBool d1
    rw [hd1_eq]; exact bitrange_one_isBool _ _
  · -- bWhole
    rw [hbW]; ring
  · -- dWhole
    rw [hdW]; ring
  · -- ak reconstruction
    have hak_eq : input_ak = ((bitrange input_ak.val 0 250 : ℕ) : Fp)
        + ((bitrange input_ak.val 250 4 : ℕ) : Fp) * ((2 ^ 250 : ℕ) : Fp)
        + ((bitrange input_ak.val 254 1 : ℕ) : Fp) * ((2 ^ 254 : ℕ) : Fp) := by
      conv_lhs => rw [← ZMod.natCast_rightInverse input_ak, bit_decomp_255 hak]
      push_cast; ring
    rw [ha_eq, hb0_eq, hb1_eq]; linear_combination -hak_eq
  · -- nk reconstruction
    have hdec : input_nk.val = bitrange input_nk.val 0 5
        + 2 ^ 5 * bitrange input_nk.val 5 240
        + 2 ^ 245 * bitrange input_nk.val 245 9
        + 2 ^ 254 * bitrange input_nk.val 254 1 := by
      simp only [bitrange, pow_zero, Nat.div_one]; omega
    have hnk_eq : input_nk = ((bitrange input_nk.val 0 5 : ℕ) : Fp)
        + ((bitrange input_nk.val 5 240 : ℕ) : Fp) * ((2 ^ 5 : ℕ) : Fp)
        + ((bitrange input_nk.val 245 9 : ℕ) : Fp) * ((2 ^ 245 : ℕ) : Fp)
        + ((bitrange input_nk.val 254 1 : ℕ) : Fp) * ((2 ^ 254 : ℕ) : Fp) := by
      conv_lhs => rw [← ZMod.natCast_rightInverse input_nk, hdec]
      push_cast; ring
    rw [hb2_eq, hc_eq, hd0_eq, hd1_eq]; linear_combination -hnk_eq
  · -- b1·b0 = 0
    rcases hb1cases with h | h
    · rw [hb1_eq, h]; simp
    · rw [hb0_eq, (high_bit_canonical (ZMod.val_lt input_ak) h).1]; simp
  · -- b1·z13A = 0
    rcases hb1cases with h | h
    · rw [hb1_eq, h]; simp
    · rw [hz13A, ha_val,
        show bitrange input_ak.val 0 250 / 2 ^ 130 = bitrange input_ak.val 130 120 from
          bitrange_low_div input_ak.val 130 120,
        high_bit_z13_zero (ZMod.val_lt input_ak) h]
      simp
  · -- aPrime
    rw [haPrime]; ring
  · -- b1·z13APrime = 0
    rcases hb1cases with h | h
    · rw [hb1_eq, h]; simp
    · rw [hb1z13APrimeImpl (by rw [hb1_eq, h]; norm_num)]; simp
  · -- d1·d0 = 0
    rcases hd1cases with h | h
    · rw [hd1_eq, h]; simp
    · rw [hd0_eq, (high_bit_high_zero (ZMod.val_lt input_nk) h (by norm_num) (by norm_num))]; simp
  · -- d1·z13C = 0
    rcases hd1cases with h | h
    · rw [hd1_eq, h]; simp
    · rw [hz13C, hc_val,
        show bitrange input_nk.val 5 240 / 2 ^ 130 = bitrange input_nk.val 135 110 from
          bitrange_div_pow input_nk.val 5 130 110,
        high_bit_high_zero (ZMod.val_lt input_nk) h (by norm_num) (by norm_num)]
      simp
  · -- b2CPrime
    rw [hb2cP]; ring
  · -- d1·z14B2CPrime = 0
    rcases hd1cases with h | h
    · rw [hd1_eq, h]; simp
    · rw [hd1z14Impl (by rw [hd1_eq, h]; norm_num)]; simp

def circuit : FormalAssertion Fp Input where
  name := "GATE CommitIvk canonicity check"
  main
  elaborated
  Assumptions
  Spec
  soundness
  completeness

end Orchard.Action.CommitIvk.Gate
