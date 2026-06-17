import Clean.Circuit
import Clean.Gadgets.Boolean
import Clean.Orchard.Action.CanonicityTheorems
import Clean.Utils.Tactics
import Clean.Utils.Tactics.ProvableStructDeriving

/-!
# NoteCommit canonicity gates

Custom-gate `FormalAssertion`s enforcing prime-field canonicity of the decomposed note
fields (`orchard note_commit.rs` `*_canonicity`, `y_canonicity`).
-/

namespace Orchard.Action.NoteCommit

open Orchard.Specs (bitrange bitrange_lt bitrange_add bitrange_mod)
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
    row.a' = row.a + ((2 ^ 130 : ℕ) : Fp) - Ecc.tP ∧
    row.z13A = ((row.a.val / 2 ^ 130 : ℕ) : Fp) ∧
    -- `z13A'` is the *partial* (13-word) CopyCheck running sum of `a'`, which overflows
    -- `2^130`, so only the telescoped decomposition is soundly available.
    ∃ lo : ℕ, lo < 2 ^ 130 ∧ row.a' = ((lo : ℕ) : Fp) + ((2 ^ 130 : ℕ) : Fp) * row.z13A'

/-- The gate's payoff: `a`/`b0`/`b1` are the canonical bit slices of `x(g_d)`. -/
def Spec (row : Row Fp) : Prop :=
  row.a = ((bitrange row.gdX.val 0 250 : ℕ) : Fp) ∧
    row.b0 = ((bitrange row.gdX.val 250 4 : ℕ) : Fp) ∧
    row.b1 = ((bitrange row.gdX.val 254 1 : ℕ) : Fp) ∧
    (row.b1 = 1 → row.z13A' = 0)

def main (row : Var Row Fp) : Circuit Fp Unit := do
  assertZero (row.a + row.b0 * Expression.const ((2 ^ 250 : ℕ) : Fp) +
    row.b1 * Expression.const ((2 ^ 254 : ℕ) : Fp) - row.gdX)
  assertZero (row.a + Expression.const ((2 ^ 130 : ℕ) : Fp) -
    Expression.const Ecc.tP - row.a')
  assertZero (row.b1 * row.b0)
  assertZero (row.b1 * row.z13A)
  assertZero (row.b1 * row.z13A')

def circuit : FormalAssertion Fp Row where
  name := "GATE NoteCommit input g_d"
  main
  Assumptions
  Spec
  soundness := by
    circuit_proof_start [Ecc.tP]
    obtain ⟨hb1, ha_lt, hb0_lt, haPrime, hz13A, hzaDec⟩ := h_assumptions
    obtain ⟨hrec, _, hg1, hg2, hg3⟩ := h_holds
    have hp := pallasBaseCard_eq
    have htpsmall : tPNat < 2 ^ 130 := by norm_num [tPNat]
    -- low 254-bit limb `lo = a + b0·2^250`
    have hlo_sum : input_a.val + input_b0.val * 2 ^ 250 < PALLAS_BASE_CARD := by omega
    have hlo_val : (input_a + input_b0 * ((2 ^ 250 : ℕ) : Fp)).val
        = input_a.val + input_b0.val * 2 ^ 250 := val_limb2 250 hlo_sum
    have hlo_lt : (input_a + input_b0 * ((2 ^ 250 : ℕ) : Fp)).val < 2 ^ 254 := by
      rw [hlo_val]; omega
    -- canonicity: when the top bit is set, the low limb is below `t_P`
    have hcanon : input_b1 = 1 →
        (input_a + input_b0 * ((2 ^ 250 : ℕ) : Fp)).val < tPNat := by
      intro h1
      have hb0z : input_b0 = 0 := by
        rcases mul_eq_zero.mp hg1 with h | h
        · exact absurd (h1 ▸ h) one_ne_zero
        · exact h
      have ha130 : input_a.val < 2 ^ 130 := by
        have hz : input_z13A = 0 := by
          rcases mul_eq_zero.mp hg2 with h | h
          · exact absurd (h1 ▸ h) one_ne_zero
          · exact h
        rw [hz13A] at hz
        have := natCast_eq_zero
          (lt_of_le_of_lt (Nat.div_le_self _ _) (lt_trans ha_lt (by norm_num [PALLAS_BASE_CARD]))) hz
        omega
      have haPrime_val : input_a'.val = input_a.val + 2 ^ 130 - tPNat := by
        rw [haPrime]; exact val_shift 130 (by omega) (by omega)
      have haPrime_lt : input_a'.val < 2 ^ 130 := by
        have hz : input_z13A' = 0 := by
          rcases mul_eq_zero.mp hg3 with h | h
          · exact absurd (h1 ▸ h) one_ne_zero
          · exact h
        obtain ⟨lo, hlo, hdec⟩ := hzaDec
        rw [hz, mul_zero, _root_.add_zero] at hdec
        rw [hdec, ZMod.val_natCast_of_lt (lt_trans hlo (by norm_num [PALLAS_BASE_CARD]))]
        exact hlo
      rw [hlo_val, hb0z, ZMod.val_zero]; omega
    -- top-bit decomposition of `gdX`
    have hrecL : input_gdX = (input_a + input_b0 * ((2 ^ 250 : ℕ) : Fp))
        + input_b1 * ((2 ^ 254 : ℕ) : Fp) := by linear_combination -hrec
    obtain ⟨_, hlo_eq, hb1_eq⟩ := canonical_top_decomp hrecL hlo_lt hb1 hcanon
    have hmod : bitrange input_gdX.val 0 254 = input_gdX.val % 2 ^ 254 := by simp [bitrange]
    -- read the sub-pieces off the low 254-bit field
    have ha_eq : input_a.val = bitrange input_gdX.val 0 250 := by
      have h1 : input_a.val = bitrange (input_a + input_b0 * ((2 ^ 250 : ℕ) : Fp)).val 0 250 := by
        simp only [bitrange, pow_zero, Nat.div_one, hlo_val]; omega
      rw [h1, hlo_eq, hmod, bitrange_mod (by norm_num : 0 + 250 ≤ 254)]
    have hb0_eq : input_b0.val = bitrange input_gdX.val 250 4 := by
      have h1 : input_b0.val = bitrange (input_a + input_b0 * ((2 ^ 250 : ℕ) : Fp)).val 250 4 := by
        simp only [bitrange, hlo_val]; omega
      rw [h1, hlo_eq, hmod, bitrange_mod (by norm_num : 250 + 4 ≤ 254)]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [← ha_eq]; exact (ZMod.natCast_rightInverse input_a).symm
    · rw [← hb0_eq]; exact (ZMod.natCast_rightInverse input_b0).symm
    · rw [← hb1_eq]; exact (ZMod.natCast_rightInverse input_b1).symm
    · intro h1
      rcases mul_eq_zero.mp hg3 with h | h
      · exact absurd (h1 ▸ h) one_ne_zero
      · exact h
  completeness := by
    circuit_proof_start
    obtain ⟨_, ha_lt, _, haPrime, hz13A, _⟩ := h_assumptions
    obtain ⟨ha_eq, hb0_eq, hb1_eq, hzaZero⟩ := h_spec
    have hp := pallasBaseCard_eq
    have htpsmall : tPNat < 2 ^ 130 := by norm_num [tPNat]
    have hgdX : input_gdX.val < 2 ^ 255 :=
      lt_trans (ZMod.val_lt input_gdX) (by norm_num [PALLAS_BASE_CARD])
    have ha_val : input_a.val = bitrange input_gdX.val 0 250 := by
      rw [ha_eq]
      exact ZMod.val_natCast_of_lt (lt_trans (bitrange_lt _ 0 250) (by norm_num [PALLAS_BASE_CARD]))
    have hb1cases := show bitrange input_gdX.val 254 1 = 0 ∨ bitrange input_gdX.val 254 1 = 1 from by
      have := bitrange_lt input_gdX.val 254 1; omega
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · -- reconstruction
      have hgd_eq : input_gdX = ((bitrange input_gdX.val 0 250 : ℕ) : Fp)
          + ((bitrange input_gdX.val 250 4 : ℕ) : Fp) * ((2 ^ 250 : ℕ) : Fp)
          + ((bitrange input_gdX.val 254 1 : ℕ) : Fp) * ((2 ^ 254 : ℕ) : Fp) := by
        conv_lhs => rw [← ZMod.natCast_rightInverse input_gdX, bit_decomp_255 hgdX]
        push_cast; ring
      rw [ha_eq, hb0_eq, hb1_eq]; linear_combination -hgd_eq
    · -- prime
      rw [haPrime]; ring
    · -- b1·b0 = 0
      rcases hb1cases with h | h
      · rw [hb1_eq, h]; simp
      · rw [hb0_eq, (high_bit_canonical (ZMod.val_lt input_gdX) h).1]; simp
    · -- b1·z13A = 0
      rcases hb1cases with h | h
      · rw [hb1_eq, h]; simp
      · rw [hz13A, ha_val,
          show bitrange input_gdX.val 0 250 / 2 ^ 130 = bitrange input_gdX.val 130 120 from
            bitrange_low_div input_gdX.val 130 120,
          high_bit_z13_zero (ZMod.val_lt input_gdX) h]
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
    row.b3C' = row.b3 + row.c * ((2 ^ 4 : ℕ) : Fp) + ((2 ^ 140 : ℕ) : Fp) - Ecc.tP ∧
    row.z13C = ((row.c.val / 2 ^ 130 : ℕ) : Fp) ∧
    ∃ lo : ℕ, lo < 2 ^ 140 ∧ row.b3C' = ((lo : ℕ) : Fp) + ((2 ^ 140 : ℕ) : Fp) * row.z14B3C'

/-- The gate's payoff: `b3`/`c`/`d0` are the canonical bit slices of `x(pk_d)`. -/
def Spec (row : Row Fp) : Prop :=
  row.b3 = ((bitrange row.pkdX.val 0 4 : ℕ) : Fp) ∧
    row.c = ((bitrange row.pkdX.val 4 250 : ℕ) : Fp) ∧
    row.d0 = ((bitrange row.pkdX.val 254 1 : ℕ) : Fp) ∧
    (row.d0 = 1 → row.z14B3C' = 0)

def main (row : Var Row Fp) : Circuit Fp Unit := do
  assertZero (row.b3 + row.c * Expression.const ((2 ^ 4 : ℕ) : Fp) +
    row.d0 * Expression.const ((2 ^ 254 : ℕ) : Fp) - row.pkdX)
  assertZero (row.b3 + row.c * Expression.const ((2 ^ 4 : ℕ) : Fp) +
    Expression.const ((2 ^ 140 : ℕ) : Fp) - Expression.const Ecc.tP - row.b3C')
  assertZero (row.d0 * row.z13C)
  assertZero (row.d0 * row.z14B3C')

def circuit : FormalAssertion Fp Row where
  name := "GATE NoteCommit input pk_d"
  main
  Assumptions := Assumptions
  Spec := Spec
  soundness := by
    circuit_proof_start [Ecc.tP]
    obtain ⟨hd0, hc_lt, hb3_lt, hb3cP, hz13C, hzbDec⟩ := h_assumptions
    obtain ⟨hrec, _, hg1, hg2⟩ := h_holds
    have hp := pallasBaseCard_eq
    have htpsmall : tPNat < 2 ^ 130 := by norm_num [tPNat]
    have hlo_sum : input_b3.val + input_c.val * 2 ^ 4 < PALLAS_BASE_CARD := by omega
    have hlo_val : (input_b3 + input_c * ((2 ^ 4 : ℕ) : Fp)).val
        = input_b3.val + input_c.val * 2 ^ 4 := val_limb2 4 hlo_sum
    have hlo_lt : (input_b3 + input_c * ((2 ^ 4 : ℕ) : Fp)).val < 2 ^ 254 := by rw [hlo_val]; omega
    have hcanon : input_d0 = 1 → (input_b3 + input_c * ((2 ^ 4 : ℕ) : Fp)).val < tPNat := by
      intro h1
      have hc130 : input_c.val < 2 ^ 130 := by
        have hz : input_z13C = 0 := by
          rcases mul_eq_zero.mp hg1 with h | h
          · exact absurd (h1 ▸ h) one_ne_zero
          · exact h
        rw [hz13C] at hz
        have := natCast_eq_zero
          (lt_of_le_of_lt (Nat.div_le_self _ _) (lt_trans hc_lt (by norm_num [PALLAS_BASE_CARD]))) hz
        omega
      have hb3cP_val : input_b3C'.val
          = (input_b3 + input_c * ((2 ^ 4 : ℕ) : Fp)).val + 2 ^ 140 - tPNat := by
        rw [hb3cP]; exact val_shift 140 (by rw [hlo_val]; omega) (by rw [hlo_val]; omega)
      have hb3cP_lt : input_b3C'.val < 2 ^ 140 := by
        have hz : input_z14B3C' = 0 := by
          rcases mul_eq_zero.mp hg2 with h | h
          · exact absurd (h1 ▸ h) one_ne_zero
          · exact h
        obtain ⟨lo, hlo, hdec⟩ := hzbDec
        rw [hz, mul_zero, _root_.add_zero] at hdec
        rw [hdec, ZMod.val_natCast_of_lt (lt_trans hlo (by norm_num [PALLAS_BASE_CARD]))]
        exact hlo
      omega
    have hrecL : input_pkdX = (input_b3 + input_c * ((2 ^ 4 : ℕ) : Fp))
        + input_d0 * ((2 ^ 254 : ℕ) : Fp) := by linear_combination -hrec
    obtain ⟨_, hlo_eq, hd0_eq⟩ := canonical_top_decomp hrecL hlo_lt hd0 hcanon
    have hmod : bitrange input_pkdX.val 0 254 = input_pkdX.val % 2 ^ 254 := by simp [bitrange]
    have hb3_eq : input_b3.val = bitrange input_pkdX.val 0 4 := by
      have h1 : input_b3.val = bitrange (input_b3 + input_c * ((2 ^ 4 : ℕ) : Fp)).val 0 4 := by
        simp only [bitrange, pow_zero, Nat.div_one, hlo_val]; omega
      rw [h1, hlo_eq, hmod, bitrange_mod (by norm_num : 0 + 4 ≤ 254)]
    have hc_eq : input_c.val = bitrange input_pkdX.val 4 250 := by
      have h1 : input_c.val = bitrange (input_b3 + input_c * ((2 ^ 4 : ℕ) : Fp)).val 4 250 := by
        simp only [bitrange, hlo_val]; omega
      rw [h1, hlo_eq, hmod, bitrange_mod (by norm_num : 4 + 250 ≤ 254)]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [← hb3_eq]; exact (ZMod.natCast_rightInverse input_b3).symm
    · rw [← hc_eq]; exact (ZMod.natCast_rightInverse input_c).symm
    · rw [← hd0_eq]; exact (ZMod.natCast_rightInverse input_d0).symm
    · intro h1
      rcases mul_eq_zero.mp hg2 with h | h
      · exact absurd (h1 ▸ h) one_ne_zero
      · exact h
  completeness := by
    circuit_proof_start
    obtain ⟨_, hc_lt, hb3_lt, hb3cP, hz13C, _⟩ := h_assumptions
    obtain ⟨hb3_eq, hc_eq, hd0_eq, hzbZero⟩ := h_spec
    have hp := pallasBaseCard_eq
    have htpsmall : tPNat < 2 ^ 130 := by norm_num [tPNat]
    have hpkdX : input_pkdX.val < 2 ^ 255 :=
      lt_trans (ZMod.val_lt input_pkdX) (by norm_num [PALLAS_BASE_CARD])
    have hb3_val : input_b3.val = bitrange input_pkdX.val 0 4 := by
      rw [hb3_eq]
      exact ZMod.val_natCast_of_lt (lt_trans (bitrange_lt _ 0 4) (by norm_num [PALLAS_BASE_CARD]))
    have hc_val : input_c.val = bitrange input_pkdX.val 4 250 := by
      rw [hc_eq]
      exact ZMod.val_natCast_of_lt (lt_trans (bitrange_lt _ 4 250) (by norm_num [PALLAS_BASE_CARD]))
    have hd0cases := show bitrange input_pkdX.val 254 1 = 0 ∨ bitrange input_pkdX.val 254 1 = 1 from by
      have := bitrange_lt input_pkdX.val 254 1; omega
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- reconstruction
      have hdec : input_pkdX.val = bitrange input_pkdX.val 0 4
          + 2 ^ 4 * bitrange input_pkdX.val 4 250 + 2 ^ 254 * bitrange input_pkdX.val 254 1 := by
        simp only [bitrange, pow_zero, Nat.div_one]; omega
      have hpkd_eq : input_pkdX = ((bitrange input_pkdX.val 0 4 : ℕ) : Fp)
          + ((bitrange input_pkdX.val 4 250 : ℕ) : Fp) * ((2 ^ 4 : ℕ) : Fp)
          + ((bitrange input_pkdX.val 254 1 : ℕ) : Fp) * ((2 ^ 254 : ℕ) : Fp) := by
        conv_lhs => rw [← ZMod.natCast_rightInverse input_pkdX, hdec]
        push_cast; ring
      rw [hb3_eq, hc_eq, hd0_eq]; linear_combination -hpkd_eq
    · -- prime
      rw [hb3cP]; ring
    · -- d0·z13C = 0
      rcases hd0cases with h | h
      · rw [hd0_eq, h]; simp
      · rw [hz13C, hc_val,
          show bitrange input_pkdX.val 4 250 / 2 ^ 130 = bitrange input_pkdX.val 134 120 from
            bitrange_div_pow input_pkdX.val 4 130 120,
          high_bit_high_zero (ZMod.val_lt input_pkdX) h (by norm_num) (by norm_num)]
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
    row.d2 = ((bitrange row.value.val 0 8 : ℕ) : Fp) ∧
    row.d3 = ((bitrange row.value.val 8 50 : ℕ) : Fp) ∧
    row.e0 = ((bitrange row.value.val 58 6 : ℕ) : Fp)

def main (row : Var Row Fp) : Circuit Fp Unit := do
  assertZero (row.d2 + row.d3 * Expression.const ((2 ^ 8 : ℕ) : Fp) +
    row.e0 * Expression.const ((2 ^ 58 : ℕ) : Fp) - row.value)

def circuit : FormalAssertion Fp Row where
  name := "GATE NoteCommit input value"
  main
  Assumptions := Assumptions
  Spec := Spec
  soundness := by
    circuit_proof_start
    obtain ⟨hd2_lt, hd3_lt, he0_lt⟩ := h_assumptions
    have hp := pallasBaseCard_eq
    have hbnd : input_d2.val + input_d3.val * 2 ^ 8 + input_e0.val * 2 ^ 58
        < PALLAS_BASE_CARD := by omega
    have hval : input_value.val
        = input_d2.val + input_d3.val * 2 ^ 8 + input_e0.val * 2 ^ 58 := by
      have hcast : input_value
          = ((input_d2.val + input_d3.val * 2 ^ 8 + input_e0.val * 2 ^ 58 : ℕ) : Fp) := by
        have hrec : input_value = input_d2 + input_d3 * ((2 ^ 8 : ℕ) : Fp)
            + input_e0 * ((2 ^ 58 : ℕ) : Fp) := by linear_combination -h_holds
        rw [hrec]; push_cast
        rw [ZMod.natCast_rightInverse input_d2, ZMod.natCast_rightInverse input_d3,
          ZMod.natCast_rightInverse input_e0]
      rw [hcast, ZMod.val_natCast_of_lt hbnd]
    refine ⟨by rw [hval]; omega, ?_, ?_, ?_⟩
    · have hd2_eq : input_d2.val = bitrange input_value.val 0 8 := by
        simp only [bitrange, pow_zero, Nat.div_one, hval]; omega
      rw [← hd2_eq]; exact (ZMod.natCast_rightInverse input_d2).symm
    · have hd3_eq : input_d3.val = bitrange input_value.val 8 50 := by
        simp only [bitrange, hval]; omega
      rw [← hd3_eq]; exact (ZMod.natCast_rightInverse input_d3).symm
    · have he0_eq : input_e0.val = bitrange input_value.val 58 6 := by
        simp only [bitrange, hval]; omega
      rw [← he0_eq]; exact (ZMod.natCast_rightInverse input_e0).symm
  completeness := by
    circuit_proof_start
    obtain ⟨hval_lt, hd2_eq, hd3_eq, he0_eq⟩ := h_spec
    have hdec : input_value.val = bitrange input_value.val 0 8
        + 2 ^ 8 * bitrange input_value.val 8 50 + 2 ^ 58 * bitrange input_value.val 58 6 := by
      simp only [bitrange, pow_zero, Nat.div_one]; omega
    have hval_eq : input_value = ((bitrange input_value.val 0 8 : ℕ) : Fp)
        + ((bitrange input_value.val 8 50 : ℕ) : Fp) * ((2 ^ 8 : ℕ) : Fp)
        + ((bitrange input_value.val 58 6 : ℕ) : Fp) * ((2 ^ 58 : ℕ) : Fp) := by
      conv_lhs => rw [← ZMod.natCast_rightInverse input_value, hdec]
      push_cast; ring
    rw [hd2_eq, hd3_eq, he0_eq]; linear_combination -hval_eq

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
    row.e1F' = row.e1 + row.f * ((2 ^ 4 : ℕ) : Fp) + ((2 ^ 140 : ℕ) : Fp) - Ecc.tP ∧
    row.z13F = ((row.f.val / 2 ^ 130 : ℕ) : Fp) ∧
    ∃ lo : ℕ, lo < 2 ^ 140 ∧ row.e1F' = ((lo : ℕ) : Fp) + ((2 ^ 140 : ℕ) : Fp) * row.z14E1F'

/-- The gate's payoff: `e1`/`f`/`g0` are the canonical bit slices of `rho`. -/
def Spec (row : Row Fp) : Prop :=
  row.e1 = ((bitrange row.rho.val 0 4 : ℕ) : Fp) ∧
    row.f = ((bitrange row.rho.val 4 250 : ℕ) : Fp) ∧
    row.g0 = ((bitrange row.rho.val 254 1 : ℕ) : Fp) ∧
    (row.g0 = 1 → row.z14E1F' = 0)

def main (row : Var Row Fp) : Circuit Fp Unit := do
  assertZero (row.e1 + row.f * Expression.const ((2 ^ 4 : ℕ) : Fp) +
    row.g0 * Expression.const ((2 ^ 254 : ℕ) : Fp) - row.rho)
  assertZero (row.e1 + row.f * Expression.const ((2 ^ 4 : ℕ) : Fp) +
    Expression.const ((2 ^ 140 : ℕ) : Fp) - Expression.const Ecc.tP - row.e1F')
  assertZero (row.g0 * row.z13F)
  assertZero (row.g0 * row.z14E1F')

def circuit : FormalAssertion Fp Row where
  name := "GATE NoteCommit input rho"
  main
  Assumptions := Assumptions
  Spec := Spec
  soundness := by
    circuit_proof_start [Ecc.tP]
    obtain ⟨hg0, hf_lt, he1_lt, he1fP, hz13F, hzeDec⟩ := h_assumptions
    obtain ⟨hrec, _, hg1, hg2⟩ := h_holds
    have hp := pallasBaseCard_eq
    have htpsmall : tPNat < 2 ^ 130 := by norm_num [tPNat]
    have hlo_sum : input_e1.val + input_f.val * 2 ^ 4 < PALLAS_BASE_CARD := by omega
    have hlo_val : (input_e1 + input_f * ((2 ^ 4 : ℕ) : Fp)).val
        = input_e1.val + input_f.val * 2 ^ 4 := val_limb2 4 hlo_sum
    have hlo_lt : (input_e1 + input_f * ((2 ^ 4 : ℕ) : Fp)).val < 2 ^ 254 := by rw [hlo_val]; omega
    have hcanon : input_g0 = 1 → (input_e1 + input_f * ((2 ^ 4 : ℕ) : Fp)).val < tPNat := by
      intro h1
      have hf130 : input_f.val < 2 ^ 130 := by
        have hz : input_z13F = 0 := by
          rcases mul_eq_zero.mp hg1 with h | h
          · exact absurd (h1 ▸ h) one_ne_zero
          · exact h
        rw [hz13F] at hz
        have := natCast_eq_zero
          (lt_of_le_of_lt (Nat.div_le_self _ _) (lt_trans hf_lt (by norm_num [PALLAS_BASE_CARD]))) hz
        omega
      have he1fP_val : input_e1F'.val
          = (input_e1 + input_f * ((2 ^ 4 : ℕ) : Fp)).val + 2 ^ 140 - tPNat := by
        rw [he1fP]; exact val_shift 140 (by rw [hlo_val]; omega) (by rw [hlo_val]; omega)
      have he1fP_lt : input_e1F'.val < 2 ^ 140 := by
        have hz : input_z14E1F' = 0 := by
          rcases mul_eq_zero.mp hg2 with h | h
          · exact absurd (h1 ▸ h) one_ne_zero
          · exact h
        obtain ⟨lo, hlo, hdec⟩ := hzeDec
        rw [hz, mul_zero, _root_.add_zero] at hdec
        rw [hdec, ZMod.val_natCast_of_lt (lt_trans hlo (by norm_num [PALLAS_BASE_CARD]))]
        exact hlo
      omega
    have hrecL : input_rho = (input_e1 + input_f * ((2 ^ 4 : ℕ) : Fp))
        + input_g0 * ((2 ^ 254 : ℕ) : Fp) := by linear_combination -hrec
    obtain ⟨_, hlo_eq, hg0_eq⟩ := canonical_top_decomp hrecL hlo_lt hg0 hcanon
    have hmod : bitrange input_rho.val 0 254 = input_rho.val % 2 ^ 254 := by simp [bitrange]
    have he1_eq : input_e1.val = bitrange input_rho.val 0 4 := by
      have h1 : input_e1.val = bitrange (input_e1 + input_f * ((2 ^ 4 : ℕ) : Fp)).val 0 4 := by
        simp only [bitrange, pow_zero, Nat.div_one, hlo_val]; omega
      rw [h1, hlo_eq, hmod, bitrange_mod (by norm_num : 0 + 4 ≤ 254)]
    have hf_eq : input_f.val = bitrange input_rho.val 4 250 := by
      have h1 : input_f.val = bitrange (input_e1 + input_f * ((2 ^ 4 : ℕ) : Fp)).val 4 250 := by
        simp only [bitrange, hlo_val]; omega
      rw [h1, hlo_eq, hmod, bitrange_mod (by norm_num : 4 + 250 ≤ 254)]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [← he1_eq]; exact (ZMod.natCast_rightInverse input_e1).symm
    · rw [← hf_eq]; exact (ZMod.natCast_rightInverse input_f).symm
    · rw [← hg0_eq]; exact (ZMod.natCast_rightInverse input_g0).symm
    · intro h1
      rcases mul_eq_zero.mp hg2 with h | h
      · exact absurd (h1 ▸ h) one_ne_zero
      · exact h
  completeness := by
    circuit_proof_start
    obtain ⟨_, hf_lt, he1_lt, he1fP, hz13F, _⟩ := h_assumptions
    obtain ⟨he1_eq, hf_eq, hg0_eq, hzeZero⟩ := h_spec
    have hp := pallasBaseCard_eq
    have htpsmall : tPNat < 2 ^ 130 := by norm_num [tPNat]
    have hrhoX : input_rho.val < 2 ^ 255 :=
      lt_trans (ZMod.val_lt input_rho) (by norm_num [PALLAS_BASE_CARD])
    have he1_val : input_e1.val = bitrange input_rho.val 0 4 := by
      rw [he1_eq]
      exact ZMod.val_natCast_of_lt (lt_trans (bitrange_lt _ 0 4) (by norm_num [PALLAS_BASE_CARD]))
    have hf_val : input_f.val = bitrange input_rho.val 4 250 := by
      rw [hf_eq]
      exact ZMod.val_natCast_of_lt (lt_trans (bitrange_lt _ 4 250) (by norm_num [PALLAS_BASE_CARD]))
    have hg0cases := show bitrange input_rho.val 254 1 = 0 ∨ bitrange input_rho.val 254 1 = 1 from by
      have := bitrange_lt input_rho.val 254 1; omega
    refine ⟨?_, ?_, ?_, ?_⟩
    · have hdec : input_rho.val = bitrange input_rho.val 0 4
          + 2 ^ 4 * bitrange input_rho.val 4 250 + 2 ^ 254 * bitrange input_rho.val 254 1 := by
        simp only [bitrange, pow_zero, Nat.div_one]; omega
      have hrho_eq : input_rho = ((bitrange input_rho.val 0 4 : ℕ) : Fp)
          + ((bitrange input_rho.val 4 250 : ℕ) : Fp) * ((2 ^ 4 : ℕ) : Fp)
          + ((bitrange input_rho.val 254 1 : ℕ) : Fp) * ((2 ^ 254 : ℕ) : Fp) := by
        conv_lhs => rw [← ZMod.natCast_rightInverse input_rho, hdec]
        push_cast; ring
      rw [he1_eq, hf_eq, hg0_eq]; linear_combination -hrho_eq
    · rw [he1fP]; ring
    · rcases hg0cases with h | h
      · rw [hg0_eq, h]; simp
      · rw [hz13F, hf_val,
          show bitrange input_rho.val 4 250 / 2 ^ 130 = bitrange input_rho.val 134 120 from
            bitrange_div_pow input_rho.val 4 130 120,
          high_bit_high_zero (ZMod.val_lt input_rho) h (by norm_num) (by norm_num)]
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
    row.g1G2' = row.g1 + row.g2 * ((2 ^ 9 : ℕ) : Fp) + ((2 ^ 130 : ℕ) : Fp) - Ecc.tP ∧
    row.z13G = ((row.g1.val + row.g2.val * 2 ^ 9) / 2 ^ 130 : ℕ) ∧
    ∃ lo : ℕ, lo < 2 ^ 130 ∧ row.g1G2' = ((lo : ℕ) : Fp) + ((2 ^ 130 : ℕ) : Fp) * row.z13G1G2'

/-- The gate's payoff: `g1`/`g2`/`h0`/`h1` are the canonical bit slices of `psi`. -/
def Spec (row : Row Fp) : Prop :=
  row.g1 = ((bitrange row.psi.val 0 9 : ℕ) : Fp) ∧
    row.g2 = ((bitrange row.psi.val 9 240 : ℕ) : Fp) ∧
    row.h0 = ((bitrange row.psi.val 249 5 : ℕ) : Fp) ∧
    row.h1 = ((bitrange row.psi.val 254 1 : ℕ) : Fp) ∧
    (row.h1 = 1 → row.z13G1G2' = 0)

def main (row : Var Row Fp) : Circuit Fp Unit := do
  assertZero (row.g1 + row.g2 * Expression.const ((2 ^ 9 : ℕ) : Fp) +
    row.h0 * Expression.const ((2 ^ 249 : ℕ) : Fp) +
    row.h1 * Expression.const ((2 ^ 254 : ℕ) : Fp) - row.psi)
  assertZero (row.g1 + row.g2 * Expression.const ((2 ^ 9 : ℕ) : Fp) +
    Expression.const ((2 ^ 130 : ℕ) : Fp) - Expression.const Ecc.tP - row.g1G2')
  assertZero (row.h1 * row.h0)
  assertZero (row.h1 * row.z13G)
  assertZero (row.h1 * row.z13G1G2')

def circuit : FormalAssertion Fp Row where
  name := "GATE NoteCommit input psi"
  main
  Assumptions := Assumptions
  Spec := Spec
  soundness := by
    circuit_proof_start [Ecc.tP]
    obtain ⟨hh1, hg1_lt, hg2_lt, hh0_lt, hg1g2P, hz13G, hzgDec⟩ := h_assumptions
    obtain ⟨hrec, _, hg_h0, hg_z13, hg_z13p⟩ := h_holds
    have hp := pallasBaseCard_eq
    have htpsmall : tPNat < 2 ^ 130 := by norm_num [tPNat]
    -- inner limb `g1 + g2·2^9`
    have hin_sum : input_g1.val + input_g2.val * 2 ^ 9 < PALLAS_BASE_CARD := by omega
    have hin_val : (input_g1 + input_g2 * ((2 ^ 9 : ℕ) : Fp)).val
        = input_g1.val + input_g2.val * 2 ^ 9 := val_limb2 9 hin_sum
    have hin_lt : input_g1.val + input_g2.val * 2 ^ 9 < 2 ^ 249 := by omega
    -- low 254-bit limb `inner + h0·2^249`
    have hlo_sum : (input_g1 + input_g2 * ((2 ^ 9 : ℕ) : Fp)).val + input_h0.val * 2 ^ 249
        < PALLAS_BASE_CARD := by rw [hin_val]; omega
    have hlo_val : ((input_g1 + input_g2 * ((2 ^ 9 : ℕ) : Fp)) + input_h0 * ((2 ^ 249 : ℕ) : Fp)).val
        = (input_g1.val + input_g2.val * 2 ^ 9) + input_h0.val * 2 ^ 249 := by
      rw [val_limb2 249 hlo_sum, hin_val]
    have hlo_lt : ((input_g1 + input_g2 * ((2 ^ 9 : ℕ) : Fp)) + input_h0 * ((2 ^ 249 : ℕ) : Fp)).val
        < 2 ^ 254 := by rw [hlo_val]; omega
    have hcanon : input_h1 = 1 →
        ((input_g1 + input_g2 * ((2 ^ 9 : ℕ) : Fp)) + input_h0 * ((2 ^ 249 : ℕ) : Fp)).val
          < tPNat := by
      intro h1
      have hh0z : input_h0 = 0 := by
        rcases mul_eq_zero.mp hg_h0 with h | h
        · exact absurd (h1 ▸ h) one_ne_zero
        · exact h
      have hin130 : input_g1.val + input_g2.val * 2 ^ 9 < 2 ^ 130 := by
        have hz : input_z13G = 0 := by
          rcases mul_eq_zero.mp hg_z13 with h | h
          · exact absurd (h1 ▸ h) one_ne_zero
          · exact h
        rw [hz13G] at hz
        have := natCast_eq_zero
          (lt_of_le_of_lt (Nat.div_le_self _ _) (lt_trans hin_lt (by norm_num [PALLAS_BASE_CARD]))) hz
        omega
      have hgP_val : input_g1G2'.val
          = (input_g1 + input_g2 * ((2 ^ 9 : ℕ) : Fp)).val + 2 ^ 130 - tPNat := by
        rw [hg1g2P]; exact val_shift 130 (by rw [hin_val]; omega) (by rw [hin_val]; omega)
      have hgP_lt : input_g1G2'.val < 2 ^ 130 := by
        have hz : input_z13G1G2' = 0 := by
          rcases mul_eq_zero.mp hg_z13p with h | h
          · exact absurd (h1 ▸ h) one_ne_zero
          · exact h
        obtain ⟨lo, hlo, hdec⟩ := hzgDec
        rw [hz, mul_zero, _root_.add_zero] at hdec
        rw [hdec, ZMod.val_natCast_of_lt (lt_trans hlo (by norm_num [PALLAS_BASE_CARD]))]
        exact hlo
      rw [hlo_val, hh0z, ZMod.val_zero]; rw [hin_val] at hgP_val; omega
    have hrecL : input_psi
        = ((input_g1 + input_g2 * ((2 ^ 9 : ℕ) : Fp)) + input_h0 * ((2 ^ 249 : ℕ) : Fp))
          + input_h1 * ((2 ^ 254 : ℕ) : Fp) := by linear_combination -hrec
    obtain ⟨_, hlo_eq, hh1_eq⟩ := canonical_top_decomp hrecL hlo_lt hh1 hcanon
    have hmod : bitrange input_psi.val 0 254 = input_psi.val % 2 ^ 254 := by simp [bitrange]
    -- inner limb is the low 249 bits
    have hin_eq : input_g1.val + input_g2.val * 2 ^ 9 = bitrange input_psi.val 0 249 := by
      have h1 : (input_g1.val + input_g2.val * 2 ^ 9)
          = bitrange ((input_g1 + input_g2 * ((2 ^ 9 : ℕ) : Fp))
              + input_h0 * ((2 ^ 249 : ℕ) : Fp)).val 0 249 := by
        simp only [bitrange, pow_zero, Nat.div_one, hlo_val]; omega
      rw [h1, hlo_eq, hmod, bitrange_mod (by norm_num : 0 + 249 ≤ 254)]
    have hh0_eq : input_h0.val = bitrange input_psi.val 249 5 := by
      have h1 : input_h0.val = bitrange ((input_g1 + input_g2 * ((2 ^ 9 : ℕ) : Fp))
          + input_h0 * ((2 ^ 249 : ℕ) : Fp)).val 249 5 := by
        simp only [bitrange, hlo_val]; omega
      rw [h1, hlo_eq, hmod, bitrange_mod (by norm_num : 249 + 5 ≤ 254)]
    have hg1_eq : input_g1.val = bitrange input_psi.val 0 9 := by
      have h1 : input_g1.val = bitrange (input_g1.val + input_g2.val * 2 ^ 9) 0 9 := by
        simp only [bitrange, pow_zero, Nat.div_one]; omega
      rw [h1, hin_eq]
      have : bitrange input_psi.val 0 249 = input_psi.val % 2 ^ 249 := by simp [bitrange]
      rw [this, bitrange_mod (by norm_num : 0 + 9 ≤ 249)]
    have hg2_eq : input_g2.val = bitrange input_psi.val 9 240 := by
      have h1 : input_g2.val = bitrange (input_g1.val + input_g2.val * 2 ^ 9) 9 240 := by
        simp only [bitrange]; omega
      rw [h1, hin_eq]
      have : bitrange input_psi.val 0 249 = input_psi.val % 2 ^ 249 := by simp [bitrange]
      rw [this, bitrange_mod (by norm_num : 9 + 240 ≤ 249)]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [← hg1_eq]; exact (ZMod.natCast_rightInverse input_g1).symm
    · rw [← hg2_eq]; exact (ZMod.natCast_rightInverse input_g2).symm
    · rw [← hh0_eq]; exact (ZMod.natCast_rightInverse input_h0).symm
    · rw [← hh1_eq]; exact (ZMod.natCast_rightInverse input_h1).symm
    · intro h1
      rcases mul_eq_zero.mp hg_z13p with h | h
      · exact absurd (h1 ▸ h) one_ne_zero
      · exact h
  completeness := by
    circuit_proof_start
    obtain ⟨_, hg1_lt, hg2_lt, hh0_lt, hg1g2P, hz13G, _⟩ := h_assumptions
    obtain ⟨hg1_eq, hg2_eq, hh0_eq, hh1_eq, hzgZero⟩ := h_spec
    have hp := pallasBaseCard_eq
    have htpsmall : tPNat < 2 ^ 130 := by norm_num [tPNat]
    have hpsiX : input_psi.val < 2 ^ 255 :=
      lt_trans (ZMod.val_lt input_psi) (by norm_num [PALLAS_BASE_CARD])
    have hg1_val : input_g1.val = bitrange input_psi.val 0 9 := by
      rw [hg1_eq]
      exact ZMod.val_natCast_of_lt (lt_trans (bitrange_lt _ 0 9) (by norm_num [PALLAS_BASE_CARD]))
    have hg2_val : input_g2.val = bitrange input_psi.val 9 240 := by
      rw [hg2_eq]
      exact ZMod.val_natCast_of_lt (lt_trans (bitrange_lt _ 9 240) (by norm_num [PALLAS_BASE_CARD]))
    -- inner limb is the low 249 bits
    have hin_eq : input_g1.val + input_g2.val * 2 ^ 9 = bitrange input_psi.val 0 249 := by
      rw [hg1_val, hg2_val]; have := bitrange_add input_psi.val 0 9 240; norm_num at this; omega
    have hh1cases := show bitrange input_psi.val 254 1 = 0 ∨ bitrange input_psi.val 254 1 = 1 from by
      have := bitrange_lt input_psi.val 254 1; omega
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · have hdec : input_psi.val = bitrange input_psi.val 0 9
          + 2 ^ 9 * bitrange input_psi.val 9 240 + 2 ^ 249 * bitrange input_psi.val 249 5
          + 2 ^ 254 * bitrange input_psi.val 254 1 := by
        simp only [bitrange, pow_zero, Nat.div_one]; omega
      have hpsi_eq : input_psi = ((bitrange input_psi.val 0 9 : ℕ) : Fp)
          + ((bitrange input_psi.val 9 240 : ℕ) : Fp) * ((2 ^ 9 : ℕ) : Fp)
          + ((bitrange input_psi.val 249 5 : ℕ) : Fp) * ((2 ^ 249 : ℕ) : Fp)
          + ((bitrange input_psi.val 254 1 : ℕ) : Fp) * ((2 ^ 254 : ℕ) : Fp) := by
        conv_lhs => rw [← ZMod.natCast_rightInverse input_psi, hdec]
        push_cast; ring
      rw [hg1_eq, hg2_eq, hh0_eq, hh1_eq]; linear_combination -hpsi_eq
    · rw [hg1g2P]; ring
    · -- h1·h0 = 0
      rcases hh1cases with h | h
      · rw [hh1_eq, h]; simp
      · rw [hh0_eq, high_bit_high_zero (ZMod.val_lt input_psi) h (by norm_num) (by norm_num)]; simp
    · -- h1·z13G = 0
      rcases hh1cases with h | h
      · rw [hh1_eq, h]; simp
      · rw [hz13G, hin_eq,
          show bitrange input_psi.val 0 249 / 2 ^ 130 = bitrange input_psi.val 130 119 from
            bitrange_div_pow input_psi.val 0 130 119,
          high_bit_high_zero (ZMod.val_lt input_psi) h (by norm_num) (by norm_num)]
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

/-- The gate runs inside `y_canonicity`, where the surrounding running-sum lookups force
each supporting cell to be the corresponding bit slice of `y`. Those semantics are the
gate's rely-conditions: every cell equals its `bitrange` of `y.val` (with `j'` the
canonicity-shifted low part). The sign bit `lsb` is *not* assumed — the gate's constraints
pin it down, which is exactly what `Spec` records. -/
def Assumptions (row : Row Fp) : Prop :=
  row.k0 = ((bitrange row.y.val 1 9 : ℕ) : Fp) ∧
    row.k2 = ((bitrange row.y.val 250 4 : ℕ) : Fp) ∧
    row.k3 = ((bitrange row.y.val 254 1 : ℕ) : Fp) ∧
    row.j = ((bitrange row.y.val 0 250 : ℕ) : Fp) ∧
    row.z1J = ((bitrange row.y.val 10 240 : ℕ) : Fp) ∧
    row.z13J = ((bitrange row.y.val 130 120 : ℕ) : Fp) ∧
    row.j'.val = bitrange row.y.val 0 250 + 2 ^ 130 - tPNat ∧
    row.z13J' = ((row.j'.val / 2 ^ 130 : ℕ) : Fp)

/-- The gate's payoff: `lsb` is the low (sign) bit of the `y` coordinate. -/
def Spec (row : Row Fp) : Prop :=
  IsLowBit row.y row.lsb

def main (row : Var Row Fp) : Circuit Fp Unit := do
  assertBool row.k3
  assertZero (row.j - (row.lsb + row.k0 * 2 + row.z1J * 1024))
  assertZero (row.y - (row.j + row.k2 * ((2 ^ 250 : ℕ) : Fp) +
    row.k3 * ((2 ^ 254 : ℕ) : Fp)))
  assertZero (row.j + Expression.const ((2 ^ 130 : ℕ) : Fp) -
    Expression.const Ecc.tP - row.j')
  assertZero (row.k3 * row.k2)
  assertZero (row.k3 * row.z13J)
  assertZero (row.k3 * row.z13J')

def circuit : FormalAssertion Fp Row where
  name := "GATE y coordinate checks"
  main
  Assumptions := Assumptions
  Spec := Spec
  soundness := by
    circuit_proof_start
    obtain ⟨hk0, _, _, hj, hz1J, _, _, _⟩ := h_assumptions
    obtain ⟨_, hj_eq, _⟩ := h_holds
    -- `hj_eq` says the witnessed `j` equals `lsb + 2·k0 + 1024·z1J`; substituting the
    -- bit-slice values of `j`, `k0`, `z1J` isolates `lsb` as the low bit of `y`.
    rw [isLowBit_iff_mod_two,
      show input_y.val % 2 = bitrange input_y.val 0 1 from by simp [bitrange]]
    have hcast : ((bitrange input_y.val 0 250 : ℕ) : Fp)
        = ((bitrange input_y.val 0 1 : ℕ) : Fp)
          + 2 * ((bitrange input_y.val 1 9 : ℕ) : Fp)
          + 1024 * ((bitrange input_y.val 10 240 : ℕ) : Fp) := by
      rw [low_250_decomp]; push_cast; ring
    rw [hj, hk0, hz1J, hcast] at hj_eq
    linear_combination -hj_eq
  completeness := by
    circuit_proof_start
    obtain ⟨hk0, hk2, hk3, hj, hz1J, hz13, hj', hz13'⟩ := h_assumptions
    have hyval : input_y.val < PALLAS_BASE_CARD := ZMod.val_lt input_y
    have hyval255 : input_y.val < 2 ^ 255 := lt_trans hyval (by norm_num [PALLAS_BASE_CARD])
    -- `lsb` is the low bit of `y`, supplied by the `Spec`.
    have hlsb : input_lsb = ((bitrange input_y.val 0 1 : ℕ) : Fp) := by
      rw [isLowBit_iff_mod_two] at h_spec
      rw [h_spec, show input_y.val % 2 = bitrange input_y.val 0 1 from by simp [bitrange]]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- k3 Boolean
      rw [hk3]; exact bitrange_one_isBool _ _
    · -- j = lsb + 2·k0 + 1024·z1J
      rw [hj, hk0, hz1J, hlsb, low_250_decomp input_y.val]; push_cast; ring
    · -- y = j + k2·2^250 + k3·2^254
      -- `bit_decomp_255` reconstructs `y` from its slices; cast it and recombine with the
      -- cell equalities.  (Rewriting `input_y` directly would also hit the `input_y.val`
      -- buried inside each `bitrange`, so we feed everything to `linear_combination`.)
      have hyv : input_y = ((input_y.val : ℕ) : Fp) :=
        (ZMod.natCast_rightInverse input_y).symm
      have hdcast : ((input_y.val : ℕ) : Fp)
          = ((bitrange input_y.val 0 250 : ℕ) : Fp)
            + ((bitrange input_y.val 250 4 : ℕ) : Fp) * ((2 ^ 250 : ℕ) : Fp)
            + ((bitrange input_y.val 254 1 : ℕ) : Fp) * ((2 ^ 254 : ℕ) : Fp) := by
        conv_lhs => rw [bit_decomp_255 hyval255]
        push_cast; ring
      linear_combination hyv + hdcast - hj - ((2 ^ 250 : ℕ) : Fp) * hk2
        - ((2 ^ 254 : ℕ) : Fp) * hk3
    · -- j' = j + 2^130 - t_P
      have htp : tPNat ≤ bitrange input_y.val 0 250 + 2 ^ 130 := by
        have h1 : tPNat < 2 ^ 130 := by norm_num [tPNat]
        omega
      have hj'cast : input_j' = ((bitrange input_y.val 0 250 : ℕ) : Fp)
          + ((2 ^ 130 : ℕ) : Fp) - ((tPNat : ℕ) : Fp) := by
        -- avoid the truncating `Nat` subtraction by adding `tPNat` back: `j'.val + t_P = j + 2^130`.
        have hj'nat : input_j'.val + tPNat = bitrange input_y.val 0 250 + 2 ^ 130 := by omega
        have hyj : input_j' = ((input_j'.val : ℕ) : Fp) :=
          (ZMod.natCast_rightInverse input_j').symm
        have hcast := congrArg (Nat.cast (R := Fp)) hj'nat
        push_cast at hcast ⊢
        rw [hyj]
        linear_combination hcast
      rw [hj, tP_eq, hj'cast]; ring
    · -- k3·k2 = 0
      rcases (show bitrange input_y.val 254 1 = 0 ∨ bitrange input_y.val 254 1 = 1 from by
        have := bitrange_lt input_y.val 254 1; omega) with h | h
      · rw [hk3, h]; simp
      · rw [hk2, (high_bit_canonical hyval h).1]; simp
    · -- k3·z13J = 0
      rcases (show bitrange input_y.val 254 1 = 0 ∨ bitrange input_y.val 254 1 = 1 from by
        have := bitrange_lt input_y.val 254 1; omega) with h | h
      · rw [hk3, h]; simp
      · rw [hz13, high_bit_z13_zero hyval h]; simp
    · -- k3·z13J' = 0
      rcases (show bitrange input_y.val 254 1 = 0 ∨ bitrange input_y.val 254 1 = 1 from by
        have := bitrange_lt input_y.val 254 1; omega) with h | h
      · rw [hk3, h]; simp
      · rw [hz13']
        have hlt : input_j'.val < 2 ^ 130 := by
          rw [hj']; exact (high_bit_canonical hyval h).2.2
        rw [Nat.div_eq_of_lt hlt]; simp

end YCanonicity.Gate

end Orchard.Action.NoteCommit
