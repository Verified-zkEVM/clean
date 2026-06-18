import Clean.Orchard.Action.NoteCommit

namespace Orchard.Action.NoteCommit

open Orchard.Specs (K bitrange bitrange_lt)
open CompElliptic.Curves.Pasta CompElliptic.CurveForms.ShortWeierstrass
open CompElliptic.Fields.Pasta (PALLAS_BASE_CARD)

set_option exponentiation.threshold 900
set_option maxRecDepth 4000

-- Shared helper: a message piece `P = lo + slice·1024` with `lo` below the shift and
-- `slice` a 50-bit value has running-sum cell `P.val / 2^10 = slice`.
theorem cell_div_pow10_eq {P lo : Fp} {slice M : ℕ}
    (hdec : P = lo + ((slice : ℕ) : Fp) * 1024)
    (hlo : lo.val < 1024) (hslice : slice < 2 ^ M) (hM : M ≤ 244) :
    P.val / 2 ^ 10 = slice := by
  have hcard : lo.val + slice * 1024 < PALLAS_BASE_CARD := by
    have hshift : slice * 1024 < 2 ^ (M + 10) := by
      calc slice * 1024 < 2 ^ M * 1024 := by gcongr
        _ = 2 ^ (M + 10) := by rw [pow_add]; norm_num
    have hle : (2 : ℕ) ^ (M + 10) ≤ 2 ^ 254 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have : (2 : ℕ) ^ 254 < PALLAS_BASE_CARD := by norm_num [PALLAS_BASE_CARD]
    omega
  have hP : P = ((lo.val + slice * 1024 : ℕ) : Fp) := by
    rw [hdec]; push_cast [ZMod.natCast_zmod_val]; ring
  rw [hP, ZMod.val_natCast_of_lt hcard]
  omega

-- low-part bounds for the d/g piece decompositions
theorem lo3_lt {a b c : Fp} (ha : a.val < 2) (hb : b.val < 2) (hc : c.val < 2 ^ 8) :
    (a + b * 2 + c * 4 : Fp).val < 1024 := by
  have hcast : (a + b * 2 + c * 4 : Fp) = ((a.val + b.val * 2 + c.val * 4 : ℕ) : Fp) := by
    push_cast [ZMod.natCast_zmod_val]; ring
  rw [hcast, ZMod.val_natCast_of_lt (by norm_num [PALLAS_BASE_CARD]; omega)]
  omega

theorem lo2_lt {a b : Fp} (ha : a.val < 2) (hb : b.val < 2 ^ 9) :
    (a + b * 2 : Fp).val < 1024 := by
  have hcast : (a + b * 2 : Fp) = ((a.val + b.val * 2 : ℕ) : Fp) := by
    push_cast [ZMod.natCast_zmod_val]; ring
  rw [hcast, ZMod.val_natCast_of_lt (by norm_num [PALLAS_BASE_CARD]; omega)]
  omega

-- Validate the d3 application using the helpers.
example (d0 d1 d2 d value : Fp)
    (hd_dec : d = d0 + d1 * 2 + d2 * 4 + ((bitrange value.val 8 50 : ℕ) : Fp) * 1024)
    (hd0 : d0.val < 2) (hd1 : d1.val < 2) (hd2 : d2.val < 2 ^ 8) :
    d.val / 2 ^ 10 = bitrange value.val 8 50 :=
  cell_div_pow10_eq hd_dec (lo3_lt hd0 hd1 hd2) (bitrange_lt _ _ _) (by norm_num)

end Orchard.Action.NoteCommit
