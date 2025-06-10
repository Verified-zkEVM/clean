import Clean.Utils.Field
import Clean.Utils.Bitwise
import Clean.Types.U32

variable {p : ℕ} [Fact p.Prime]

namespace Gadgets.Rotation32.Theorems
open Bitwise (rot_right32)

def rot_right32_eq_bv_rotate (x : ℕ) (h : x < 2^32) (offset : ℕ) :
    rot_right32 x offset = (x.toUInt64.toBitVec.rotateRight offset).toNat := by
  sorry

theorem rot_right_composition (x n m : ℕ) (h : x < 2^32) :
      rot_right32 (rot_right32 x n) m = rot_right32 x (n + m) := by
  rw [rot_right32_eq_bv_rotate _ h,
    rot_right32_eq_bv_rotate _ h,
    rot_right32_eq_bv_rotate _ (by sorry)]

  sorry

end Gadgets.Rotation32.Theorems
