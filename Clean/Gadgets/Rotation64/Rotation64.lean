import Clean.Types.U64
import Clean.Circuit.SubCircuit
import Clean.Gadgets.Rotation64.Theorems
import Clean.Gadgets.Rotation64.Rotation64Bytes
import Clean.Gadgets.Rotation64.ByteRotationTable
import Clean.Gadgets.ByteDecomposition
import Clean.Circuit.Provable

namespace Gadgets.Rotation64
variable {p : ℕ} [Fact p.Prime]
variable [p_large_enough: Fact (p > 2^16 + 2^8)]

instance : Fact (p > 512) := by
  constructor
  linarith [p_large_enough.elim]

open Theorems (rot_right64)

/--
  Rotate the 64-bit integer by `offset` bits
-/
def rot64 (offset : Fin 64) (x : Var U64 (F p)) : Circuit (F p) (Var U64 (F p)) := do
  let byte_offset := offset / 8
  let bit_offset : ℕ := (offset % 8).val

  -- apply the byte rotation
  let out ← subcircuit (Rotation64Bytes.circuit byte_offset) x

  -- apply the bit rotation
  let ⟨x0, x1, x2, x3, x4, x5, x6, x7⟩ := out

  let ⟨x0_l, x0_h⟩ ← subcircuit (ByteDecomposition.circuit bit_offset) x0
  let ⟨x1_l, x1_h⟩ ← subcircuit (ByteDecomposition.circuit bit_offset) x1
  let ⟨x2_l, x2_h⟩ ← subcircuit (ByteDecomposition.circuit bit_offset) x2
  let ⟨x3_l, x3_h⟩ ← subcircuit (ByteDecomposition.circuit bit_offset) x3
  let ⟨x4_l, x4_h⟩ ← subcircuit (ByteDecomposition.circuit bit_offset) x4
  let ⟨x5_l, x5_h⟩ ← subcircuit (ByteDecomposition.circuit bit_offset) x5
  let ⟨x6_l, x6_h⟩ ← subcircuit (ByteDecomposition.circuit bit_offset) x6
  let ⟨x7_l, x7_h⟩ ← subcircuit (ByteDecomposition.circuit bit_offset) x7

  let ⟨y0, y1, y2, y3, y4, y5, y6, y7⟩ ← U64.witness fun _env => U64.mk 0 0 0 0 0 0 0 0

  assert_zero (x1_l * ((2 : ℕ)^(8 - bit_offset) : F p) + x0_h - y0)
  assert_zero (x2_l * ((2 : ℕ)^(8 - bit_offset) : F p) + x1_h - y1)
  assert_zero (x3_l * ((2 : ℕ)^(8 - bit_offset) : F p) + x2_h - y2)
  assert_zero (x4_l * ((2 : ℕ)^(8 - bit_offset) : F p) + x3_h - y3)
  assert_zero (x5_l * ((2 : ℕ)^(8 - bit_offset) : F p) + x4_h - y4)
  assert_zero (x6_l * ((2 : ℕ)^(8 - bit_offset) : F p) + x5_h - y5)
  assert_zero (x7_l * ((2 : ℕ)^(8 - bit_offset) : F p) + x6_h - y6)
  assert_zero (x0_l * ((2 : ℕ)^(8 - bit_offset) : F p) + x7_h - y7)
  return ⟨ y0, y1, y2, y3, y4, y5, y6, y7 ⟩

def assumptions (input : U64 (F p)) := input.is_normalized

def spec (offset : Fin 64) (x : U64 (F p)) (y: U64 (F p)) :=
  y.value = rot_right64 x.value offset.val
  ∧ y.is_normalized

def circuit (off : Fin 64) : FormalCircuit (F p) U64 U64 where
  main := rot64 off
  assumptions := assumptions
  spec := spec off
  soundness := by sorry
  completeness := by sorry
  local_length := 24
  output _inputs i0 := var_from_offset U64 (i0 + 16)

  initial_offset_eq := by
    intros
    simp only [Fin.zero_eta, Fin.isValue, Fin.val_zero, rot64, Fin.div_val, Fin.val_natCast,
      Nat.reduceMod, Fin.mod_val, Nat.cast_ofNat]; rfl
  local_length_eq := by
    intros
    simp only [rot64, Fin.isValue, Fin.div_val, Fin.mod_val, Nat.cast_ofNat, Pi.ofNat_apply]; rfl

end Gadgets.Rotation64
