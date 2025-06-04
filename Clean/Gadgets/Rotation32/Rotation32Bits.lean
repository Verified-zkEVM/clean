import Clean.Types.U32
import Clean.Circuit.SubCircuit
import Clean.Gadgets.Rotation32.Theorems
import Clean.Gadgets.Rotation32.Rotation32Bytes
import Clean.Gadgets.Rotation32.ByteRotationTable
import Clean.Gadgets.ByteDecomposition.ByteDecomposition
import Clean.Circuit.Provable

namespace Gadgets.Rotation32Bits
variable {p : ℕ} [Fact p.Prime]
variable [p_large_enough: Fact (p > 2^16 + 2^8)]

instance : Fact (p > 512) := by
  constructor
  linarith [p_large_enough.elim]

open Bitwise (rot_right32)

/--
  Rotate the 32-bit integer by `offset` bits
-/
def rot32_bits (offset : Fin 8) (x : Var U32 (F p)) : Circuit (F p) (Var U32 (F p)) := do

  let two_power : F p := 2^offset.val

  let ⟨low, high⟩ ← subcircuit (Gadgets.U32ByteDecomposition.circuit offset) x
  let ⟨x0_l, x1_l, x2_l, x3_l⟩ := low
  let ⟨x0_h, x1_h, x2_h, x3_h⟩ := high

  let ⟨y0, y1, y2, y3⟩ ← U32.witness fun _env => U32.mk 0 0 0 0

  assert_zero (x1_l * two_power + x0_h - y0)
  assert_zero (x2_l * two_power + x1_h - y1)
  assert_zero (x3_l * two_power + x2_h - y2)
  assert_zero (x0_l * two_power + x3_h - y3)

  return ⟨y0, y1, y2, y3⟩

instance lawful (off : Fin 8) : ConstantLawfulCircuits (F := (F p)) (rot32_bits off) := by infer_constant_lawful_circuits

def assumptions (input : U32 (F p)) := input.is_normalized

def spec (offset : Fin 8) (x : U32 (F p)) (y: U32 (F p)) :=
  y.value = rot_right32 x.value offset.val
  ∧ y.is_normalized

-- #eval! (rot32_bits (p:=p_babybear) 0) default |>.operations.local_length
-- #eval! (rot32_bits (p:=p_babybear) 0) default |>.output
def elaborated (off : Fin 8) : ElaboratedCircuit (F p) U32 U32 where
  main := rot32_bits off
  local_length _ := 16
  output _inputs i0 := var_from_offset U32 (i0 + 8)
  initial_offset_eq := by
    intros
    simp only [rot32_bits]
    rfl
  local_length_eq := by
    intros
    simp only [rot32_bits]
    rfl

theorem rotation32_bits_soundness
