import Clean.Types.U32
import Clean.Circuit.SubCircuit
import Clean.Gadgets.Rotation32.Theorems
import Clean.Gadgets.Rotation32.Rotation32Bytes
import Clean.Gadgets.Rotation32.Rotation32Bits
import Clean.Circuit.Provable

namespace Gadgets.Rotation32
variable {p : ℕ} [Fact p.Prime]
variable [p_large_enough: Fact (p > 2^16 + 2^8)]

instance : Fact (p > 512) := by
  constructor
  linarith [p_large_enough.elim]

open Bitwise (rot_right32)

/--
  Rotate the 32-bit integer by `offset` bits
-/
def rot32 (offset : Fin 32) (x : Var U32 (F p)) : Circuit (F p) (Var U32 (F p)) := do
  let byte_offset : ℕ := offset.val / 8
  let bit_offset : ℕ := (offset % 8).val

  -- rotation is performed by combining a bit and a byte rotation
  let byte_rotated ← subcircuit (Rotation32Bytes.circuit byte_offset) x
  subcircuit (Rotation32Bits.circuit bit_offset) byte_rotated

instance lawful (off : Fin 32) : ConstantLawfulCircuits (F := (F p)) (rot32 off) := by infer_constant_lawful_circuits

def assumptions (input : U32 (F p)) := input.is_normalized

def spec (offset : Fin 32) (x : U32 (F p)) (y: U32 (F p)) :=
  y.value = rot_right32 x.value offset.val
  ∧ y.is_normalized

-- #eval! (rot32 (p:=p_babybear) 0) default |>.operations.local_length
-- #eval! (rot32 (p:=p_babybear) 0) default |>.output
def elaborated (off : Fin 32) : ElaboratedCircuit (F p) U32 U32 where
  main := rot32 off
  local_length _ := 12
  output _inputs i0 := var_from_offset U32 (i0 + 8)
  initial_offset_eq := by
    intros
    simp only [rot32]
    rfl
  local_length_eq := by
    intros
    simp only [rot32]
    rfl

theorem soundness (offset : Fin 32) : Soundness (F p) (circuit := elaborated offset) assumptions (spec offset) := by
  intro i0 env x_var x h_input x_normalized h_holds

  simp [circuit_norm, rot32, elaborated, U32.copy, subcircuit_norm,
    Rotation32Bits.circuit, Rotation32Bits.elaborated] at h_holds

  -- abstract away intermediate U32
  let byte_offset : ℕ := offset.val / 8
  let bit_offset : ℕ := (offset % 8).val

end Gadgets.Rotation32
