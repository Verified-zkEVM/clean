import Clean.Types.U64
import Clean.Circuit.SubCircuit
import Clean.Gadgets.Rotation64.Theorems
import Clean.Gadgets.Rotation64.Rotation64Bytes
import Clean.Gadgets.Rotation64.Rotation64Bits
import Clean.Gadgets.ByteDecomposition
import Clean.Circuit.Provable

namespace Gadgets.Rotation64
variable {p : ℕ} [Fact p.Prime]
variable [p_large_enough: Fact (p > 2^16 + 2^8)]

instance : Fact (p > 512) := by
  constructor
  linarith [p_large_enough.elim]

open Gadgets.Rotation64.Theorems (rot_right64)
open Gadgets.Rotation64 (byte_rotation_lookup)


/--
  Rotate the 64-bit integer by `offset` bits
-/
def rot64 (offset : Fin 64) (x : Var U64 (F p)) : Circuit (F p) (Var U64 (F p)) := do
  let byte_offset : ℕ := offset.val / 8
  let bit_offset : ℕ := (offset % 8).val

  -- rotation is performed by combining a bit and a byte rotation
  let byte_rotated ← subcircuit (Rotation64Bytes.circuit byte_offset) x
  subcircuit (Rotation64Bits.circuit bit_offset) byte_rotated

instance lawful (off : Fin 64) : ConstantLawfulCircuits (F := (F p)) (rot64 off) := by infer_constant_lawful_circuits

def assumptions (input : U64 (F p)) := input.is_normalized

def spec (offset : Fin 64) (x : U64 (F p)) (y: U64 (F p)) :=
  y.value = rot_right64 x.value offset.val
  ∧ y.is_normalized

#eval! (rot64 (p:=p_babybear) 0) default |>.operations.local_length
#eval! (rot64 (p:=p_babybear) 0) default |>.output
def elaborated (off : Fin 64) : ElaboratedCircuit (F p) U64 (Var U64 (F p)) where
  main := rot64 off
  local_length _ := 24
  output _inputs i0 := var_from_offset U64 (i0 + 16)
  initial_offset_eq := by
    intros
    simp only [rot64]
    rfl
  local_length_eq := by
    intros
    simp only [rot64]
    rfl


theorem soundness (offset : Fin 64) : Soundness (F p) (circuit := elaborated offset) assumptions (spec offset) := by
  intro i0 env ⟨x0_var, x1_var, x2_var, x3_var, x4_var, x5_var, x6_var, x7_var ⟩ ⟨x0, x1, x2, x3, x4, x5, x6, x7⟩ h_input x_normalized h_holds

  sorry

theorem completeness (offset : Fin 64) : Completeness (F p) (circuit := elaborated offset) U64 assumptions := by
  sorry

def circuit (offset : Fin 64) : FormalCircuit (F p) U64 U64 := {
  elaborated offset with
  assumptions := assumptions
  spec := spec offset
  soundness := soundness offset
  completeness := completeness offset
}

end Gadgets.Rotation64
