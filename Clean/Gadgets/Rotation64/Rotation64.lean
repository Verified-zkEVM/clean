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

open Gadgets.Rotation64.Theorems (rot_right64)
open Gadgets.Rotation64 (byte_rotation_lookup)


/--
  Rotate the 64-bit integer by `offset` bits
-/
def rot64 (offset : Fin 64) (x : Var U64 (F p)) : Circuit (F p) (Var U64 (F p)) := do
  let byte_offset := offset / 8
  let bit_offset : ℕ := (offset % 8).val

  -- apply the byte rotation
  let out ← subcircuit (Gadgets.Rotation64Bytes.circuit byte_offset) x

  -- apply the bit rotation

  let ⟨low, high⟩ ← subcircuit (Gadgets.U64ByteDecomposition.circuit bit_offset) out
  let ⟨x0_l, x1_l, x2_l, x3_l, x4_l, x5_l, x6_l, x7_l⟩ := low
  let ⟨x0_h, x1_h, x2_h, x3_h, x4_h, x5_h, x6_h, x7_h⟩ := high

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

instance lawful (off : Fin 64) : ConstantLawfulCircuits (F := (F p)) (rot64 off) := by infer_constant_lawful_circuits

def assumptions (input : U64 (F p)) := input.is_normalized

def spec (offset : Fin 64) (x : U64 (F p)) (y: U64 (F p)) :=
  y.value = rot_right64 x.value offset.val
  ∧ y.is_normalized

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
  intro i0 env ⟨x0_var, x1_var, x2_var, x3_var, x4_var, x5_var, x6_var, x7_var ⟩ ⟨x0, x1, x2, x3, x4, x5, x6, x7⟩ h_input x_byte h_holds

  simp [elaborated, subcircuit_norm, rot64, Circuit.constraints_hold.soundness] at h_holds

  simp [subcircuit_norm, circuit_norm] at h_holds
  simp [U64.witness] at h_holds

  simp [circuit_norm, subcircuit_norm,
    Rotation64Bytes.circuit, Rotation64Bytes.elaborated,
    Rotation64Bytes.assumptions, Rotation64Bytes.spec,
    U64ByteDecomposition.circuit, U64ByteDecomposition.elaborated] at h_holds
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
