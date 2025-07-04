import Clean.Types.U32
import Clean.Circuit.Subcircuit
import Clean.Utils.Rotation
import Clean.Gadgets.Rotation32.Rotation32Bytes
import Clean.Gadgets.Rotation32.Rotation32Bits
import Clean.Circuit.Provable

namespace Gadgets.Rotation32
variable {p : ℕ} [Fact p.Prime]
variable [p_large_enough: Fact (p > 2^16 + 2^8)]

instance : Fact (p > 512) := by
  constructor
  linarith [p_large_enough.elim]

open Bitwise (rotRight32)
open Utils.Rotation (rotRight32_composition)

/--
  Rotate the 32-bit integer by `offset` bits
-/
def main (offset : Fin 32) (x : Var U32 (F p)) : Circuit (F p) (Var U32 (F p)) := do
  let byte_offset : ℕ := offset.val / 8
  let bit_offset : ℕ := (offset % 8).val

  -- rotation is performed by combining a bit and a byte rotation
  let byte_rotated ← subcircuit (Rotation32Bytes.circuit byte_offset) x
  subcircuit (Rotation32Bits.circuit bit_offset) byte_rotated

def Assumptions (input : U32 (F p)) := input.Normalized

def Spec (offset : Fin 32) (x : U32 (F p)) (y: U32 (F p)) :=
  y.value = rotRight32 x.value offset.val
  ∧ y.Normalized

def output (offset : Fin 32) (i0 : Nat) : U32 (Expression (F p)) :=
  Rotation32Bits.output (offset % 8).val i0

-- #eval! (rot32 (p:=p_babybear) 0) default |>.localLength
-- #eval! (rot32 (p:=p_babybear) 0) default |>.output
def elaborated (off : Fin 32) : ElaboratedCircuit (F p) U32 U32 where
  main := main off
  localLength _ := 8
  output _inputs i0 := output off i0

theorem soundness (offset : Fin 32) : Soundness (F p) (circuit := elaborated offset) Assumptions (Spec offset) := by
  intro i0 env x_var x h_input x_normalized h_holds

  simp [circuit_norm, main, elaborated, U32.copy, subcircuit_norm,
    Rotation32Bits.circuit, Rotation32Bits.elaborated] at h_holds

  -- abstract away intermediate U32
  let byte_offset : ℕ := offset.val / 8
  let bit_offset : ℕ := (offset % 8).val
  set byte_rotated := eval env (ElaboratedCircuit.output (self:=Rotation32Bytes.elaborated byte_offset) (x_var : Var U32 _) i0)

  simp [Rotation32Bytes.circuit, Rotation32Bytes.elaborated, Rotation32Bytes.Spec, Rotation32Bytes.Assumptions,
    Rotation32Bits.circuit, Rotation32Bits.elaborated, Rotation32Bits.Spec, Rotation32Bits.Assumptions,
    Vector.finRange] at h_holds

  simp [circuit_norm, Spec, output, h_holds, elaborated]
  set y := eval env (Rotation32Bits.output (offset.val % 8 : ℕ) i0)

  simp [Assumptions] at x_normalized
  rw [←h_input] at x_normalized
  obtain ⟨h0, h1⟩ := h_holds
  specialize h0 x_normalized
  obtain ⟨hy_rot, hy_norm⟩ := h0
  specialize h1 hy_norm
  rw [hy_rot] at h1
  obtain ⟨hy, hy_norm⟩ := h1
  simp only [hy_norm, and_true]
  rw [h_input] at hy x_normalized

  -- reason about rotation
  rw [rotRight32_composition _ _ _ (U32.value_lt_of_normalized x_normalized)] at hy
  rw [hy]
  rw [show(offset.val / 8) % 4 = offset.val / 8 by
    apply Nat.mod_eq_of_lt
    apply Nat.div_lt_of_lt_mul
    exact offset.is_lt]
  rw [Nat.div_add_mod']

theorem completeness (offset : Fin 32) : Completeness (F p) (elaborated offset) Assumptions := by
  intro i0 env x_var h_env x h_eval x_normalized

  simp [circuit_norm, main, elaborated, subcircuit_norm,
    Rotation32Bits.circuit, Rotation32Bits.elaborated, Rotation32Bits.Assumptions,
    Rotation32Bytes.circuit, Rotation32Bytes.elaborated, Rotation32Bytes.Assumptions]
  simp [circuit_norm, elaborated, main, subcircuit_norm,
    Rotation32Bytes.circuit, Rotation32Bytes.Assumptions, Rotation32Bytes.Spec] at h_env

  obtain ⟨h0, _⟩ := h_env
  rw [h_eval] at h0
  specialize h0 x_normalized
  obtain ⟨h_rot, h_norm⟩ := h0

  simp only [Assumptions] at x_normalized
  rw [h_eval]
  simp only [x_normalized, true_and, h_norm]

def circuit (offset : Fin 32) : FormalCircuit (F p) U32 U32 := {
  elaborated offset with
  Assumptions
  Spec := Spec offset
  soundness := soundness offset
  completeness := completeness offset
}

end Gadgets.Rotation32
