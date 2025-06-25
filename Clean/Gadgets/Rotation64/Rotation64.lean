import Clean.Types.U64
import Clean.Circuit.Subcircuit
import Clean.Utils.Rotation
import Clean.Gadgets.Rotation64.Theorems
import Clean.Gadgets.Rotation64.Rotation64Bytes
import Clean.Gadgets.Rotation64.Rotation64Bits
import Clean.Circuit.Provable

namespace Gadgets.Rotation64
variable {p : ℕ} [Fact p.Prime]
variable [p_large_enough: Fact (p > 2^16 + 2^8)]

instance : Fact (p > 512) := by
  constructor
  linarith [p_large_enough.elim]

open Bitwise (rot_right64)
open Utils.Rotation (rot_right64_composition)

/--
  Rotate the 64-bit integer by `offset` bits
-/
def rot64 (offset : Fin 64) (x : Var U64 (F p)) : Circuit (F p) (Var U64 (F p)) := do
  let byte_offset : ℕ := offset.val / 8
  let bit_offset : ℕ := (offset % 8).val

  -- rotation is performed by combining a bit and a byte rotation
  let byte_rotated ← subcircuit (Rotation64Bytes.circuit byte_offset) x
  subcircuit (Rotation64Bits.circuit bit_offset) byte_rotated

def assumptions (input : U64 (F p)) := input.Normalized

def spec (offset : Fin 64) (x : U64 (F p)) (y: U64 (F p)) :=
  y.value = rot_right64 x.value offset.val
  ∧ y.Normalized

def output (offset : Fin 64) (i0 : Nat) : U64 (Expression (F p)) :=
  Rotation64Bits.output (offset % 8).val i0

-- #eval! (rot64 (p:=p_babybear) 0) default |>.localLength
-- #eval! (rot64 (p:=p_babybear) 0) default |>.output
def elaborated (off : Fin 64) : ElaboratedCircuit (F p) U64 U64 where
  main := rot64 off
  localLength _ := 16
  output _ i0 := output off i0

theorem soundness (offset : Fin 64) : Soundness (F p) (circuit := elaborated offset) assumptions (spec offset) := by
  intro i0 env x_var x h_input x_normalized h_holds

  simp [circuit_norm, rot64, elaborated, U64.copy, subcircuit_norm,
    Rotation64Bits.circuit, Rotation64Bits.elaborated] at h_holds

  -- abstract away intermediate U64
  let byte_offset : ℕ := offset.val / 8
  let bit_offset : ℕ := (offset % 8).val
  set byte_rotated := eval env (ElaboratedCircuit.output (self:=Rotation64Bytes.elaborated byte_offset) (x_var : Var U64 _) i0)

  simp [Rotation64Bytes.circuit, Rotation64Bytes.elaborated, Rotation64Bytes.spec, Rotation64Bytes.assumptions,
    Rotation64Bits.circuit, Rotation64Bits.elaborated, Rotation64Bits.spec, Rotation64Bits.assumptions,
    Vector.finRange] at h_holds

  simp [circuit_norm, spec, output, h_holds, elaborated]
  set y := eval env (Rotation64Bits.output (offset.val % 8 : ℕ) i0)

  simp [assumptions] at x_normalized
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
  rw [rot_right64_composition _ _ _ (U64.value_lt_of_normalized x_normalized)] at hy
  rw [hy]
  rw [show(offset.val / 8) % 8 = offset.val / 8 by
    apply Nat.mod_eq_of_lt
    apply Nat.div_lt_of_lt_mul
    exact offset.is_lt]
  rw [Nat.div_add_mod']

theorem completeness (offset : Fin 64) : Completeness (F p) (elaborated offset) assumptions := by
  intro i0 env x_var h_env x h_eval x_normalized

  simp [circuit_norm, rot64, elaborated, subcircuit_norm,
    Rotation64Bits.circuit, Rotation64Bits.elaborated, Rotation64Bits.assumptions,
    Rotation64Bytes.circuit, Rotation64Bytes.elaborated, Rotation64Bytes.assumptions]
  simp [circuit_norm, elaborated, rot64, subcircuit_norm,
    Rotation64Bytes.circuit, Rotation64Bytes.assumptions, Rotation64Bytes.spec] at h_env

  obtain ⟨h0, _⟩ := h_env
  rw [h_eval] at h0
  specialize h0 x_normalized
  obtain ⟨h_rot, h_norm⟩ := h0

  simp only [assumptions] at x_normalized
  rw [h_eval]
  simp only [x_normalized, true_and, h_norm]

def circuit (offset : Fin 64) : FormalCircuit (F p) U64 U64 := {
  elaborated offset with
  Assumptions := assumptions
  Spec := spec offset
  soundness := soundness offset
  completeness := completeness offset
}

end Gadgets.Rotation64
