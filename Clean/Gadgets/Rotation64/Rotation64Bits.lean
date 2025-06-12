import Clean.Types.U64
import Clean.Circuit.SubCircuit
import Clean.Gadgets.Rotation64.Theorems
import Clean.Circuit.Provable

namespace Gadgets.Rotation64Bits
variable {p : ℕ} [Fact p.Prime]
variable [p_large_enough: Fact (p > 2^16 + 2^8)]

instance : Fact (p > 512) := by
  constructor
  linarith [p_large_enough.elim]

open Bitwise (rot_right64)
open Rotation64.Theorems (rotation64_bits_soundness)
open ByteDecomposition (Outputs)

def to_vars' (x : Var U64 (F p)) : Vector (Expression (F p)) (size U64) := to_vars x
def from_vars' (x : Vector (Expression (F p)) (size U64)) : Var U64 (F p) := from_vars x

/--
  Rotate the 64-bit integer by `offset` bits
-/
def rot64_bits (offset : Fin 8) (x : Var U64 (F p)) : Circuit (F p) (Var U64 (F p)) := do
  let base : F p := (2^(8 - offset.val) % 256 : ℕ)

  let parts ← Circuit.map (to_vars' x) (subcircuit (Gadgets.ByteDecomposition.circuit offset))
  let lows := parts.map Outputs.low |>.rotate 1
  let highs := parts.map Outputs.high
  let rotated := lows.zip highs |>.map fun (low, high) => low * base + high

  (from_vars' rotated : Var U64 (F p)).copy

def assumptions (input : U64 (F p)) := input.is_normalized

def spec (offset : Fin 8) (x : U64 (F p)) (y: U64 (F p)) :=
  y.value = rot_right64 x.value offset.val
  ∧ y.is_normalized

-- #eval! (rot64_bits (p:=p_babybear) 0) default |>.local_length
-- #eval! (rot64_bits (p:=p_babybear) 0) default |>.output
def elaborated (off : Fin 8) : ElaboratedCircuit (F p) U64 U64 where
  main := rot64_bits off
  local_length _ := 24
  output _inputs i0 := var_from_offset U64 (i0 + 16)
  local_length_eq _ i0 := by
    simp only [circuit_norm, rot64_bits, U64.Copy.circuit,
      ByteDecomposition.circuit, ByteDecomposition.elaborated]
  output_eq _ _ := by
    simp only [circuit_norm, rot64_bits, U64.Copy.circuit,
      ByteDecomposition.circuit, ByteDecomposition.elaborated]
  subcircuits_consistent _ _ := by
    simp +arith only [circuit_norm, rot64_bits, U64.Copy.circuit,
      ByteDecomposition.circuit, ByteDecomposition.elaborated]

lemma concat_byte (offset : Fin 8) (x y : F p) (hx : x.val < 2^offset.val) (hy : y.val < 2^(8 - offset.val)) :
    (x * (2^(8 - offset.val) % 256 : ℕ) + y).val < 2^8 := by
  let base : F p := (2^(8 - offset.val) % 256 : ℕ)
  have : 2^8 < p := by linarith [p_large_enough.elim]
  have : 2^(8 - offset.val) % 256 < 256 := Nat.mod_lt _ (by norm_num)
  have : 2^(8 - offset.val) % 256 ≤ 2^(8 - offset.val) := Nat.mod_le ..
  have h_base : base.val = 2^(8 - offset.val) % 256 := ZMod.val_cast_of_lt (by linarith [p_large_enough.elim])
  have : x.val * (2^(8 - offset.val) % 256) + 2^(8 - offset.val) ≤ 2^8 := by
    have : x.val * (2^(8 - offset.val) % 256) ≤ x.val * 2^(8 - offset.val) :=
      Nat.mul_le_mul_left _ (Nat.mod_le ..)
    suffices x.val * 2^(8 - offset.val) + 1 * 2^(8 - offset.val) ≤ 2^offset.val * 2^(8 - offset.val) by
      rw [←pow_add, add_tsub_cancel_of_le (by linarith [offset.is_lt])] at this
      linarith
    rw [←add_mul]
    exact Nat.mul_le_mul_right _ hx
  rw [ZMod.val_add_of_lt, ZMod.val_mul_of_lt, h_base]
  linarith
  rw [h_base]; linarith
  rw [ZMod.val_mul_of_lt, h_base]; linarith
  rw [h_base]; linarith

theorem soundness (offset : Fin 8) : Soundness (F p) (elaborated offset) assumptions (spec offset) := by
  intro i0 env x_var x h_input x_normalized h_holds

  dsimp only [circuit_norm, elaborated, rot64_bits, U64.copy,
    U64.Copy.circuit, ByteDecomposition.circuit, ByteDecomposition.elaborated] at h_holds
  simp only [spec, circuit_norm, elaborated, subcircuit_norm, U64.Copy.assumptions, U64.Copy.spec,
    ByteDecomposition.assumptions, ByteDecomposition.spec] at h_holds ⊢
  set y := eval env (var_from_offset U64 (i0 + 16))
  obtain ⟨ h_decomposition, h_concatenation ⟩ := h_holds

  simp only [ProvableType.ext_iff, size, from_vars', ProvableType.eval_from_vars,
    ProvableType.to_elements_from_elements] at h_concatenation
  simp only [Vector.getElem_map, Vector.getElem_zip, Vector.getElem_mapIdx, Vector.getElem_rotate] at h_concatenation
  simp only [Expression.eval] at h_concatenation

  rw [assumptions, U64.ByteVector.is_normalized_iff] at x_normalized

  have byte_decomp_assumptions (i : ℕ) (hi : i < 8) : ((to_vars x_var)[i].eval env).val < 256 := by
    rw [ProvableType.getElem_eval_to_vars, h_input]
    exact x_normalized i hi
  simp only [size] at byte_decomp_assumptions
  simp only [to_vars', byte_decomp_assumptions, true_implies] at h_decomposition

  have y_norm : y.is_normalized := by
    simp only [U64.ByteVector.is_normalized_iff]
    intro i hi
    specialize h_concatenation i hi
    simp only [size, ←h_concatenation]
    let j : Fin 8 := ⟨ (i + 1) % 8, Nat.mod_lt _ (by norm_num) ⟩
    set x := env.get (i0 + (i + 1) % 8 * 2)
    set y := env.get (i0 + i * 2 + 1)
    set base := ((2^(8 - offset.val) % 256 : ℕ) : F p)
    have hx : x.val < 2^offset.val := (h_decomposition j).right.left
    have hy : y.val < 2^(8 - offset.val) := (h_decomposition ⟨ i, hi ⟩).right.right
    exact concat_byte offset x y hx hy
  suffices y.value = _ from ⟨ this, y_norm ⟩

  stop
  simp only [circuit_norm, eval, var_from_offset, Vector.mapRange] at h_concatenation h_decomposition
  simp [circuit_norm, spec, rot_right64, eval, elaborated, var_from_offset, Vector.mapRange]

  rw [
    show Expression.eval env x0_var = x0 by injections h_input,
    show Expression.eval env x1_var = x1 by injections h_input,
    show Expression.eval env x2_var = x2 by injections h_input,
    show Expression.eval env x3_var = x3 by injections h_input,
    show Expression.eval env x4_var = x4 by injections h_input,
    show Expression.eval env x5_var = x5 by injections h_input,
    show Expression.eval env x6_var = x6 by injections h_input,
    show Expression.eval env x7_var = x7 by injections h_input,
  ] at h_holds
  obtain ⟨h_decomposition, eq0, eq1, eq2, eq3, eq4, eq5, eq6, eq7⟩ := h_holds
  specialize h_decomposition x_normalized
  obtain ⟨h_x0_l, h_x0_h, h_x1_l, h_x1_h, h_x2_l, h_x2_h, h_x3_l, h_x3_h,
    h_x4_l, h_x4_h, h_x5_l, h_x5_h, h_x6_l, h_x6_h, h_x7_l, h_x7_h⟩ := h_decomposition
  simp only [U64.value, U64.is_normalized, and_true]

  dsimp [U64.is_normalized] at x_normalized
  obtain ⟨h_x0, h_x1, h_x2, h_x3, h_x4, h_x5, h_x6, h_x7⟩ := x_normalized
  rw [rotation64_bits_soundness offset
    h_x0 h_x1 h_x2 h_x3 h_x4 h_x5 h_x6 h_x7
    h_x0_l h_x0_h h_x1_l h_x1_h h_x2_l h_x2_h h_x3_l h_x3_h
    h_x4_l h_x4_h h_x5_l h_x5_h h_x6_l h_x6_h h_x7_l h_x7_h
    eq0 eq1 eq2 eq3 eq4 eq5 eq6 eq7]
  use rfl
  sorry

theorem completeness (offset : Fin 8) : Completeness (F p) (elaborated offset) assumptions := by
  sorry

def circuit (offset : Fin 8) : FormalCircuit (F p) U64 U64 := {
  elaborated offset with
  assumptions := assumptions
  spec := spec offset
  soundness := soundness offset
  completeness := completeness offset
}

end Gadgets.Rotation64Bits
