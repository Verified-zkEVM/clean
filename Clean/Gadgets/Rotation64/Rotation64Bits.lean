import Clean.Types.U64
import Clean.Circuit.SubCircuit
import Clean.Gadgets.Rotation64.Theorems
import Clean.Circuit.Provable
import Clean.Gadgets.ByteDecomposition.ByteDecomposition

namespace Gadgets.Rotation64Bits
variable {p : ℕ} [Fact p.Prime]
variable [p_large_enough: Fact (p > 2^16 + 2^8)]

instance : Fact (p > 512) := by
  constructor
  linarith [p_large_enough.elim]

open Bitwise (rot_right64)
open Rotation64.Theorems
open ByteDecomposition (Outputs)
open ByteDecomposition.Theorems (byte_decomposition_lt)

-- definitions to prevent `to_vars`/`from_vars` from being unfolded in the proof
-- TODO get rid of these
def to_vars' (x : Var U64 (F p)) : Vector (Expression (F p)) (size U64) := to_vars x
def from_vars' (x : Vector (Expression (F p)) (size U64)) : Var U64 (F p) := from_vars x

/--
  Rotate the 64-bit integer by `offset` bits
-/
def rot64_bits (offset : Fin 8) (x : Var U64 (F p)) : Circuit (F p) (Var U64 (F p)) := do
  let base : F p := (2^(8 - offset.val) : ℕ)

  let parts ← Circuit.map (to_vars' x) (subcircuit (Gadgets.ByteDecomposition.circuit offset))
  let lows := parts.map Outputs.low |>.rotate 1
  let highs := parts.map Outputs.high
  let rotated := lows.zip highs |>.map fun (low, high) => high + low * base

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

theorem soundness (offset : Fin 8) : Soundness (F p) (elaborated offset) assumptions (spec offset) := by
  intro i0 env x_var x h_input x_normalized h_holds

  -- simplify statements
  dsimp only [circuit_norm, elaborated, rot64_bits, U64.copy,
    U64.Copy.circuit, ByteDecomposition.circuit, ByteDecomposition.elaborated] at h_holds
  simp only [spec, circuit_norm, elaborated, subcircuit_norm, U64.Copy.assumptions, U64.Copy.spec,
    ByteDecomposition.assumptions, ByteDecomposition.spec] at h_holds ⊢
  set y := eval env (var_from_offset U64 (i0 + 16))
  obtain ⟨ h_decomposition, h_concatenation ⟩ := h_holds

  -- targeted rewriting of the assumptions
  simp only [ProvableType.ext_iff, size, from_vars', to_vars', ProvableType.eval_from_vars,
    ProvableType.to_elements_from_elements, Vector.getElem_map, Vector.getElem_zip,
    Vector.getElem_mapIdx, Vector.getElem_rotate, Expression.eval] at h_concatenation

  rw [assumptions, U64.ByteVector.is_normalized_iff] at x_normalized

  have getElem_eval_to_vars (i : ℕ) (hi : i < 8) : (to_vars x_var)[i].eval env = (to_elements x)[i] := by
    rw [ProvableType.getElem_eval_to_vars, h_input]
  simp only [size] at getElem_eval_to_vars x_normalized

  simp only [to_vars', Fin.forall_iff, getElem_eval_to_vars, x_normalized, true_implies] at h_decomposition
  set base := ((2^(8 - offset.val) : ℕ) : F p)
  have neg_offset_le : 8 - offset.val ≤ 8 := by
    rw [tsub_le_iff_right, le_add_iff_nonneg_right]; apply zero_le

  -- prove that the output is normalized
  have y_norm : y.is_normalized := by
    simp only [U64.ByteVector.is_normalized_iff]
    intro i hi
    specialize h_concatenation i hi
    simp only [size, ←h_concatenation]
    set x := env.get (i0 + i * 2 + 1)
    set y := env.get (i0 + (i + 1) % 8 * 2)
    have hx : x.val < 2^(8 - offset.val) := (h_decomposition i hi).right.right
    have hy : y.val < 2^offset.val := (h_decomposition ((i + 1) % 8) (Nat.mod_lt _ (by norm_num))).right.left
    have hy' : y.val < 2^(8 - (8 - offset.val)) := by rw [Nat.sub_sub_self offset.is_le']; exact hy
    exact (byte_decomposition_lt (8-offset.val) neg_offset_le x y hx hy').left
  suffices y.value = _ from ⟨ this, y_norm ⟩

  -- capture the rotation relation in terms of byte vectors
  set xs : Vector _ 8 := to_elements x
  set ys : Vector _ 8 := to_elements y
  set o := offset.val

  have h_rot_vector (i : ℕ) (hi : i < 8) :
      ys[i].val = xs[i].val / 2^o + (xs[(i + 1) % 8].val % 2^o) * 2^(8-o) := by
    rw [←h_concatenation i hi]
    set x := env.get (i0 + i * 2 + 1)
    set y := env.get (i0 + (i + 1) % 8 * 2)
    obtain h_decomp_x := h_decomposition i hi
    obtain h_decomp_y := h_decomposition ((i + 1) % 8) (Nat.mod_lt _ (by norm_num))
    have hx : x.val < 2^(8 - o) := h_decomp_x.right.right
    have hy : y.val < 2^o := h_decomp_y.right.left
    have hy' : y.val < 2^(8 - (8 - o)) := by rw [Nat.sub_sub_self offset.is_le']; exact hy
    rw [(byte_decomposition_lt (8-o) neg_offset_le x y hx hy').right, h_decomp_x.left.right, h_decomp_y.left.left]

  -- finish the proof using our characerization of rotation on byte vectors
  have h_rot_vector' : y.vals = rot_right64_u64 x.vals o := by
    rw [ProvableType.ext_iff, ←rot_right64_bytes_u64_eq]
    simp only [U64.vals, U64.to_elements_map, Vector.getElem_map, rot_right64_bytes, size, Vector.getElem_ofFn]
    exact h_rot_vector

  rw [←U64.vals_value, ←U64.vals_value, h_rot_vector']
  exact rotation64_bits_soundness offset.is_lt

theorem completeness (offset : Fin 8) : Completeness (F p) (elaborated offset) assumptions := by
  intro i0 env x_var _ x h_input x_normalized

  -- simplify goal
  simp only [rot64_bits, elaborated, circuit_norm, subcircuit_norm,
    U64.copy, U64.Copy.circuit, U64.Copy.assumptions,
    ByteDecomposition.circuit, ByteDecomposition.assumptions]

  -- we only have to prove the byte decomposition assumptions
  rw [assumptions, U64.ByteVector.is_normalized_iff] at x_normalized

  have getElem_eval_to_vars (i : ℕ) (hi : i < 8) : (to_vars x_var)[i].eval env = (to_elements x)[i] := by
    rw [ProvableType.getElem_eval_to_vars, h_input]

  simp_all only [size, to_vars', forall_const]

def circuit (offset : Fin 8) : FormalCircuit (F p) U64 U64 := {
  elaborated offset with
  assumptions
  spec := spec offset
  soundness := soundness offset
  completeness := completeness offset
}

end Gadgets.Rotation64Bits
