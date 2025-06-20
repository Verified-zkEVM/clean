import Clean.Types.U32
import Clean.Circuit.SubCircuit
import Clean.Gadgets.Rotation32.Theorems
import Clean.Gadgets.Rotation32.Rotation32Bytes
import Clean.Gadgets.ByteDecomposition.ByteDecomposition
import Clean.Circuit.Provable

namespace Gadgets.Rotation32Bits
variable {p : ℕ} [Fact p.Prime]
variable [p_large_enough: Fact (p > 2^16 + 2^8)]

instance : Fact (p > 512) := by
  constructor
  linarith [p_large_enough.elim]

open Bitwise (rot_right32)
open Gadgets.Rotation32.Theorems
open ByteDecomposition (Outputs)
open ByteDecomposition.Theorems (byte_decomposition_lt)

/--
  Rotate the 32-bit integer by `offset` bits
-/
def rot32_bits (offset : Fin 8) (x : U32 (Expression (F p))) : Circuit (F p) (Var U32 (F p)) := do
  let parts ← Circuit.map x.to_limbs (subcircuit (ByteDecomposition.circuit offset))
  let lows := parts.map Outputs.low
  let highs := parts.map Outputs.high

  let rotated := highs.zip (lows.rotate 1) |>.map fun (high, low) =>
    high + low * ((2^(8 - offset.val) : ℕ) : F p)

  return U32.from_limbs rotated

def assumptions (input : U32 (F p)) := input.is_normalized

def spec (offset : Fin 8) (x : U32 (F p)) (y: U32 (F p)) :=
  y.value = rot_right32 x.value offset.val
  ∧ y.is_normalized

def output (offset : Fin 8) (i0 : Nat) : U32 (Expression (F p)) :=
  U32.from_limbs (.ofFn fun ⟨i,_⟩ =>
    (var ⟨i0 + i*2 + 1⟩) + var ⟨i0 + (i + 1) % 4 * 2⟩ * .const ((2^(8 - offset.val) : ℕ) : F p))

-- #eval rot32_bits (p:=p_babybear) 1 default |>.output
def elaborated (off : Fin 8) : ElaboratedCircuit (F p) U32 U32 where
  main := rot32_bits off
  local_length _ := 8
  output _inputs i0 := output off i0
  local_length_eq _ i0 := by
    simp only [circuit_norm, rot32_bits, ByteDecomposition.circuit, ByteDecomposition.elaborated]
  output_eq _ _ := by
    simp only [circuit_norm, rot32_bits, output, ByteDecomposition.circuit, ByteDecomposition.elaborated]
    apply congrArg U32.from_limbs
    simp [Vector.ext_iff, Vector.getElem_rotate]
  subcircuits_consistent _ _ := by
    simp +arith only [circuit_norm, rot32_bits,
      ByteDecomposition.circuit, ByteDecomposition.elaborated]

theorem soundness (offset : Fin 8) : Soundness (F p) (elaborated offset) assumptions (spec offset) := by
  intro i0 env x_var x h_input x_normalized h_holds

  -- simplify statements
  dsimp only [circuit_norm, elaborated, rot32_bits,
    ByteDecomposition.circuit, ByteDecomposition.elaborated] at h_holds
  simp only [spec, circuit_norm, elaborated, subcircuit_norm,
    ByteDecomposition.assumptions, ByteDecomposition.spec] at h_holds ⊢

  -- targeted rewriting of the assumptions
  rw [assumptions, U32.ByteVector.is_normalized_iff] at x_normalized
  simp only [U32.ByteVector.getElem_eval_to_limbs, h_input, x_normalized, true_implies,
    Fin.forall_iff] at h_holds

  set base := ((2^(8 - offset.val) : ℕ) : F p)
  have neg_offset_le : 8 - offset.val ≤ 8 := by
    rw [tsub_le_iff_right, le_add_iff_nonneg_right]; apply zero_le

  -- capture the rotation relation in terms of byte vectors
  set y := eval env (output offset i0)
  set xs := x.to_limbs
  set ys := y.to_limbs
  set o := offset.val

  have h_rot_vector (i : ℕ) (hi : i < 4) :
      ys[i].val < 2^8 ∧
      ys[i].val = xs[i].val / 2^o + (xs[(i + 1) % 4].val % 2^o) * 2^(8-o) := by
    simp only [ys, y, output, U32.ByteVector.eval_from_limbs, U32.ByteVector.to_limbs_from_limbs,
      Vector.getElem_map, Vector.getElem_ofFn, Expression.eval]
    set high := env.get (i0 + i * 2 + 1)
    set next_low := env.get (i0 + (i + 1) % 4 * 2)
    have ⟨⟨_, high_eq⟩, ⟨_, high_lt⟩⟩ := h_holds i hi
    have ⟨⟨next_low_eq, _⟩, ⟨next_low_lt, _⟩⟩ := h_holds ((i + 1) % 4) (Nat.mod_lt _ (by norm_num))
    have next_low_lt' : next_low.val < 2^(8 - (8 - o)) := by rw [Nat.sub_sub_self offset.is_le']; exact next_low_lt
    have ⟨lt, eq⟩ := byte_decomposition_lt (8-o) neg_offset_le high_lt next_low_lt'
    use lt
    rw [eq, high_eq, next_low_eq]

  -- prove that the output is normalized
  have y_norm : y.is_normalized := by
    rw [U32.ByteVector.is_normalized_iff]
    intro i hi
    exact (h_rot_vector i hi).left

  -- finish the proof using our characerization of rotation on byte vectors
  have h_rot_vector' : y.vals = rot_right32_u32 x.vals o := by
    rw [U32.ByteVector.ext_iff, ←rot_right32_bytes_u32_eq]
    intro i hi
    simp only [U32.vals, U32.ByteVector.to_limbs_map, Vector.getElem_map, rot_right32_bytes, size, Vector.getElem_ofFn]
    exact (h_rot_vector i hi).right

  rw [←U32.vals_value, ←U32.vals_value, h_rot_vector']
  exact ⟨ rotation32_bits_soundness offset.is_lt, y_norm ⟩

theorem completeness (offset : Fin 8) : Completeness (F p) (elaborated offset) assumptions := by
  intro i0 env x_var _ x h_input x_normalized

  -- simplify goal
  simp only [rot32_bits, elaborated, circuit_norm, subcircuit_norm,
    ByteDecomposition.circuit, ByteDecomposition.assumptions]

  -- we only have to prove the byte decomposition assumptions
  rw [assumptions, U32.ByteVector.is_normalized_iff] at x_normalized
  simp_all only [size, U32.ByteVector.getElem_eval_to_limbs, forall_const]

def circuit (offset : Fin 8) : FormalCircuit (F p) U32 U32 := {
  elaborated offset with
  assumptions
  spec := spec offset
  soundness := soundness offset
  completeness := completeness offset
}

end Gadgets.Rotation32Bits
