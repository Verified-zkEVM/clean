import Clean.Types.U64
import Clean.Circuit.Subcircuit
import Clean.Gadgets.Rotation64.Theorems
import Clean.Circuit.Provable
import Clean.Gadgets.ByteDecomposition.ByteDecomposition

namespace Gadgets.Rotation64Bits
variable {p : ℕ} [Fact p.Prime]
variable [p_large_enough: Fact (p > 2^16 + 2^8)]

instance : Fact (p > 512) := by
  constructor
  linarith [p_large_enough.elim]

open Rotation64.Theorems
open ByteDecomposition (Outputs)
open ByteDecomposition.Theorems (byteDecomposition_lt)
/--
  Rotate the 64-bit integer by `offset` bits
-/
def main (offset : Fin 8) (x : Var U64 (F p)) : Circuit (F p) (Var U64 (F p)) := do
  let parts ← Circuit.map x.toLimbs (ByteDecomposition.circuit offset)
  let lows := parts.map Outputs.low
  let highs := parts.map Outputs.high

  let rotated := highs.zip (lows.rotate 1) |>.map fun (high, low) =>
    high + low * ((2^(8 - offset.val) : ℕ) : F p)

  return U64.fromLimbs rotated

def Assumptions (input : U64 (F p)) := input.Normalized

def Spec (offset : Fin 8) (x : U64 (F p)) (y: U64 (F p)) :=
  y.value = rotRight64 x.value offset.val
  ∧ y.Normalized

def output (offset : Fin 8) (i0 : Nat) : U64 (Expression (F p)) :=
  U64.fromLimbs (.ofFn fun ⟨i,_⟩ =>
    (var ⟨i0 + i*2 + 1⟩) + var ⟨i0 + (i + 1) % 8 * 2⟩ * .const ((2^(8 - offset.val) : ℕ) : F p))

def elaborated (off : Fin 8) : ElaboratedCircuit (F p) U64 U64 where
  main := main off
  localLength _ := 16
  output _ i0 := output off i0
  localLength_eq _ i0 := by
    simp only [circuit_norm, main, ByteDecomposition.circuit, ByteDecomposition.elaborated]
  output_eq _ _ := by
    simp only [circuit_norm, main, output, ByteDecomposition.circuit, ByteDecomposition.elaborated]
    apply congrArg U64.fromLimbs
    simp [Vector.ext_iff, Vector.getElem_rotate]
  subcircuitsConsistent _ _ := by
    simp +arith only [circuit_norm, main,
      ByteDecomposition.circuit, ByteDecomposition.elaborated]

theorem soundness (offset : Fin 8) : Soundness (F p) (elaborated offset) Assumptions (Spec offset) := by
  intro i0 env x_var x h_input x_normalized h_holds

  -- simplify statements
  dsimp only [circuit_norm, elaborated, main,
    ByteDecomposition.circuit, ByteDecomposition.elaborated] at h_holds
  simp only [Spec, circuit_norm, elaborated,
    ByteDecomposition.Assumptions, ByteDecomposition.Spec] at h_holds ⊢

  -- targeted rewriting of the assumptions
  rw [Assumptions, U64.ByteVector.normalized_iff] at x_normalized
  simp only [U64.ByteVector.getElem_eval_toLimbs, h_input, x_normalized, true_implies,
    Fin.forall_iff] at h_holds

  set base := ((2^(8 - offset.val) : ℕ) : F p)
  have neg_offset_le : 8 - offset.val ≤ 8 := by
    rw [tsub_le_iff_right, le_add_iff_nonneg_right]; apply zero_le

  -- capture the rotation relation in terms of byte vectors
  set y := eval env (output offset i0)
  set xs := x.toLimbs
  set ys := y.toLimbs
  set o := offset.val

  have h_rot_vector (i : ℕ) (hi : i < 8) :
      ys[i].val < 2^8 ∧
      ys[i].val = xs[i].val / 2^o + (xs[(i + 1) % 8].val % 2^o) * 2^(8-o) := by
    simp only [ys, y, output, U64.ByteVector.eval_fromLimbs, U64.ByteVector.toLimbs_fromLimbs,
      Vector.getElem_map, Vector.getElem_ofFn, Expression.eval]
    set high := env.get (i0 + i * 2 + 1)
    set next_low := env.get (i0 + (i + 1) % 8 * 2)
    have ⟨⟨_, high_eq⟩, ⟨_, high_lt⟩⟩ := h_holds i hi
    have ⟨⟨next_low_eq, _⟩, ⟨next_low_lt, _⟩⟩ := h_holds ((i + 1) % 8) (Nat.mod_lt _ (by norm_num))
    have next_low_lt' : next_low.val < 2^(8 - (8 - o)) := by rw [Nat.sub_sub_self offset.is_le']; exact next_low_lt
    have ⟨lt, eq⟩ := byteDecomposition_lt (8-o) neg_offset_le high_lt next_low_lt'
    use lt
    rw [eq, high_eq, next_low_eq]

  -- prove that the output is normalized
  have y_norm : y.Normalized := by
    rw [U64.ByteVector.normalized_iff]
    intro i hi
    exact (h_rot_vector i hi).left

  -- finish the proof using our characerization of rotation on byte vectors
  have h_rot_vector' : y.vals = rotRight64_u64 x.vals o := by
    rw [U64.ByteVector.ext_iff, ←rotRight64_bytes_u64_eq]
    intro i hi
    simp only [U64.vals, U64.ByteVector.toLimbs_map, Vector.getElem_map, rotRight64_bytes, size, Vector.getElem_ofFn]
    exact (h_rot_vector i hi).right

  rw [←U64.vals_valueNat, ←U64.vals_valueNat, h_rot_vector']
  exact ⟨ rotation64_bits_soundness offset.is_lt, y_norm ⟩

theorem completeness (offset : Fin 8) : Completeness (F p) (elaborated offset) Assumptions := by
  intro i0 env x_var _ x h_input x_normalized

  -- simplify goal
  set_option diagnostics true in
  simp only [main, circuit_norm, elaborated]

  -- we only have to prove the byte decomposition assumptions
  rw [Assumptions, U64.ByteVector.normalized_iff] at x_normalized
  simp_all only [size, U64.ByteVector.getElem_eval_toLimbs, forall_const]

@[simps! (config := {isSimp := false, attrs := [`circuit_norm]})]
def circuit (offset : Fin 8) : FormalCircuit (F p) U64 U64 := {
  elaborated offset with
  Assumptions
  Spec := Spec offset
  soundness := soundness offset
  completeness := completeness offset
}

end Gadgets.Rotation64Bits
