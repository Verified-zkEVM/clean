import Clean.Types.U32
import Clean.Circuit.Subcircuit
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

open Gadgets.Rotation32.Theorems
open ByteDecomposition (Outputs)
open ByteDecomposition.Theorems (byteDecomposition_lt)

/--
  Rotate the 32-bit integer by `offset` bits
-/
def main {sentences : PropertySet (F p)} (order : SentenceOrder sentences) (offset : Fin 8) (x : U32 (Expression (F p))) : Circuit sentences (Var U32 (F p)) := do
  let parts ← Circuit.map x.toLimbs (ByteDecomposition.circuit order offset)
  let lows := parts.map Outputs.low
  let highs := parts.map Outputs.high

  let rotated := highs.zip (lows.rotate 1) |>.map fun (high, low) =>
    high + low * ((2^(8-offset.val) : ℕ) : F p)

  return U32.fromLimbs rotated

def Assumptions (input : U32 (F p)) := input.Normalized

def CompletenessAssumptions {sentences : PropertySet (F p)} (_ : YieldContext sentences) (input : U32 (F p)) := Assumptions input

def Spec {sentences : PropertySet (F p)} (_checked : CheckedYields sentences) (offset : Fin 8) (x : U32 (F p)) (y : U32 (F p)) :=
  y.value = rotRight32 x.value offset.val
  ∧ y.Normalized

def output (offset : Fin 8) (i0 : ℕ) : U32 (Expression (F p)) :=
  U32.fromLimbs (.ofFn fun ⟨i,_⟩ =>
    (var ⟨i0 + i*2 + 1⟩) + var ⟨i0 + (i + 1) % 4 * 2⟩ * .const ((2^(8-offset.val) : ℕ) : F p))

-- #eval main (p:=p_babybear) 1 default |>.output
def elaborated {sentences : PropertySet (F p)} (order : SentenceOrder sentences) (off : Fin 8) : ElaboratedCircuit (F p) sentences U32 U32 where
  main := main order off
  localLength _ := 8
  output _inputs i0 := output off i0
  yields _ _ _ := ∅
  localLength_eq _ i0 := by
    simp only [circuit_norm, main, ByteDecomposition.circuit, ByteDecomposition.elaborated]
  output_eq _ _ := by
    simp only [circuit_norm, main, output, ByteDecomposition.circuit, ByteDecomposition.elaborated]
    apply congrArg U32.fromLimbs
    simp [Vector.ext_iff, Vector.getElem_rotate]
  yields_eq := by
    intros env input offset
    simp only [main, circuit_norm, ElaboratedCircuit.yields_eq]
    simp [ByteDecomposition.circuit, ByteDecomposition.elaborated]
  subcircuitsConsistent _ _ := by
    simp +arith only [circuit_norm, main,
      ByteDecomposition.circuit, ByteDecomposition.elaborated]

theorem soundness {sentences : PropertySet (F p)} (order : SentenceOrder sentences) (offset : Fin 8) : Soundness (F p) (elaborated order offset) order Assumptions (Spec (offset := offset)) := by
  intro i0 env yields checked x_var x h_input x_normalized h_holds

  -- simplify statements
  dsimp only [circuit_norm, elaborated, main,
    ByteDecomposition.circuit, ByteDecomposition.elaborated] at h_holds
  simp only [Spec, circuit_norm, elaborated,
    ByteDecomposition.Assumptions, ByteDecomposition.Spec] at h_holds ⊢

  -- targeted rewriting of the assumptions
  rw [Assumptions, U32.ByteVector.normalized_iff] at x_normalized
  simp only [U32.ByteVector.getElem_eval_toLimbs, h_input, x_normalized, true_implies,
    Fin.forall_iff] at h_holds

  set base := ((2^(8-offset.val) : ℕ) : F p)
  have neg_offset_le : 8 - offset.val ≤ 8 := by
    rw [tsub_le_iff_right, le_add_iff_nonneg_right]; apply zero_le

  -- capture the rotation relation in terms of byte vectors
  set y := eval env (output offset i0)
  set xs := x.toLimbs
  set ys := y.toLimbs
  set o := offset.val

  have h_rot_vector (i : ℕ) (hi : i < 4) :
      ys[i].val < 2^8 ∧
      ys[i].val = xs[i].val / 2^o + (xs[(i + 1) % 4].val % 2^o) * 2^(8-o) := by
    simp only [ys, y, output, U32.ByteVector.eval_fromLimbs, U32.ByteVector.toLimbs_fromLimbs,
      Vector.getElem_map, Vector.getElem_ofFn, Expression.eval]
    set high := env.get (i0 + i * 2 + 1)
    set next_low := env.get (i0 + (i + 1) % 4 * 2)
    have ⟨eq_spec, byte_spec⟩ := h_holds i hi
    have ⟨_, high_eq⟩ := eq_spec
    have ⟨_, high_lt⟩ := byte_spec
    have ⟨next_eq_spec, next_byte_spec⟩ := h_holds ((i + 1) % 4) (Nat.mod_lt _ (by norm_num))
    have ⟨next_low_eq, _⟩ := next_eq_spec
    have ⟨next_low_lt, _⟩ := next_byte_spec
    have next_low_lt' : next_low.val < 2^(8 - (8 - o)) := by rw [Nat.sub_sub_self offset.is_le']; exact next_low_lt
    have ⟨lt, eq⟩ := byteDecomposition_lt (8-o) neg_offset_le high_lt next_low_lt'
    use lt
    rw [eq, high_eq, next_low_eq]

  -- prove that the output is normalized
  have y_norm : y.Normalized := by
    rw [U32.ByteVector.normalized_iff]
    intro i hi
    exact (h_rot_vector i hi).left

  -- finish the proof using our characerization of rotation on byte vectors
  have h_rot_vector' : y.vals = rotRight32_u32 x.vals o := by
    rw [U32.ByteVector.ext_iff, ←rotRight32_bytes_u32_eq]
    intro i hi
    simp only [U32.vals, U32.ByteVector.toLimbs_map, Vector.getElem_map, rotRight32_bytes, Vector.getElem_ofFn]
    exact (h_rot_vector i hi).right

  rw [←U32.vals_valueNat, ←U32.vals_valueNat, h_rot_vector']
  exact ⟨ rotation32_bits_soundness offset.is_lt, y_norm ⟩

theorem completeness {sentences : PropertySet (F p)} (order : SentenceOrder sentences) (offset : Fin 8) : Completeness (F p) sentences (elaborated order offset) CompletenessAssumptions := by
  intro i0 env yields x_var _ x h_input x_normalized

  -- simplify goal
  simp only [main, elaborated, circuit_norm,
    ByteDecomposition.circuit, ByteDecomposition.CompletenessAssumptions, ByteDecomposition.Assumptions]

  -- we only have to prove the byte decomposition assumptions
  simp only [CompletenessAssumptions, Assumptions] at x_normalized
  rw [U32.ByteVector.normalized_iff] at x_normalized
  simp_all only [U32.ByteVector.getElem_eval_toLimbs]
  intro i
  trivial

def circuit {sentences : PropertySet (F p)} (order : SentenceOrder sentences) (offset : Fin 8) : FormalCircuit order U32 U32 := {
  elaborated := elaborated order offset
  Assumptions
  CompletenessAssumptions
  Spec := Spec (offset := offset)
  soundness := soundness order offset
  completeness := completeness order offset
  completenessAssumptions_implies_assumptions := fun _ _ h => h
}

end Gadgets.Rotation32Bits
