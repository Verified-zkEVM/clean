import Clean.Gadgets.Xor.Xor64
import Clean.Gadgets.Keccak.KeccakState
import Clean.Gadgets.Rotation64.Rotation64
import Clean.Specs.Keccak256

namespace Gadgets.Keccak256.ThetaD
variable {p : ℕ} [Fact p.Prime] [p_large_enough: Fact (p > 2^16 + 2^8)]

instance : Fact (p > 512) := .mk (by linarith [p_large_enough.elim])

def main (row : Var KeccakRow (F p)) : Circuit (F p) (Var KeccakRow (F p)) := do
  let c0 ← subcircuit (Rotation64.circuit (64 - 1)) row[1]
  let c0 ← subcircuit Xor64.circuit ⟨row[4], c0⟩

  let c1 ← subcircuit (Rotation64.circuit (64 - 1)) row[2]
  let c1 ← subcircuit Xor64.circuit ⟨row[0], c1⟩

  let c2 ← subcircuit (Rotation64.circuit (64 - 1)) row[3]
  let c2 ← subcircuit Xor64.circuit ⟨row[1], c2⟩

  let c3 ← subcircuit (Rotation64.circuit (64 - 1)) row[4]
  let c3 ← subcircuit Xor64.circuit ⟨row[2], c3⟩

  let c4 ← subcircuit (Rotation64.circuit (64 - 1)) row[0]
  let c4 ← subcircuit Xor64.circuit ⟨row[3], c4⟩

  return #v[c0, c1, c2, c3, c4]

instance elaborated : ElaboratedCircuit (F p) KeccakRow KeccakRow where
  main := main
  localLength _ := 120

def Assumptions (state : KeccakRow (F p)) := state.Normalized

def Spec (row : KeccakRow (F p)) (out: KeccakRow (F p)) : Prop :=
  out.Normalized
  ∧ out.value = Specs.Keccak256.thetaD row.value

theorem soundness : Soundness (F p) elaborated Assumptions Spec := by
  intro i0 env row_var row h_input row_norm h_holds
  simp only [circuit_norm, eval_vector] at h_input
  dsimp only [Assumptions] at row_norm
  dsimp only [circuit_norm, Spec, main, Xor64.circuit, Rotation64.circuit, Rotation64.elaborated] at h_holds ⊢
  simp only [circuit_norm, subcircuit_norm, Xor64.Assumptions, Xor64.Spec, Rotation64.Assumptions, Rotation64.Spec] at h_holds
  simp only [Nat.reduceMod, zero_sub, Fin.coe_neg_one, and_imp, add_assoc, Nat.reduceAdd, and_assoc] at h_holds
  simp only [circuit_norm, KeccakRow.normalized_iff, KeccakRow.value, KeccakState.value, eval_vector]

  have s (i : ℕ) (hi : i < 5) : eval env (row_var[i]) = row[i] := by
    rw [←h_input, Vector.getElem_map]

  simp only [s] at h_holds
  obtain ⟨ h_rot0, h_xor0, h_rot1, h_xor1, h_rot2, h_xor2, h_rot3, h_xor3, h_rot4, h_xor4 ⟩ := h_holds

  specialize h_rot0 (row_norm 1)
  specialize h_xor0 (row_norm 4) h_rot0.right
  rw [h_rot0.left] at h_xor0

  specialize h_rot1 (row_norm 2)
  specialize h_xor1 (row_norm 0) h_rot1.right
  rw [h_rot1.left] at h_xor1

  specialize h_rot2 (row_norm 3)
  specialize h_xor2 (row_norm 1) h_rot2.right
  rw [h_rot2.left] at h_xor2

  specialize h_rot3 (row_norm 4)
  specialize h_xor3 (row_norm 2) h_rot3.right
  rw [h_rot3.left] at h_xor3

  specialize h_rot4 (row_norm 0)
  specialize h_xor4 (row_norm 3) h_rot4.right
  rw [h_rot4.left] at h_xor4

  simp [Specs.Keccak256.thetaD, h_xor0, h_xor1, h_xor2, h_xor3, h_xor4, Bitwise.rotLeft64]

theorem completeness : Completeness (F p) elaborated Assumptions := by
  intro i0 env row_var h_env row h_input h_assumptions
  simp only [Assumptions, KeccakRow.normalized_iff] at h_assumptions
  dsimp only [circuit_norm, main, Xor64.circuit, Rotation64.circuit, Rotation64.elaborated] at h_env ⊢
  simp_all only [circuit_norm, subcircuit_norm, getElem_eval_vector, h_input,
    Xor64.Assumptions, Xor64.Spec, Rotation64.Assumptions, Rotation64.Spec,
    add_assoc, seval, h_assumptions, true_and, true_implies]

def circuit : FormalCircuit (F p) KeccakRow KeccakRow :=
  { elaborated with Assumptions, Spec, soundness, completeness }

end Gadgets.Keccak256.ThetaD
