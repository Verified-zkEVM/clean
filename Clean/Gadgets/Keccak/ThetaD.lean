import Clean.Gadgets.Addition8.Addition8FullCarry
import Clean.Types.U64
import Clean.Gadgets.Xor.Xor64
import Clean.Gadgets.Keccak.KeccakState
import Clean.Gadgets.Rotation64.Rotation64
import Clean.Gadgets.Keccak.Keccak

namespace Gadgets.Keccak.ThetaD
variable {p : ℕ} [Fact p.Prime]
variable [p_large_enough: Fact (p > 512)]

open FieldUtils (mod_256 floordiv)
open Xor (xor_u64)
open Clean.Gadgets.Keccak256
open Gadgets.Rotation64.Theorems (rot_right64)

def theta_d (state : Var KeccakRow (F p)) : Circuit (F p) (Var KeccakRow (F p)) := do
  let c0 ← subcircuit (Gadgets.Rotation64.circuit (64 - 1)) (state.get 1)
  let c0 ← subcircuit Gadgets.Xor.circuit ⟨(state.get 4), c0⟩

  let c1 ← subcircuit (Gadgets.Rotation64.circuit (64 - 1)) (state.get 2)
  let c1 ← subcircuit Gadgets.Xor.circuit ⟨(state.get 0), c1⟩

  let c2 ← subcircuit (Gadgets.Rotation64.circuit (64 - 1)) (state.get 3)
  let c2 ← subcircuit Gadgets.Xor.circuit ⟨(state.get 1), c2⟩

  let c3 ← subcircuit (Gadgets.Rotation64.circuit (64 - 1)) (state.get 4)
  let c3 ← subcircuit Gadgets.Xor.circuit ⟨(state.get 2), c3⟩

  let c4 ← subcircuit (Gadgets.Rotation64.circuit (64 - 1)) (state.get 0)
  let c4 ← subcircuit Gadgets.Xor.circuit ⟨(state.get 3), c4⟩

  return #v[c0, c1, c2, c3, c4]

instance elaborated : ElaboratedCircuit (F p) KeccakRow (Var KeccakRow (F p)) where
  main := theta_d
  local_length _ := 160
  output _ i0 := #v[
    var_from_offset U64 (i0 + 24),
    var_from_offset U64 (i0 + 56),
    var_from_offset U64 (i0 + 88),
    var_from_offset U64 (i0 + 120),
    var_from_offset U64 (i0 + 152)
  ]

def assumptions (state : KeccakRow (F p)) := state.is_normalized

def spec (state : KeccakRow (F p)) (out: KeccakRow (F p)) : Prop :=
  out.is_normalized ∧ out.value = Clean.Gadgets.Keccak256.theta_d state.value

theorem soundness : Soundness (F p) assumptions spec := by
  intro i0 env state_var state h_input state_norm h_holds
  simp only [circuit_norm, eval_vector] at h_input
  dsimp only [assumptions] at state_norm
  dsimp only [circuit_norm, theta_d, Xor.circuit, Rotation64.circuit] at h_holds
  simp only [circuit_norm, subcircuit_norm] at h_holds
  dsimp only [Xor.assumptions, Xor.spec, Rotation64.assumptions, Rotation64.spec] at h_holds
  simp [add_assoc, and_assoc, -Fin.val_zero, -Fin.val_one', -Fin.val_one, -Fin.val_two] at h_holds

  have u64_from_offset (i : ℕ) : var_from_offset (F:=(F p)) U64 (i0 + i) = ⟨var ⟨i0 + i⟩, var ⟨i0 + i + 1⟩, var ⟨i0 + i + 2⟩, var ⟨i0 + i + 3⟩, var ⟨i0 + i + 4⟩, var ⟨i0 + i + 5⟩, var ⟨i0 + i + 6⟩, var ⟨i0 + i + 7⟩⟩ := by
    simp only [var_from_offset, from_vars, from_elements, Vector.natInit, add_zero, Vector.push_mk,
      Nat.reduceAdd, List.push_toArray, List.nil_append, List.cons_append]

  rw [←u64_from_offset 16, ←u64_from_offset 48, ←u64_from_offset 80, ←u64_from_offset 112, ←u64_from_offset 144] at h_holds
  clear u64_from_offset

  have s (i : Fin 5) : eval env (state_var[i.val]) = state[i.val] := by
    rw [←h_input, Vector.getElem_map]

  simp only [s] at h_holds
  simp [circuit_norm, spec, KeccakRow.is_normalized_iff, KeccakRow.value, KeccakState.value]

  obtain ⟨ h_rot0, h_xor0, h_rot1, h_xor1, h_rot2, h_xor2, h_rot3, h_xor3, h_rot4, h_xor4 ⟩ := h_holds

  specialize h_rot0 (state_norm 1)
  specialize h_xor0 (state_norm 4) h_rot0.right
  rw [h_rot0.left] at h_xor0

  specialize h_rot1 (state_norm 2)
  specialize h_xor1 (state_norm 0) h_rot1.right
  rw [h_rot1.left] at h_xor1

  specialize h_rot2 (state_norm 3)
  specialize h_xor2 (state_norm 1) h_rot2.right
  rw [h_rot2.left] at h_xor2

  specialize h_rot3 (state_norm 4)
  specialize h_xor3 (state_norm 2) h_rot3.right
  rw [h_rot3.left] at h_xor3

  specialize h_rot4 (state_norm 0)
  specialize h_xor4 (state_norm 3) h_rot4.right
  rw [h_rot4.left] at h_xor4

  simp [Clean.Gadgets.Keccak256.theta_d, Clean.Gadgets.Keccak256.xor_u64, h_xor0, h_xor1, h_xor2, h_xor3, h_xor4, rol_u64, eval_vector]


theorem completeness : Completeness (F p) KeccakRow assumptions := by
  intro i0 env state_var h_env state h_input h_assumptions
  simp only [circuit_norm, eval_vector] at h_input
  dsimp only [circuit_norm, theta_d, Xor.circuit, Rotation64.circuit]
  simp only [circuit_norm, subcircuit_norm]
  dsimp only [Xor.assumptions, Xor.spec]
  simp [add_assoc]
  sorry

def circuit : FormalCircuit (F p) KeccakRow KeccakRow := {
  elaborated with
  assumptions
  spec
  soundness
  completeness
}

end Gadgets.Keccak.ThetaD
