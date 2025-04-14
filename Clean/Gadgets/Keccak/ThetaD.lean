import Clean.Gadgets.Addition8.Addition8FullCarry
import Clean.Types.U64
import Clean.Gadgets.Xor.Xor64
import Clean.Gadgets.Keccak.KeccakState
import Clean.Gadgets.Rotation64.Rotation64

namespace Gadgets.Keccak.ThetaD
variable {p : ℕ} [Fact p.Prime]
variable [p_large_enough: Fact (p > 512)]

open FieldUtils (mod_256 floordiv)
open Xor (xor_u64)
open Clean.Gadgets.Keccak256
open Gadgets.Rotation64.Theorems (rot_right64)

@[reducible]
def Inputs := ProvableVector U64 5

@[reducible]
def Outputs := ProvableVector U64 5

def theta_d (state : Var Inputs (F p)) : Circuit (F p) (Var Outputs (F p)) := do
  let c0 ← subcircuit (Gadgets.Rotation64.circuit 1) (state.get 1)
  let c0 ← subcircuit Gadgets.Xor.circuit ⟨c0, (state.get 4)⟩

  let c1 ← subcircuit (Gadgets.Rotation64.circuit 1) (state.get 2)
  let c1 ← subcircuit Gadgets.Xor.circuit ⟨c1, (state.get 0)⟩

  let c2 ← subcircuit (Gadgets.Rotation64.circuit 1) (state.get 3)
  let c2 ← subcircuit Gadgets.Xor.circuit ⟨c2, (state.get 1)⟩

  let c3 ← subcircuit (Gadgets.Rotation64.circuit 1) (state.get 4)
  let c3 ← subcircuit Gadgets.Xor.circuit ⟨c3, (state.get 2)⟩

  let c4 ← subcircuit (Gadgets.Rotation64.circuit 1) (state.get 0)
  let c4 ← subcircuit Gadgets.Xor.circuit ⟨c4, (state.get 3)⟩

  return #v[c0, c1, c2, c3, c4]

instance elaborated : ElaboratedCircuit (F p) Inputs (Var Outputs (F p)) where
  main := theta_d
  local_length _ := 160
  output _ i0 := #v[
    var_from_offset U64 (i0 + 24),
    var_from_offset U64 (i0 + 56),
    var_from_offset U64 (i0 + 88),
    var_from_offset U64 (i0 + 120),
    var_from_offset U64 (i0 + 152)
  ]

def assumptions (state : Inputs (F p)) : Prop :=
  ∀ i : Fin 5, state[i].is_normalized

def spec (state : Inputs (F p)) (out: Outputs (F p)) : Prop :=
  let h_norm := out[0].is_normalized ∧ out[1].is_normalized ∧
            out[2].is_normalized ∧ out[3].is_normalized ∧ out[4].is_normalized

  let h0 := out[0].value = (rot_right64 (state[1].value) 1 |>.xor state[4].value)
  let h1 := out[1].value = (rot_right64 (state[2].value) 1 |>.xor state[0].value)
  let h2 := out[2].value = (rot_right64 (state[3].value) 1 |>.xor state[1].value)
  let h3 := out[3].value = (rot_right64 (state[4].value) 1 |>.xor state[2].value)
  let h4 := out[4].value = (rot_right64 (state[0].value) 1 |>.xor state[3].value)

  h_norm ∧ h0 ∧ h1 ∧ h2 ∧ h3 ∧ h4

theorem soundness : Soundness (F p) assumptions spec := by
  intro i0 env state_var state h_input state_norm h_holds
  simp only [circuit_norm] at h_input
  dsimp only [assumptions] at state_norm
  dsimp only [circuit_norm, theta_d, Xor.circuit, Rotation64.circuit] at h_holds
  simp only [circuit_norm, subcircuit_norm] at h_holds
  dsimp only [Xor.assumptions, Xor.spec, Rotation64.assumptions, Rotation64.spec] at h_holds
  simp [add_assoc, and_assoc] at h_holds

  have u64_from_offset (i : ℕ) : var_from_offset (F:=(F p)) U64 (i0 + i) = ⟨var ⟨i0 + i⟩, var ⟨i0 + i + 1⟩, var ⟨i0 + i + 2⟩, var ⟨i0 + i + 3⟩, var ⟨i0 + i + 4⟩, var ⟨i0 + i + 5⟩, var ⟨i0 + i + 6⟩, var ⟨i0 + i + 7⟩⟩ := by
    simp only [var_from_offset, from_vars, from_elements, Vector.natInit, add_zero, Vector.push_mk,
      Nat.reduceAdd, List.push_toArray, List.nil_append, List.cons_append]

  rw [←u64_from_offset 16, ←u64_from_offset 48, ←u64_from_offset 80, ←u64_from_offset 112, ←u64_from_offset 144] at h_holds
  clear u64_from_offset

  have s0 : eval env (state_var[0]) = state[0] := by rw [←h_input, Vector.getElem_map]
  have s1 : eval env (state_var[1]) = state[1] := by rw [←h_input, Vector.getElem_map]
  have s2 : eval env (state_var[2]) = state[2] := by rw [←h_input, Vector.getElem_map]
  have s3 : eval env (state_var[@Fin.val 5 3]) = state[3] := by rw [←h_input, Vector.getElem_map]; rfl
  have s4 : eval env (state_var[@Fin.val 5 4]) = state[4] := by rw [←h_input, Vector.getElem_map]; rfl

  rw [s0, s1, s2, s3, s4] at h_holds
  clear s0 s1 s2 s3 s4

  simp [circuit_norm, spec]

  -- lift everything to U64 variables
  set c0 := eval env <| var_from_offset (F:=(F p)) U64 (i0 + 16)
  set c0' := eval env <| var_from_offset (F:=(F p)) U64 (i0 + 24)
  set c1 := eval env <| var_from_offset (F:=(F p)) U64 (i0 + 48)
  set c1' := eval env <| var_from_offset (F:=(F p)) U64 (i0 + 56)
  set c2 := eval env <| var_from_offset (F:=(F p)) U64 (i0 + 80)
  set c2' := eval env <| var_from_offset (F:=(F p)) U64 (i0 + 88)
  set c3 := eval env <| var_from_offset (F:=(F p)) U64 (i0 + 112)
  set c3' := eval env <| var_from_offset (F:=(F p)) U64 (i0 + 120)
  set c4 := eval env <| var_from_offset (F:=(F p)) U64 (i0 + 144)
  set c4' := eval env <| var_from_offset (F:=(F p)) U64 (i0 + 152)

  obtain ⟨ h_rot0, h_xor0, h_rot1, h_xor1, h_rot2, h_xor2, h_rot3, h_xor3, h_rot4, h_xor4 ⟩ := h_holds

  specialize h_rot0 (state_norm 1)
  specialize h_xor0 h_rot0.right (state_norm 4)
  specialize h_rot1 (state_norm 2)
  specialize h_xor1 h_rot1.right (state_norm 0)
  specialize h_rot2 (state_norm 3)
  specialize h_xor2 h_rot2.right (state_norm 1)
  specialize h_rot3 (state_norm 4)
  specialize h_xor3 h_rot3.right (state_norm 2)
  specialize h_rot4 (state_norm 0)
  specialize h_xor4 h_rot4.right (state_norm 3)

  simp [h_xor0, h_xor1, h_xor2, h_xor3, h_xor4, h_rot0, h_rot1, h_rot2, h_rot3, h_rot4]


theorem completeness : Completeness (F p) Outputs assumptions := by
  intro i0 env state_var h_env state h_input h_assumptions
  simp only [circuit_norm] at h_input
  dsimp only [circuit_norm, theta_d, Xor.circuit, Rotation64.circuit]
  simp only [circuit_norm, subcircuit_norm]
  dsimp only [Xor.assumptions, Xor.spec]
  simp [add_assoc]
  sorry

def circuit : FormalCircuit (F p) Inputs Outputs := {
  elaborated with
  assumptions
  spec
  soundness
  completeness
}

end Gadgets.Keccak.ThetaD
