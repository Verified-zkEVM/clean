import Clean.Gadgets.Addition8.Addition8FullCarry
import Clean.Types.U64
import Clean.Gadgets.Xor.Xor64
import Clean.Gadgets.Keccak.KeccakState
import Clean.Gadgets.Rotation64.Rotation64
import Clean.Gadgets.Keccak.Keccak

namespace Gadgets.Keccak.ThetaXor

variable {p : ℕ} [Fact p.Prime]
variable [p_large_enough: Fact (p > 512)]

open FieldUtils (mod_256 floordiv)
open Xor (xor_u64)
open Clean.Gadgets.Keccak256 (KeccakState KeccakSlice)

structure Inputs (F : Type) where
  state : KeccakState F
  d : KeccakSlice F

instance : ProvableStruct Inputs where
  components := [KeccakState, KeccakSlice]
  to_components := fun { state, d } => .cons state (.cons d .nil)
  from_components := fun (.cons state (.cons d .nil)) => { state, d }

def theta_xor (inputs : Var Inputs (F p)) : Circuit (F p) (Var KeccakState (F p)) := do
  let ⟨state, d⟩ := inputs
  return #v[
    ←subcircuit Gadgets.Xor.circuit ⟨state.get 0, d.get 0⟩,
    ←subcircuit Gadgets.Xor.circuit ⟨state.get 1, d.get 0⟩,
    ←subcircuit Gadgets.Xor.circuit ⟨state.get 2, d.get 0⟩,
    ←subcircuit Gadgets.Xor.circuit ⟨state.get 3, d.get 0⟩,
    ←subcircuit Gadgets.Xor.circuit ⟨state.get 4, d.get 0⟩,
    ←subcircuit Gadgets.Xor.circuit ⟨state.get 5, d.get 1⟩,
    ←subcircuit Gadgets.Xor.circuit ⟨state.get 6, d.get 1⟩,
    ←subcircuit Gadgets.Xor.circuit ⟨state.get 7, d.get 1⟩,
    ←subcircuit Gadgets.Xor.circuit ⟨state.get 8, d.get 1⟩,
    ←subcircuit Gadgets.Xor.circuit ⟨state.get 9, d.get 1⟩,
    ←subcircuit Gadgets.Xor.circuit ⟨state.get 10, d.get 2⟩,
    ←subcircuit Gadgets.Xor.circuit ⟨state.get 11, d.get 2⟩,
    ←subcircuit Gadgets.Xor.circuit ⟨state.get 12, d.get 2⟩,
    ←subcircuit Gadgets.Xor.circuit ⟨state.get 13, d.get 2⟩,
    ←subcircuit Gadgets.Xor.circuit ⟨state.get 14, d.get 2⟩,
    ←subcircuit Gadgets.Xor.circuit ⟨state.get 15, d.get 3⟩,
    ←subcircuit Gadgets.Xor.circuit ⟨state.get 16, d.get 3⟩,
    ←subcircuit Gadgets.Xor.circuit ⟨state.get 17, d.get 3⟩,
    ←subcircuit Gadgets.Xor.circuit ⟨state.get 18, d.get 3⟩,
    ←subcircuit Gadgets.Xor.circuit ⟨state.get 19, d.get 3⟩,
    ←subcircuit Gadgets.Xor.circuit ⟨state.get 20, d.get 4⟩,
    ←subcircuit Gadgets.Xor.circuit ⟨state.get 21, d.get 4⟩,
    ←subcircuit Gadgets.Xor.circuit ⟨state.get 22, d.get 4⟩,
    ←subcircuit Gadgets.Xor.circuit ⟨state.get 23, d.get 4⟩,
    ←subcircuit Gadgets.Xor.circuit ⟨state.get 24, d.get 4⟩
  ]

instance elaborated : ElaboratedCircuit (F p) Inputs (Var KeccakState (F p)) where
  main := theta_xor
  local_length _ := 200
  output _ i0 := var_from_offset KeccakState i0
  output_eq _ i := by
    simp only [var_from_offset_vector, theta_xor, Xor.circuit]
    simp only [circuit_norm]
    rfl

def assumptions (inputs : Inputs (F p)) : Prop :=
  let ⟨state, d⟩ := inputs
  state.is_normalized ∧ d.is_normalized

def spec (inputs : Inputs (F p)) (out: KeccakState (F p)) : Prop :=
  let ⟨state, d⟩ := inputs
  out.is_normalized ∧ out.value = Clean.Gadgets.Keccak256.theta_xor state.value d.value

theorem soundness : Soundness (F p) assumptions spec := by
  intro i0 env state_var ⟨state, d⟩ h_input ⟨state_norm, d_norm⟩ h_holds
  simp only [circuit_norm, eval_vector] at h_input
  dsimp only [circuit_norm, theta_xor, Xor.circuit, Rotation64.circuit] at h_holds
  simp only [circuit_norm, subcircuit_norm] at h_holds
  dsimp only [Xor.assumptions, Xor.spec, Rotation64.assumptions, Rotation64.spec] at h_holds
  simp [add_assoc, and_assoc, -Fin.val_zero, -Fin.val_one', -Fin.val_one, -Fin.val_two] at h_holds

  simp at h_input
  obtain ⟨h_state, h_d⟩ := h_input

  have s_d (i : Fin 5) : eval env (state_var.d[i.val]) = d[i.val] := by
    rw [← h_d, Vector.getElem_map]

  have s_state (i : Fin 25) : eval env (state_var.state[i.val]) = state[i.val] := by
    rw [← h_state, Vector.getElem_map]

  simp only [s_d, s_state] at h_holds
  simp [circuit_norm, spec, Clean.Gadgets.Keccak256.theta_xor, Clean.Gadgets.Keccak256.xor_u64, Fin.forall_fin_succ,
    -Fin.val_zero, -Fin.val_one', -Fin.val_one, -Fin.val_two, var_from_offset_vector, eval_vector,
    KeccakState.is_normalized, KeccakState.value, KeccakSlice.value]

  repeat
    first
    | obtain ⟨ h, h_holds ⟩ := h_holds
    | let h := h_holds; let h_holds := True
    specialize h (state_norm _) (d_norm _)
    obtain ⟨ xor, norm ⟩ := h
    simp [xor, norm]


theorem completeness : Completeness (F p) KeccakState assumptions := by
  intro i0 env state_var h_env state h_input h_assumptions
  simp only [circuit_norm] at h_input
  dsimp only [circuit_norm, theta_xor, Xor.circuit, Rotation64.circuit]
  simp only [circuit_norm, subcircuit_norm]
  dsimp only [Xor.assumptions, Xor.spec]
  simp [add_assoc]
  sorry

def circuit : FormalCircuit (F p) Inputs KeccakState := {
  elaborated with
  assumptions
  spec
  soundness
  completeness
}

end Gadgets.Keccak.ThetaXor
