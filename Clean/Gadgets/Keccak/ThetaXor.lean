import Clean.Gadgets.Addition8.Addition8FullCarry
import Clean.Types.U64
import Clean.Gadgets.Xor.Xor64
import Clean.Gadgets.Keccak.KeccakState
import Clean.Gadgets.Rotation64.Rotation64
import Clean.Specs.Keccak256

namespace Gadgets.Keccak256.ThetaXor

variable {p : ℕ} [Fact p.Prime]
variable [p_large_enough: Fact (p > 512)]

open Gadgets.Keccak256 (KeccakState KeccakRow)

structure Inputs (F : Type) where
  state : KeccakState F
  d : KeccakRow F

instance : ProvableStruct Inputs where
  components := [KeccakState, KeccakRow]
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
  output _ i0 := #v[
    var_from_offset U64 (i0),
    var_from_offset U64 (i0 + 8),
    var_from_offset U64 (i0 + 16),
    var_from_offset U64 (i0 + 24),
    var_from_offset U64 (i0 + 32),
    var_from_offset U64 (i0 + 40),
    var_from_offset U64 (i0 + 48),
    var_from_offset U64 (i0 + 56),
    var_from_offset U64 (i0 + 64),
    var_from_offset U64 (i0 + 72),
    var_from_offset U64 (i0 + 80),
    var_from_offset U64 (i0 + 88),
    var_from_offset U64 (i0 + 96),
    var_from_offset U64 (i0 + 104),
    var_from_offset U64 (i0 + 112),
    var_from_offset U64 (i0 + 120),
    var_from_offset U64 (i0 + 128),
    var_from_offset U64 (i0 + 136),
    var_from_offset U64 (i0 + 144),
    var_from_offset U64 (i0 + 152),
    var_from_offset U64 (i0 + 160),
    var_from_offset U64 (i0 + 168),
    var_from_offset U64 (i0 + 176),
    var_from_offset U64 (i0 + 184),
    var_from_offset U64 (i0 + 192)
  ]

def assumptions (inputs : Inputs (F p)) : Prop :=
  let ⟨state, d⟩ := inputs
  (∀ i : Fin 25, state[i].is_normalized) ∧ (∀ i : Fin 5, d[i].is_normalized)

def spec (inputs : Inputs (F p)) (out: KeccakState (F p)) : Prop :=
  let ⟨state, d⟩ := inputs
  let h_norm := ∀ i : Fin 25, out[i].is_normalized

  let state_u64 := state.map (fun x => x.value)
  let d_u64 := d.map (fun x => x.value)
  let out_u64 := out.map (fun x => x.value)

  let state' := Specs.Keccak256.theta_xor state_u64 d_u64

  h_norm ∧ state' = out_u64

theorem soundness : Soundness (F p) assumptions spec := by
  intro i0 env state_var ⟨state, d⟩ h_input ⟨state_norm, d_norm⟩ h_holds
  simp only [circuit_norm] at h_input
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
  simp [circuit_norm, spec, Specs.Keccak256.theta_xor, Fin.forall_fin_succ,
    -Fin.val_zero, -Fin.val_one', -Fin.val_one, -Fin.val_two]

  repeat
    first
    | obtain ⟨ h, h_holds ⟩ := h_holds
    | let h := h_holds; let h_holds := True
    specialize h (state_norm _) (d_norm _)
    obtain ⟨ xor, norm ⟩ := h
    simp [xor, norm]
  get_elem_tactic


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

end Gadgets.Keccak256.ThetaXor
