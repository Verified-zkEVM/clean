import Clean.Gadgets.Addition8.Addition8FullCarry
import Clean.Types.U64
import Clean.Gadgets.Addition32.Theorems
import Clean.Gadgets.Xor.Xor64
import Clean.Gadgets.Keccak.KeccakState
import Clean.Specs.Keccak256

namespace Gadgets.Keccak256.ThetaC
variable {p : ℕ} [Fact p.Prime] [Fact (p > 512)]

open Gadgets.Keccak256 (KeccakState KeccakRow)


def theta_c (state : Var KeccakState (F p)) : Circuit (F p) (Var KeccakRow (F p)) := do
  -- TODO would be nice to have a for loop of length 5 here
  let c0 ← subcircuit Gadgets.Xor.circuit ⟨(state.get 0), (state.get 1)⟩
  let c0 ← subcircuit Gadgets.Xor.circuit ⟨c0, (state.get 2)⟩
  let c0 ← subcircuit Gadgets.Xor.circuit ⟨c0, (state.get 3)⟩
  let c0 ← subcircuit Gadgets.Xor.circuit ⟨c0, (state.get 4)⟩

  let c1 ← subcircuit Gadgets.Xor.circuit ⟨(state.get 5), (state.get 6)⟩
  let c1 ← subcircuit Gadgets.Xor.circuit ⟨c1, (state.get 7)⟩
  let c1 ← subcircuit Gadgets.Xor.circuit ⟨c1, (state.get 8)⟩
  let c1 ← subcircuit Gadgets.Xor.circuit ⟨c1, (state.get 9)⟩

  let c2 ← subcircuit Gadgets.Xor.circuit ⟨(state.get 10), (state.get 11)⟩
  let c2 ← subcircuit Gadgets.Xor.circuit ⟨c2, (state.get 12)⟩
  let c2 ← subcircuit Gadgets.Xor.circuit ⟨c2, (state.get 13)⟩
  let c2 ← subcircuit Gadgets.Xor.circuit ⟨c2, (state.get 14)⟩

  let c3 ← subcircuit Gadgets.Xor.circuit ⟨(state.get 15), (state.get 16)⟩
  let c3 ← subcircuit Gadgets.Xor.circuit ⟨c3, (state.get 17)⟩
  let c3 ← subcircuit Gadgets.Xor.circuit ⟨c3, (state.get 18)⟩
  let c3 ← subcircuit Gadgets.Xor.circuit ⟨c3, (state.get 19)⟩

  let c4 ← subcircuit Gadgets.Xor.circuit ⟨(state.get 20), (state.get 21)⟩
  let c4 ← subcircuit Gadgets.Xor.circuit ⟨c4, (state.get 22)⟩
  let c4 ← subcircuit Gadgets.Xor.circuit ⟨c4, (state.get 23)⟩
  let c4 ← subcircuit Gadgets.Xor.circuit ⟨c4, (state.get 24)⟩
  return #v[c0, c1, c2, c3, c4]

def assumptions (state : KeccakState (F p)) : Prop :=
  ∀ i : Fin 25, state[i].is_normalized

def spec (state : KeccakState (F p)) (out: KeccakRow (F p)) : Prop :=
  let h_norm := out[0].is_normalized ∧ out[1].is_normalized ∧
             out[2].is_normalized ∧ out[3].is_normalized ∧ out[4].is_normalized

  let state_u64 := state.map (fun x => x.value)
  let out_u64 := out.map (fun x => x.value)

  let state' := Specs.Keccak256.theta_c state_u64

  h_norm ∧ state' = out_u64

-- #eval! theta_c (p:=p_babybear) default |>.operations.local_length
-- #eval! theta_c (p:=p_babybear) default |>.output
instance elaborated : ElaboratedCircuit (F p) KeccakState (Var KeccakRow (F p)) where
  main := theta_c
  local_length _ := 160
  output _ i0 := #v[
    var_from_offset U64 (i0 + 24),
    var_from_offset U64 (i0 + 56),
    var_from_offset U64 (i0 + 88),
    var_from_offset U64 (i0 + 120),
    var_from_offset U64 (i0 + 152)
  ]

theorem soundness : Soundness (F p) assumptions spec := by
  intro i0 env state_var state h_input state_norm h_holds
  simp only [circuit_norm] at h_input
  dsimp only [assumptions] at state_norm
  dsimp only [circuit_norm, theta_c, Xor.circuit] at h_holds
  simp only [circuit_norm, subcircuit_norm] at h_holds
  dsimp only [Xor.assumptions, Xor.spec] at h_holds
  simp [add_assoc, and_assoc, -Fin.val_zero, -Fin.val_one', -Fin.val_one, -Fin.val_two] at h_holds

  have s (i : Fin 25) : eval env (state_var[i.val]) = state[i.val] := by
    rw [←h_input, Vector.getElem_map]

  simp only [s] at h_holds
  simp [circuit_norm, spec]

  repeat
    first
    | obtain⟨ h0, h1, h2, h3, h_holds ⟩ := h_holds
    | obtain⟨ h0, h1, h2, h3 ⟩ := h_holds
    obtain ⟨ xor0, norm0 ⟩ := h0 (state_norm _) (state_norm _)
    obtain ⟨ xor1, norm1 ⟩ := h1 norm0 (state_norm _)
    obtain ⟨ xor2, norm2 ⟩ := h2 norm1 (state_norm _)
    obtain ⟨ xor, norm ⟩ := h3 norm2 (state_norm _)
    rw [xor2, xor1, xor0] at xor
    clear h0 h1 h2 h3 xor0 xor1 xor2 norm0 norm1 norm2

  simp_all [Specs.Keccak256.theta_c, spec]
  get_elem_tactic

theorem completeness : Completeness (F p) KeccakRow assumptions := by
  intro i0 env state_var h_env state h_input h_assumptions
  simp only [circuit_norm] at h_input
  dsimp only [circuit_norm, theta_c, Xor.circuit]
  simp only [circuit_norm, subcircuit_norm]
  dsimp only [Xor.assumptions, Xor.spec]
  simp [add_assoc, -Fin.val_zero, -Fin.val_one', -Fin.val_one, -Fin.val_two]

  have s (i : Fin 25) : eval env (state_var[i.val]) = state[i.val] := by
    rw [←h_input, Vector.getElem_map]

  simp only [s]

  sorry

def circuit : FormalCircuit (F p) KeccakState KeccakRow := {
  elaborated with
  main := theta_c
  assumptions
  spec
  soundness
  completeness
}

end Gadgets.Keccak256.ThetaC
