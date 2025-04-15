import Clean.Gadgets.Addition8.Addition8FullCarry
import Clean.Types.U64
import Clean.Gadgets.Xor.Xor64
import Clean.Gadgets.Keccak.KeccakState
import Clean.Gadgets.Rotation64.Rotation64
import Clean.Gadgets.Keccak.Keccak
import Clean.Gadgets.Keccak.ThetaC
import Clean.Gadgets.Keccak.ThetaD
import Clean.Gadgets.Keccak.ThetaXor

namespace Gadgets.Keccak.Theta
variable {p : ℕ} [Fact p.Prime]
variable [p_large_enough: Fact (p > 512)]

open FieldUtils (mod_256 floordiv)
open Xor (xor_u64)
open Clean.Gadgets.Keccak256


def theta (state : Var KeccakState (F p)) : Circuit (F p) (Var KeccakState (F p)) := do
  let c ← subcircuit Gadgets.Keccak.ThetaC.circuit state
  let d ← subcircuit Gadgets.Keccak.ThetaD.circuit c
  return ←subcircuit Gadgets.Keccak.ThetaXor.circuit ⟨state, d⟩


instance elaborated : ElaboratedCircuit (F p) KeccakState (Var KeccakState (F p)) where
  main := theta
  local_length _ := 520
  output _ i0 := #v[
    var_from_offset U64 (i0 + 320),
    var_from_offset U64 (i0 + 328),
    var_from_offset U64 (i0 + 336),
    var_from_offset U64 (i0 + 344),
    var_from_offset U64 (i0 + 352),
    var_from_offset U64 (i0 + 360),
    var_from_offset U64 (i0 + 368),
    var_from_offset U64 (i0 + 376),
    var_from_offset U64 (i0 + 384),
    var_from_offset U64 (i0 + 392),
    var_from_offset U64 (i0 + 400),
    var_from_offset U64 (i0 + 408),
    var_from_offset U64 (i0 + 416),
    var_from_offset U64 (i0 + 424),
    var_from_offset U64 (i0 + 432),
    var_from_offset U64 (i0 + 440),
    var_from_offset U64 (i0 + 448),
    var_from_offset U64 (i0 + 456),
    var_from_offset U64 (i0 + 464),
    var_from_offset U64 (i0 + 472),
    var_from_offset U64 (i0 + 480),
    var_from_offset U64 (i0 + 488),
    var_from_offset U64 (i0 + 496),
    var_from_offset U64 (i0 + 504),
    var_from_offset U64 (i0 + 512)
  ]

def assumptions (state : KeccakState (F p)) : Prop :=
  ∀ i : Fin 25, state[i].is_normalized

def spec (state : KeccakState (F p)) (out_state: KeccakState (F p)) : Prop :=
  let h_norm := ∀ i : Fin 25, out_state[i].is_normalized

  let state_u64 := state.map (fun x => x.value)
  let out_u64 := out_state.map (fun x => x.value)

  let state' := Clean.Gadgets.Keccak256.theta state_u64

  h_norm ∧ state' = out_u64

theorem soundness : Soundness (F p) assumptions spec := by
  intro i0 env state_var state h_input state_norm h_holds
  simp only [circuit_norm] at h_input
  dsimp only [assumptions] at state_norm
  dsimp only [circuit_norm, theta, ThetaC.circuit, ThetaD.circuit, ThetaXor.circuit] at h_holds
  simp only [circuit_norm, subcircuit_norm] at h_holds
  sorry


theorem completeness : Completeness (F p) KeccakState assumptions := by
  intro i0 env state_var h_env state h_input h_assumptions
  simp only [circuit_norm] at h_input
  dsimp only [circuit_norm, theta]
  simp only [circuit_norm, subcircuit_norm]
  sorry

def circuit : FormalCircuit (F p) KeccakState KeccakState := {
  elaborated with
  assumptions
  spec
  soundness
  completeness
}

end Gadgets.Keccak.Theta
