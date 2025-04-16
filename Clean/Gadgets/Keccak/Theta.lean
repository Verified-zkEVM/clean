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
  output _ i0 := var_from_offset KeccakState (i0 + 320)

def assumptions (state : KeccakState (F p)) : Prop :=
  state.is_normalized

def spec (state : KeccakState (F p)) (out_state: KeccakState (F p)) : Prop :=
  out_state.is_normalized
  ∧ out_state.value = Clean.Gadgets.Keccak256.theta state.value

theorem soundness : Soundness (F p) assumptions spec := by
  intro i0 env state_var state h_input h_assumptions h_holds
  dsimp only [circuit_norm, subcircuit_norm, theta, assumptions, spec,
    ThetaC.circuit, ThetaD.circuit, ThetaXor.circuit,
    ThetaC.assumptions, ThetaD.assumptions, ThetaXor.assumptions,
    ThetaC.spec, ThetaD.spec, ThetaXor.spec,
    Clean.Gadgets.Keccak256.theta
    ] at *
  simp_all [circuit_norm]

theorem completeness : Completeness (F p) KeccakState assumptions := by
  intro i0 env state_var h_env state h_input h_assumptions
  dsimp only [circuit_norm, subcircuit_norm, theta, assumptions, spec,
    ThetaC.circuit, ThetaD.circuit, ThetaXor.circuit,
    ThetaC.assumptions, ThetaD.assumptions, ThetaXor.assumptions,
    ThetaC.spec, ThetaD.spec, ThetaXor.spec,
    Clean.Gadgets.Keccak256.theta
    ] at h_input h_assumptions ⊢
  simp [circuit_norm] at h_input h_assumptions ⊢
  simp_all [elaborated, theta]
  -- TODO: we need subcircuit abstraction of `env.uses_local_witnesses` to make this as easy as it
  -- should be!
  sorry

def circuit : FormalCircuit (F p) KeccakState KeccakState := {
  elaborated with
  assumptions
  spec
  soundness
  completeness
}

end Gadgets.Keccak.Theta
