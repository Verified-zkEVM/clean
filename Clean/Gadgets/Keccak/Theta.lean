import Clean.Specs.Keccak256
import Clean.Gadgets.Keccak.ThetaC
import Clean.Gadgets.Keccak.ThetaD
import Clean.Gadgets.Keccak.ThetaXor

namespace Gadgets.Keccak256.Theta
variable {p : ℕ} [Fact p.Prime] [p_large_enough: Fact (p > 2^16 + 2^8)]

instance : Fact (p > 512) := .mk (by linarith [p_large_enough.elim])

def main (state : Var KeccakState (F p)) : Circuit (F p) (Var KeccakState (F p)) := do
  let c ← ThetaC.circuit state
  let d ← ThetaD.circuit c
  ThetaXor.circuit ⟨state, d⟩

@[reducible] instance elaborated : ElaboratedCircuit (F p) KeccakState KeccakState main := by
  elaborate_circuit

def Assumptions (state : KeccakState (F p)) := state.Normalized

def Spec (state : KeccakState (F p)) (out_state : KeccakState (F p)) : Prop :=
  out_state.Normalized
  ∧ out_state.value = Specs.Keccak256.theta state.value

theorem soundness : Soundness (F p) main Assumptions Spec := by
  circuit_proof_all [ThetaC.circuit, ThetaC.Assumptions, ThetaC.Spec,
    ThetaD.circuit, ThetaD.Assumptions, ThetaD.Spec,
    ThetaXor.circuit, ThetaXor.Assumptions, ThetaXor.Spec, Specs.Keccak256.theta]

theorem completeness : Completeness (F p) main Assumptions := by
  circuit_proof_all [ThetaC.circuit, ThetaC.Assumptions, ThetaC.Spec,
    ThetaD.circuit, ThetaD.Assumptions, ThetaD.Spec,
    ThetaXor.circuit, ThetaXor.Assumptions, ThetaXor.Spec]

def circuit : FormalCircuit (F p) KeccakState KeccakState := {
  main, Assumptions, Spec, soundness, completeness
}
end Gadgets.Keccak256.Theta
