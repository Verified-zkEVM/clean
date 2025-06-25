import Clean.Specs.Keccak256
import Clean.Gadgets.Keccak.ThetaC
import Clean.Gadgets.Keccak.ThetaD
import Clean.Gadgets.Keccak.ThetaXor

namespace Gadgets.Keccak256.Theta
variable {p : ℕ} [Fact p.Prime] [p_large_enough: Fact (p > 2^16 + 2^8)]

instance : Fact (p > 512) := .mk (by linarith [p_large_enough.elim])

def theta (state : Var KeccakState (F p)) : Circuit (F p) (Var KeccakState (F p)) := do
  let c ← subcircuit ThetaC.circuit state
  let d ← subcircuit ThetaD.circuit c
  subcircuit ThetaXor.circuit ⟨state, d⟩

instance elaborated : ElaboratedCircuit (F p) KeccakState KeccakState where
  main := theta
  localLength _ := 480

def assumptions (state : KeccakState (F p)) := state.Normalized

def spec (state : KeccakState (F p)) (out_state: KeccakState (F p)) : Prop :=
  out_state.Normalized
  ∧ out_state.value = Specs.Keccak256.theta state.value

theorem soundness : Soundness (F p) elaborated assumptions spec := by
  simp_all [Soundness, circuit_norm, subcircuit_norm, spec, theta, assumptions,
    ThetaC.circuit, ThetaD.circuit, ThetaXor.circuit,
    ThetaC.assumptions, ThetaD.assumptions, ThetaXor.assumptions,
    ThetaC.spec, ThetaD.spec, ThetaXor.spec, Specs.Keccak256.theta]

theorem completeness : Completeness (F p) elaborated assumptions := by
  simp_all [Completeness, circuit_norm, subcircuit_norm, theta, assumptions, spec,
    ThetaC.circuit, ThetaD.circuit, ThetaXor.circuit,
    ThetaC.assumptions, ThetaD.assumptions, ThetaXor.assumptions,
    ThetaC.spec, ThetaD.spec, ThetaXor.spec, Specs.Keccak256.theta]

def circuit : FormalCircuit (F p) KeccakState KeccakState := {
  elaborated with
    Assumptions := assumptions,
    Spec := spec,
    soundness := soundness,
    completeness := completeness
}
end Gadgets.Keccak256.Theta
