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

@[reducible]
instance elaborated : ElaboratedCircuit (F p) KeccakState KeccakState main where
  localLength _ := 480
  localLength_eq _ _ := by simp only [main, circuit_norm, ThetaC.circuit, ThetaC.elaborated, ThetaD.circuit, ThetaD.elaborated, ThetaXor.circuit, ThetaXor.elaborated]
  channelsLawful := by simp only [main, circuit_norm, ThetaC.circuit, ThetaC.elaborated, ThetaD.circuit, ThetaD.elaborated, ThetaXor.circuit, ThetaXor.elaborated]

def Assumptions (state : KeccakState (F p)) := state.Normalized

def Spec (state : KeccakState (F p)) (out_state : KeccakState (F p)) : Prop :=
  out_state.Normalized
  ∧ out_state.value = Specs.Keccak256.theta state.value

theorem soundness : Soundness (F p) main Assumptions Spec := by
  simp_all [circuit_norm, Spec, main, Assumptions,
    ThetaC.circuit, ThetaD.circuit, ThetaXor.circuit,
    ThetaC.Assumptions, ThetaD.Assumptions, ThetaXor.Assumptions,
    ThetaC.Spec, ThetaD.Spec, ThetaXor.Spec, Specs.Keccak256.theta]

theorem completeness : Completeness (F p) main Assumptions := by
  simp_all [circuit_norm, main, Assumptions, ThetaC.circuit, ThetaD.circuit, ThetaXor.circuit,
    ThetaC.Assumptions, ThetaD.Assumptions, ThetaXor.Assumptions, ThetaC.Spec, ThetaD.Spec,
    ThetaXor.Spec]

def circuit : FormalCircuit (F p) KeccakState KeccakState where
  main := main
  elaborated := elaborated
  Assumptions := Assumptions
  Spec := Spec
  soundness := soundness
  completeness := completeness
end Gadgets.Keccak256.Theta
