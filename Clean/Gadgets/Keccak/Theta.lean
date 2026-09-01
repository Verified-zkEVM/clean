import Clean.Specs.Keccak256
import Clean.Gadgets.Keccak.ThetaC
import Clean.Gadgets.Keccak.ThetaD
import Clean.Gadgets.Keccak.ThetaXor

namespace Gadgets.Keccak256.Theta
variable {p : ℕ} [Fact p.Prime] [p_large_enough: Fact (p > 2^16 + 2^8)]

instance : Fact (p > 512) := .mk (by linarith [p_large_enough.elim])

@[implicit_reducible]
def main (state : Var KeccakState (F p)) : Circuit (F p) (Var KeccakState (F p)) := do
  let c ← ThetaC.circuit state
  let d ← ThetaD.circuit c
  ThetaXor.circuit ⟨state, d⟩

@[reducible] instance elaborated : ElaboratedCircuit (F p) KeccakState KeccakState main where
  localLength _ := 480
  output _ i₀ := .mapFinRange 25 fun i => varFromOffset U64 (i₀ + 280 + i.val * 8)
  localLength_eq := by
    intro state i₀
    simp only [main, ThetaC.circuit, ThetaC.elaborated, ThetaD.circuit, ThetaD.elaborated,
      ThetaXor.circuit, ThetaXor.elaborated, circuit_norm]
  output_eq := by
    intro state i₀
    simp only [main, ThetaC.circuit, ThetaC.elaborated, ThetaD.circuit, ThetaD.elaborated,
      ThetaXor.circuit, ThetaXor.elaborated, circuit_norm]
  subcircuitsConsistent := by
    intro state i₀
    simp only [main, ThetaC.circuit, ThetaC.elaborated, ThetaD.circuit, ThetaD.elaborated,
      ThetaXor.circuit, ThetaXor.elaborated, circuit_norm]
    omega
  channelsLawful := by
    intro state i₀
    simp only [main, ThetaC.circuit, ThetaC.elaborated, ThetaD.circuit, ThetaD.elaborated,
      ThetaXor.circuit, ThetaXor.elaborated, circuit_norm]

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

@[implicit_reducible]
def circuit : FormalCircuit (F p) KeccakState KeccakState := {
  main, elaborated, Assumptions, Spec, soundness, completeness
}
end Gadgets.Keccak256.Theta
