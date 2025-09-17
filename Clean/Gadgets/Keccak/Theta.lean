import Clean.Specs.Keccak256
import Clean.Gadgets.Keccak.ThetaC
import Clean.Gadgets.Keccak.ThetaD
import Clean.Gadgets.Keccak.ThetaXor

namespace Gadgets.Keccak256.Theta
variable {p : ℕ} [Fact p.Prime] [p_large_enough: Fact (p > 2^16 + 2^8)]

instance : Fact (p > 512) := .mk (by linarith [p_large_enough.elim])

def main {sentences : PropertySet (F p)} (order : SentenceOrder sentences) (state : Var KeccakState (F p)) : Circuit sentences (Var KeccakState (F p)) := do
  let c ← ThetaC.circuit order state
  let d ← ThetaD.circuit order c
  ThetaXor.circuit order ⟨state, d⟩

def elaborated {sentences : PropertySet (F p)} (order : SentenceOrder sentences) : ElaboratedCircuit (F p) sentences KeccakState KeccakState where
  main := main order
  localLength _ := 480

def Assumptions (state : KeccakState (F p)) := state.Normalized

def CompletenessAssumptions {sentences : PropertySet (F p)} (_ : YieldContext sentences) (state : KeccakState (F p)) := Assumptions state

def Spec {sentences : PropertySet (F p)} (_checked : CheckedYields sentences) (state : KeccakState (F p)) (out_state : KeccakState (F p)) : Prop :=
  out_state.Normalized
  ∧ out_state.value = Specs.Keccak256.theta state.value

theorem soundness {sentences : PropertySet (F p)} (order : SentenceOrder sentences) : Soundness (F p) (elaborated order) order Assumptions Spec := by
  circuit_proof_start
  constructor
  · sorry
  simp_all [circuit_norm, Spec, elaborated, main, Assumptions,
    ThetaC.circuit, ThetaC.elaborated, ThetaD.circuit, ThetaD.elaborated, ThetaXor.circuit, ThetaXor.elaborated,
    ThetaC.Assumptions, ThetaD.Assumptions, ThetaXor.Assumptions,
    ThetaC.Spec, ThetaD.Spec, ThetaXor.Spec, Specs.Keccak256.theta]

theorem completeness {sentences : PropertySet (F p)} (order : SentenceOrder sentences) : Completeness (F p) sentences (elaborated order) CompletenessAssumptions := by
  simp_all [circuit_norm, elaborated, main, CompletenessAssumptions, Assumptions, Spec,
    ThetaC.circuit, ThetaC.elaborated, ThetaD.circuit, ThetaD.elaborated, ThetaXor.circuit, ThetaXor.elaborated,
    ThetaC.CompletenessAssumptions, ThetaC.Assumptions, ThetaD.CompletenessAssumptions, ThetaD.Assumptions, ThetaXor.CompletenessAssumptions, ThetaXor.Assumptions,
    ThetaC.Spec, ThetaD.Spec, ThetaXor.Spec, Specs.Keccak256.theta]

def circuit {sentences : PropertySet (F p)} (order : SentenceOrder sentences) : FormalCircuit order KeccakState KeccakState :=
 { elaborated := elaborated order
   Assumptions
   CompletenessAssumptions
   Spec
   soundness := soundness order
   completeness := completeness order
   completenessAssumptions_implies_assumptions := fun _ _ h => h }
end Gadgets.Keccak256.Theta
