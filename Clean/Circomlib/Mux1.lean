import Clean.Circuit
import Clean.Utils.Field

namespace Circomlib
open Circuit
variable {p : ℕ} [Fact p.Prime] [Fact (p > 2)]

/-
Original source code:
https://github.com/iden3/circomlib/blob/master/circuits/mux1.circom
-/

namespace MultiMux1
/-
template MultiMux1(n) {
    signal input c[n][2]; // Constants
    signal input s; // Selector
    signal output out[n];

    for (var i=0; i<n; i++) {
        out[i] <== (c[i][1] - c[i][0])*s + c[i][0];
    }
}
-/
def main (n: ℕ) [NeZero n] (input : Var (ProvablePair (ProvableVector (ProvablePair field field) n) field) (F p)) := do
  -- Extract vector of pairs and selector
  let c := input.1
  let s := input.2
  
  -- Create output vector where each element is witnessed and constrained
  -- Note: We assume n > 0 (enforced by NeZero instance)
  let out ← Circuit.mapFinRange n fun i => do
    let c_i := c[i]
    let c0 : Expression (F p) := c_i.1
    let c1 : Expression (F p) := c_i.2
    let out_i <== (c1 - c0) * s + c0
    return out_i
  return out

-- Note: This circuit requires n > 0. In practice, a 0-output multiplexer doesn't make sense.
def circuit (n : ℕ) [NeZero n] : FormalCircuit (F p) (ProvablePair (ProvableVector (ProvablePair field field) n) field) (fields n) where
  main := main n
  
  localLength _ := n
  localLength_eq := by sorry -- TODO: prove
  subcircuitsConsistent := by sorry -- TODO: prove
  
  Assumptions input := 
    let ⟨c, s⟩ := input
    s = 0 ∨ s = 1
  
  Spec input output :=
    let ⟨c, s⟩ := input
    (s = 0 ∨ s = 1) ∧
    ∀ i (_ : i < n), 
      output[i] = if s = 0 then (c[i]).1 else (c[i]).2
  
  soundness := by
    simp only [circuit_norm, main, MultiMux1.main]
    sorry -- TODO: prove soundness
  
  completeness := by
    simp only [circuit_norm, main, MultiMux1.main]
    sorry -- TODO: prove completeness

end MultiMux1

namespace Mux1
/-
template Mux1() {
    var i;
    signal input c[2]; // Constants
    signal input s; // Selector
    signal output out;

    component mux = MultiMux1(1);

    for (i=0; i<2; i++) {
        mux.c[0][i] <== c[i];
    }

    s ==> mux.s;

    mux.out[0] ==> out;
}
-/
def main (input : Var (ProvablePair (fields 2) field) (F p)) := do
  -- Extract inputs
  let c := input.1
  let s := input.2
  
  -- Create input for MultiMux1 by converting to vector of pairs
  let c_pairs : Var (ProvableVector (ProvablePair field field) 1) (F p) := 
    Vector.ofFn fun _ : Fin 1 => (c[0], c[1])
  
  -- Create combined input for MultiMux1
  let mux_input : Var (ProvablePair (ProvableVector (ProvablePair field field) 1) field) (F p) := 
    (c_pairs, s)
  
  -- Call MultiMux1 with n=1
  let mux_out ← MultiMux1.main 1 mux_input
  
  -- Extract single output
  return mux_out[0]

def circuit : FormalCircuit (F p) (ProvablePair (fields 2) field) field where
  main := main
  
  localLength _ := 1
  localLength_eq := by sorry -- TODO: prove  
  subcircuitsConsistent := by sorry -- TODO: prove
  
  Assumptions input := 
    let ⟨_, s⟩ := input
    s = 0 ∨ s = 1
  
  Spec input output :=
    let ⟨c, s⟩ := input
    (s = 0 ∨ s = 1) ∧
    output = if s = 0 then c[0] else c[1]
  
  soundness := by
    simp only [circuit_norm, main, MultiMux1.main]
    sorry
  
  completeness := by
    simp only [circuit_norm, main, MultiMux1.main]
    sorry

end Mux1

end Circomlib