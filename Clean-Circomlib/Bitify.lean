import Clean.Circuit
import Clean.Utils.Bits

namespace Circomlib
variable {p : ℕ} [Fact p.Prime] [Fact (p > 2)]

namespace Num2Bits
/-
template Num2Bits(n) {
    signal input in;
    signal output out[n];
    var lc1=0;

    var e2=1;
    for (var i = 0; i<n; i++) {
        out[i] <-- (in >> i) & 1;
        out[i] * (out[i] -1 ) === 0;
        lc1 += out[i] * e2;
        e2 = e2+e2;
    }

    lc1 === in;
}
-/
def main (n: ℕ) [NeZero n] (input : Expression (F p)) := do
  let bits ← Circuit.mapFinRange n fun i => do
    let bit ← witnessField fun env => ((input.eval env).val >>> i.val) &&& (1 : ℕ)
    bit * (bit - 1) === 0
    return bit

  let (lc1, _) := Fin.foldl n (fun (lc1, e2) i =>
    let lc1 := lc1 + bits[i] * e2
    let e2 := e2 + e2
    (lc1, e2)) (0, 1)

  lc1 === input
  return bits

def circuit n [NeZero n] (hn : 2^n < p) : GeneralFormalCircuit (F p) field (fields n) where
  main input := main n input
  localLength _ := n
  localLength_eq := by simp +arith only [circuit_norm, main]
  subcircuitsConsistent := by simp +arith only [circuit_norm, main]

  Assumptions input := sorry
  Spec input output := sorry

  soundness := by
    simp only [circuit_norm, main]
    sorry

  completeness := by
    simp only [circuit_norm, main]
    sorry

end Num2Bits
end Circomlib
