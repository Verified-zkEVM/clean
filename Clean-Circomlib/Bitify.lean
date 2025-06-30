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
def main (n: ℕ) (inp : Expression (F p)) := do
  let out ← witnessVector n fun env =>
    .ofFn fun i => ((inp.eval env).val >>> i.val) &&& (1 : ℕ)

  let (lc1, _) ← Circuit.foldlRange n (0, 1) fun (lc1, e2) i => do
    out[i] * (out[i] - 1) === 0
    let lc1 := lc1 + out[i] * e2
    let e2 := e2 + e2
    return (lc1, e2)

  lc1 === inp
  return out

def circuit n (hn : 2^n < p) : GeneralFormalCircuit (F p) field (fields n) where
  main := main n
  localLength _ := n
  localLength_eq := by simp +arith [circuit_norm, main]
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

namespace Bits2Num
/-
template Bits2Num(n) {
    signal input in[n];
    signal output out;
    var lc1=0;

    var e2 = 1;
    for (var i = 0; i<n; i++) {
        lc1 += in[i] * e2;
        e2 = e2 + e2;
    }

    lc1 ==> out;
}
-/
def main (n: ℕ) (input : Vector (Expression (F p)) n) := do
  let (lc1, _) := Fin.foldl n (fun (lc1, e2) i =>
    let lc1 := lc1 + input[i] * e2
    let e2 := e2 + e2
    (lc1, e2)) (0, 1)
  let out ← witnessField fun env => lc1.eval env
  out === lc1
  return out

def circuit n (hn : 2^n < p) : GeneralFormalCircuit (F p) (fields n) field where
  main := main n
  localLength _ := 1
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
end Bits2Num

end Circomlib
