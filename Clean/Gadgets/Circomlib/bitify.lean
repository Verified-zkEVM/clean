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
  let lc1 : Expression (F p) := 0
  let e2 : Expression (F p) := 1

  let (lc1, _, bits) ← Circuit.foldlRange n (lc1, e2, []) (fun (lc1, e2, bits) i => do
    let bit ← witnessField fun env => ((input.eval env).val >>> i.val) &&& (1 : ℕ)
    bit * (bit - 1) === 0
    let lc1 := lc1 + bit * e2
    let e2 := e2 + e2
    let bits := bits.concat bit
    return (lc1, e2, bits))

  lc1 === input
  -- TODO doesn't work, because we can't prove here that bits has length n
  return bits

def circuit n [NeZero n] (hn : 2^n < p) : GeneralFormalCircuit (F p) field (fields n) where
  main input := main n input

end Num2Bits
end Circomlib
