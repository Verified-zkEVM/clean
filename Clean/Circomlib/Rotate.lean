import Clean.Circuit
import Clean.Utils.Field

namespace Circomlib
variable {p : ℕ} [Fact p.Prime] [Fact (p > 2)]

/-
Original source code:
https://github.com/iden3/circomlib/blob/master/circuits/sha256/rotate.circom
-/

namespace RotR

/-
template RotR(n, r) {
    signal input inp[n];
    signal output out[n];

    for (var i = 0; i < n; i++) {
        out[i] <== inp[ (i+r)%n ];
    }
}
-/
def main (n r : ℕ) [NeZero n] (inp : Vector (Expression (F p)) n) := do
  let out <== Vector.mapFinRange n fun i => inp.get (i + Fin.ofNat n r)
  return out

def circuit (n r : ℕ) [NeZero n] : FormalCircuit (F p) (fields n) (fields n) where
  main := main n r
  localLength := sorry
  localLength_eq := sorry
  subcircuitsConsistent := sorry
  Spec := sorry
  soundness := sorry
  completeness := sorry

end RotR
end Circomlib
