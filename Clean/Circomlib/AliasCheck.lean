import Clean.Circuit
import Clean.Utils.Bits
import Clean.Circomlib.CompConstant

/-
Original source code:
https://github.com/iden3/circomlib/blob/35e54ea21da3e8762557234298dbb553c175ea8d/circuits/aliascheck.circom
-/

namespace Circomlib
open Utils.Bits
variable {p : ℕ} [Fact p.Prime] [Fact (p < 2^254)] [Fact (p > 2^253)]

namespace AliasCheck
/-
template AliasCheck() {

    signal input in[254];

    component  compConstant = CompConstant(-1);

    for (var i=0; i<254; i++) in[i] ==> compConstant.in[i];

    compConstant.out === 0;
}
-/
def main (input : Vector (Expression (F p)) 254) := do
  -- CompConstant(-1) means we're comparing against p-1 (since -1 ≡ p-1 mod p)
  let comp_out ← subcircuit (CompConstant.circuit (p - 1)) input
  comp_out === 0

def circuit (h135 : 2^135 < p) : FormalAssertion (F p) (fields 254) where
  main
  localLength _ := 127 + 1 + 135 + 1

  Assumptions input := ∀ i (_ : i < 254), input[i] = 0 ∨ input[i] = 1

  Spec input := sorry

  soundness := by
    simp only [circuit_norm, main]
    sorry

  completeness := by
    simp only [circuit_norm, main]
    sorry
end AliasCheck

end Circomlib
